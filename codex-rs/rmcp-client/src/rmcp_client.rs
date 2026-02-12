use std::collections::HashMap;
use std::ffi::OsString;
use std::io;
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::Arc;
use std::time::Duration;

use anyhow::Result;
use anyhow::anyhow;
use futures::FutureExt;
use futures::StreamExt;
use futures::future::BoxFuture;
use futures::stream::BoxStream;
use oauth2::TokenResponse;
use reqwest::header::ACCEPT;
use reqwest::header::AUTHORIZATION;
use reqwest::header::CONTENT_TYPE;
use reqwest::header::HeaderMap;
use reqwest::header::WWW_AUTHENTICATE;
use rmcp::model::CallToolRequestParams;
use rmcp::model::CallToolResult;
use rmcp::model::ClientNotification;
use rmcp::model::ClientRequest;
use rmcp::model::CreateElicitationRequestParams;
use rmcp::model::CreateElicitationResult;
use rmcp::model::CustomNotification;
use rmcp::model::CustomRequest;
use rmcp::model::Extensions;
use rmcp::model::InitializeRequestParams;
use rmcp::model::InitializeResult;
use rmcp::model::ListResourceTemplatesResult;
use rmcp::model::ListResourcesResult;
use rmcp::model::ListToolsResult;
use rmcp::model::PaginatedRequestParams;
use rmcp::model::ReadResourceRequestParams;
use rmcp::model::ReadResourceResult;
use rmcp::model::RequestId;
use rmcp::model::ServerResult;
use rmcp::model::Tool;
use rmcp::service::RoleClient;
use rmcp::service::RunningService;
use rmcp::service::{self};
use rmcp::transport::StreamableHttpClientTransport;
use rmcp::transport::auth::AuthClient;
use rmcp::transport::auth::AuthError;
use rmcp::transport::auth::OAuthState;
use rmcp::transport::child_process::TokioChildProcess;
use rmcp::transport::common::http_header::EVENT_STREAM_MIME_TYPE;
use rmcp::transport::common::http_header::HEADER_LAST_EVENT_ID;
use rmcp::transport::common::http_header::HEADER_SESSION_ID;
use rmcp::transport::common::http_header::JSON_MIME_TYPE;
use rmcp::transport::streamable_http_client::AuthRequiredError;
use rmcp::transport::streamable_http_client::StreamableHttpClient;
use rmcp::transport::streamable_http_client::StreamableHttpClientTransportConfig;
use rmcp::transport::streamable_http_client::StreamableHttpError;
use rmcp::transport::streamable_http_client::StreamableHttpPostResponse;
use serde_json::Value;
use sse_stream::Error as SseError;
use sse_stream::Sse;
use sse_stream::SseStream;
use tokio::io::AsyncBufReadExt;
use tokio::io::BufReader;
use tokio::process::Command;
use tokio::sync::Mutex;
use tokio::time;
use tracing::info;
use tracing::warn;

use crate::load_oauth_tokens;
use crate::logging_client_handler::LoggingClientHandler;
use crate::oauth::OAuthCredentialsStoreMode;
use crate::oauth::OAuthPersistor;
use crate::oauth::StoredOAuthTokens;
use crate::program_resolver;
use crate::utils::apply_default_headers;
use crate::utils::build_default_headers;
use crate::utils::create_env_for_mcp_server;
use crate::utils::run_with_timeout;

enum PendingTransport {
    ChildProcess {
        transport: TokioChildProcess,
        process_group_guard: Option<ProcessGroupGuard>,
    },
    StreamableHttp {
        transport: StreamableHttpClientTransport<StreamableHttpResponseClient>,
    },
    StreamableHttpWithOAuth {
        transport: StreamableHttpClientTransport<AuthClient<StreamableHttpResponseClient>>,
        oauth_persistor: OAuthPersistor,
    },
}

#[derive(Clone)]
struct StreamableHttpResponseClient {
    inner: reqwest::Client,
}

const NON_JSON_RESPONSE_BODY_PREVIEW_BYTES: usize = 8_192;

impl StreamableHttpResponseClient {
    fn new(inner: reqwest::Client) -> Self {
        Self { inner }
    }
}

impl StreamableHttpClient for StreamableHttpResponseClient {
    type Error = reqwest::Error;

    async fn post_message(
        &self,
        uri: std::sync::Arc<str>,
        message: rmcp::model::ClientJsonRpcMessage,
        session_id: Option<std::sync::Arc<str>>,
        auth_token: Option<String>,
    ) -> Result<StreamableHttpPostResponse, StreamableHttpError<Self::Error>> {
        let mut request = self
            .inner
            .post(uri.as_ref())
            .header(ACCEPT, [EVENT_STREAM_MIME_TYPE, JSON_MIME_TYPE].join(", "));
        if let Some(auth_header) = auth_token {
            request = request.bearer_auth(auth_header);
        }
        if let Some(session_id) = session_id {
            request = request.header(HEADER_SESSION_ID, session_id.as_ref());
        }

        let response = request.json(&message).send().await?;
        if response.status() == reqwest::StatusCode::UNAUTHORIZED {
            if let Some(header) = response.headers().get(WWW_AUTHENTICATE) {
                let header = header
                    .to_str()
                    .map_err(|_| {
                        StreamableHttpError::UnexpectedServerResponse(
                            "invalid www-authenticate header value".into(),
                        )
                    })?
                    .to_string();
                return Err(StreamableHttpError::AuthRequired(AuthRequiredError {
                    www_authenticate_header: header,
                }));
            }
        }

        let status = response.status();
        if matches!(
            status,
            reqwest::StatusCode::ACCEPTED | reqwest::StatusCode::NO_CONTENT
        ) {
            return Ok(StreamableHttpPostResponse::Accepted);
        }

        let content_type = response
            .headers()
            .get(CONTENT_TYPE)
            .and_then(|value| value.to_str().ok())
            .map(str::to_string);
        let session_id = response
            .headers()
            .get(HEADER_SESSION_ID)
            .and_then(|v| v.to_str().ok())
            .map(|s| s.to_string());

        match content_type.as_ref() {
            Some(ct) if ct.as_bytes().starts_with(EVENT_STREAM_MIME_TYPE.as_bytes()) => {
                let event_stream = SseStream::from_byte_stream(response.bytes_stream()).boxed();
                Ok(StreamableHttpPostResponse::Sse(event_stream, session_id))
            }
            Some(ct) if ct.as_bytes().starts_with(JSON_MIME_TYPE.as_bytes()) => {
                let message: rmcp::model::ServerJsonRpcMessage = response.json().await?;
                Ok(StreamableHttpPostResponse::Json(message, session_id))
            }
            None | Some(_) => {
                let body = response.text().await?;
                let mut body_preview = body;
                let body_len = body_preview.len();
                if body_len > NON_JSON_RESPONSE_BODY_PREVIEW_BYTES {
                    let mut boundary = NON_JSON_RESPONSE_BODY_PREVIEW_BYTES;
                    while !body_preview.is_char_boundary(boundary) {
                        boundary = boundary.saturating_sub(1);
                    }
                    body_preview.truncate(boundary);
                    body_preview.push_str(&format!(
                        "... (truncated {} bytes)",
                        body_len.saturating_sub(boundary)
                    ));
                }

                let content_type = content_type.as_deref().unwrap_or("missing-content-type");
                let content_type = format!("{content_type}; body: {body_preview}");
                Err(StreamableHttpError::UnexpectedContentType(Some(
                    content_type,
                )))
            }
        }
    }

    async fn delete_session(
        &self,
        uri: std::sync::Arc<str>,
        session: std::sync::Arc<str>,
        auth_token: Option<String>,
    ) -> Result<(), StreamableHttpError<Self::Error>> {
        <reqwest::Client as StreamableHttpClient>::delete_session(
            &self.inner,
            uri,
            session,
            auth_token,
        )
        .await
    }

    async fn get_stream(
        &self,
        uri: std::sync::Arc<str>,
        _session_id: std::sync::Arc<str>,
        last_event_id: Option<String>,
        auth_token: Option<String>,
    ) -> Result<BoxStream<'static, Result<Sse, SseError>>, StreamableHttpError<Self::Error>> {
        let mut request_builder = self
            .inner
            .get(uri.as_ref())
            .header(ACCEPT, [EVENT_STREAM_MIME_TYPE, JSON_MIME_TYPE].join(", "));
        if let Some(last_event_id) = last_event_id {
            request_builder = request_builder.header(HEADER_LAST_EVENT_ID, last_event_id);
        }
        if let Some(auth_header) = auth_token {
            request_builder = request_builder.bearer_auth(auth_header);
        }
        let response = request_builder.send().await?;
        if response.status() == reqwest::StatusCode::METHOD_NOT_ALLOWED {
            return Err(StreamableHttpError::ServerDoesNotSupportSse);
        }
        let response = response.error_for_status()?;
        match response.headers().get(reqwest::header::CONTENT_TYPE) {
            Some(ct) => {
                if !ct.as_bytes().starts_with(EVENT_STREAM_MIME_TYPE.as_bytes())
                    && !ct.as_bytes().starts_with(JSON_MIME_TYPE.as_bytes())
                {
                    return Err(StreamableHttpError::UnexpectedContentType(Some(
                        String::from_utf8_lossy(ct.as_bytes()).to_string(),
                    )));
                }
            }
            None => {
                return Err(StreamableHttpError::UnexpectedContentType(None));
            }
        }
        let event_stream = SseStream::from_byte_stream(response.bytes_stream()).boxed();
        Ok(event_stream)
    }
}

enum ClientState {
    Connecting {
        transport: Option<PendingTransport>,
    },
    Ready {
        _process_group_guard: Option<ProcessGroupGuard>,
        service: Arc<RunningService<RoleClient, LoggingClientHandler>>,
        oauth: Option<OAuthPersistor>,
    },
}

#[cfg(unix)]
const PROCESS_GROUP_TERM_GRACE_PERIOD: Duration = Duration::from_secs(2);

#[cfg(unix)]
struct ProcessGroupGuard {
    process_group_id: u32,
}

#[cfg(not(unix))]
struct ProcessGroupGuard;

impl ProcessGroupGuard {
    fn new(process_group_id: u32) -> Self {
        #[cfg(unix)]
        {
            Self { process_group_id }
        }
        #[cfg(not(unix))]
        {
            let _ = process_group_id;
            Self
        }
    }

    #[cfg(unix)]
    fn maybe_terminate_process_group(&self) {
        let process_group_id = self.process_group_id;
        let should_escalate =
            match codex_utils_pty::process_group::terminate_process_group(process_group_id) {
                Ok(exists) => exists,
                Err(error) => {
                    warn!("Failed to terminate MCP process group {process_group_id}: {error}");
                    false
                }
            };
        if should_escalate {
            std::thread::spawn(move || {
                std::thread::sleep(PROCESS_GROUP_TERM_GRACE_PERIOD);
                if let Err(error) =
                    codex_utils_pty::process_group::kill_process_group(process_group_id)
                {
                    warn!("Failed to kill MCP process group {process_group_id}: {error}");
                }
            });
        }
    }

    #[cfg(not(unix))]
    fn maybe_terminate_process_group(&self) {}
}

impl Drop for ProcessGroupGuard {
    fn drop(&mut self) {
        if cfg!(unix) {
            self.maybe_terminate_process_group();
        }
    }
}

pub type Elicitation = CreateElicitationRequestParams;
pub type ElicitationResponse = CreateElicitationResult;

/// Interface for sending elicitation requests to the UI and awaiting a response.
pub type SendElicitation = Box<
    dyn Fn(RequestId, Elicitation) -> BoxFuture<'static, Result<ElicitationResponse>> + Send + Sync,
>;

pub struct ToolWithConnectorId {
    pub tool: Tool,
    pub connector_id: Option<String>,
    pub connector_name: Option<String>,
}

pub struct ListToolsWithConnectorIdResult {
    pub next_cursor: Option<String>,
    pub tools: Vec<ToolWithConnectorId>,
}

/// MCP client implemented on top of the official `rmcp` SDK.
/// https://github.com/modelcontextprotocol/rust-sdk
pub struct RmcpClient {
    state: Mutex<ClientState>,
}

impl RmcpClient {
    pub async fn new_stdio_client(
        program: OsString,
        args: Vec<OsString>,
        env: Option<HashMap<String, String>>,
        env_vars: &[String],
        cwd: Option<PathBuf>,
    ) -> io::Result<Self> {
        let program_name = program.to_string_lossy().into_owned();

        // Build environment for program resolution and subprocess
        let envs = create_env_for_mcp_server(env, env_vars);

        // Resolve program to executable path (platform-specific)
        let resolved_program = program_resolver::resolve(program, &envs)?;

        let mut command = Command::new(resolved_program);
        command
            .kill_on_drop(true)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .env_clear()
            .envs(envs)
            .args(&args);
        #[cfg(unix)]
        command.process_group(0);
        if let Some(cwd) = cwd {
            command.current_dir(cwd);
        }

        let (transport, stderr) = TokioChildProcess::builder(command)
            .stderr(Stdio::piped())
            .spawn()?;
        let process_group_guard = transport.id().map(ProcessGroupGuard::new);

        if let Some(stderr) = stderr {
            tokio::spawn(async move {
                let mut reader = BufReader::new(stderr).lines();
                loop {
                    match reader.next_line().await {
                        Ok(Some(line)) => {
                            info!("MCP server stderr ({program_name}): {line}");
                        }
                        Ok(None) => break,
                        Err(error) => {
                            warn!("Failed to read MCP server stderr ({program_name}): {error}");
                            break;
                        }
                    }
                }
            });
        }

        Ok(Self {
            state: Mutex::new(ClientState::Connecting {
                transport: Some(PendingTransport::ChildProcess {
                    transport,
                    process_group_guard,
                }),
            }),
        })
    }

    #[allow(clippy::too_many_arguments)]
    pub async fn new_streamable_http_client(
        server_name: &str,
        url: &str,
        bearer_token: Option<String>,
        http_headers: Option<HashMap<String, String>>,
        env_http_headers: Option<HashMap<String, String>>,
        store_mode: OAuthCredentialsStoreMode,
    ) -> Result<Self> {
        let default_headers = build_default_headers(http_headers, env_http_headers)?;

        let initial_oauth_tokens =
            if bearer_token.is_none() && !default_headers.contains_key(AUTHORIZATION) {
                match load_oauth_tokens(server_name, url, store_mode) {
                    Ok(tokens) => tokens,
                    Err(err) => {
                        warn!("failed to read tokens for server `{server_name}`: {err}");
                        None
                    }
                }
            } else {
                None
            };

        let transport = if let Some(initial_tokens) = initial_oauth_tokens.clone() {
            match create_oauth_transport_and_runtime(
                server_name,
                url,
                initial_tokens.clone(),
                store_mode,
                default_headers.clone(),
            )
            .await
            {
                Ok((transport, oauth_persistor)) => PendingTransport::StreamableHttpWithOAuth {
                    transport,
                    oauth_persistor,
                },
                Err(err)
                    if err.downcast_ref::<AuthError>().is_some_and(|auth_err| {
                        matches!(auth_err, AuthError::NoAuthorizationSupport)
                    }) =>
                {
                    let access_token = initial_tokens
                        .token_response
                        .0
                        .access_token()
                        .secret()
                        .to_string();
                    warn!(
                        "OAuth metadata discovery is unavailable for MCP server `{server_name}`; falling back to stored bearer token authentication"
                    );
                    let http_config =
                        StreamableHttpClientTransportConfig::with_uri(url.to_string())
                            .auth_header(access_token);
                    let http_client =
                        apply_default_headers(reqwest::Client::builder(), &default_headers)
                            .build()?;
                    let http_client = StreamableHttpResponseClient::new(http_client);
                    let transport =
                        StreamableHttpClientTransport::with_client(http_client, http_config);
                    PendingTransport::StreamableHttp { transport }
                }
                Err(err) => return Err(err),
            }
        } else {
            let mut http_config = StreamableHttpClientTransportConfig::with_uri(url.to_string());
            if let Some(bearer_token) = bearer_token.clone() {
                http_config = http_config.auth_header(bearer_token);
            }

            let http_client =
                apply_default_headers(reqwest::Client::builder(), &default_headers).build()?;
            let http_client = StreamableHttpResponseClient::new(http_client);

            let transport = StreamableHttpClientTransport::with_client(http_client, http_config);
            PendingTransport::StreamableHttp { transport }
        };
        Ok(Self {
            state: Mutex::new(ClientState::Connecting {
                transport: Some(transport),
            }),
        })
    }

    /// Perform the initialization handshake with the MCP server.
    /// https://modelcontextprotocol.io/specification/2025-06-18/basic/lifecycle#initialization
    pub async fn initialize(
        &self,
        params: InitializeRequestParams,
        timeout: Option<Duration>,
        send_elicitation: SendElicitation,
    ) -> Result<InitializeResult> {
        let client_handler = LoggingClientHandler::new(params.clone(), send_elicitation);

        let (transport, oauth_persistor, process_group_guard) = {
            let mut guard = self.state.lock().await;
            match &mut *guard {
                ClientState::Connecting { transport } => match transport.take() {
                    Some(PendingTransport::ChildProcess {
                        transport,
                        process_group_guard,
                    }) => (
                        service::serve_client(client_handler.clone(), transport).boxed(),
                        None,
                        process_group_guard,
                    ),
                    Some(PendingTransport::StreamableHttp { transport }) => (
                        service::serve_client(client_handler.clone(), transport).boxed(),
                        None,
                        None,
                    ),
                    Some(PendingTransport::StreamableHttpWithOAuth {
                        transport,
                        oauth_persistor,
                    }) => (
                        service::serve_client(client_handler.clone(), transport).boxed(),
                        Some(oauth_persistor),
                        None,
                    ),
                    None => return Err(anyhow!("client already initializing")),
                },
                ClientState::Ready { .. } => return Err(anyhow!("client already initialized")),
            }
        };

        let service = match timeout {
            Some(duration) => time::timeout(duration, transport)
                .await
                .map_err(|_| anyhow!("timed out handshaking with MCP server after {duration:?}"))?
                .map_err(|err| anyhow!("handshaking with MCP server failed: {err}"))?,
            None => transport
                .await
                .map_err(|err| anyhow!("handshaking with MCP server failed: {err}"))?,
        };

        let initialize_result_rmcp = service
            .peer()
            .peer_info()
            .ok_or_else(|| anyhow!("handshake succeeded but server info was missing"))?;
        let initialize_result = initialize_result_rmcp.clone();

        {
            let mut guard = self.state.lock().await;
            *guard = ClientState::Ready {
                _process_group_guard: process_group_guard,
                service: Arc::new(service),
                oauth: oauth_persistor.clone(),
            };
        }

        if let Some(runtime) = oauth_persistor
            && let Err(error) = runtime.persist_if_needed().await
        {
            warn!("failed to persist OAuth tokens after initialize: {error}");
        }

        Ok(initialize_result)
    }

    pub async fn list_tools(
        &self,
        params: Option<PaginatedRequestParams>,
        timeout: Option<Duration>,
    ) -> Result<ListToolsResult> {
        self.refresh_oauth_if_needed().await;
        let service = self.service().await?;
        let fut = service.list_tools(params);
        let result = run_with_timeout(fut, timeout, "tools/list").await?;
        self.persist_oauth_tokens().await;
        Ok(result)
    }

    pub async fn list_tools_with_connector_ids(
        &self,
        params: Option<PaginatedRequestParams>,
        timeout: Option<Duration>,
    ) -> Result<ListToolsWithConnectorIdResult> {
        self.refresh_oauth_if_needed().await;
        let service = self.service().await?;

        let fut = service.list_tools(params);
        let result = run_with_timeout(fut, timeout, "tools/list").await?;
        let tools = result
            .tools
            .into_iter()
            .map(|tool| {
                let meta = tool.meta.as_ref();
                let connector_id = Self::meta_string(meta, "connector_id");
                let connector_name = Self::meta_string(meta, "connector_name")
                    .or_else(|| Self::meta_string(meta, "connector_display_name"));
                Ok(ToolWithConnectorId {
                    tool,
                    connector_id,
                    connector_name,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        self.persist_oauth_tokens().await;
        Ok(ListToolsWithConnectorIdResult {
            next_cursor: result.next_cursor,
            tools,
        })
    }

    fn meta_string(meta: Option<&rmcp::model::Meta>, key: &str) -> Option<String> {
        meta.and_then(|meta| meta.get(key))
            .and_then(Value::as_str)
            .map(str::trim)
            .filter(|value| !value.is_empty())
            .map(str::to_string)
    }

    pub async fn list_resources(
        &self,
        params: Option<PaginatedRequestParams>,
        timeout: Option<Duration>,
    ) -> Result<ListResourcesResult> {
        self.refresh_oauth_if_needed().await;
        let service = self.service().await?;

        let fut = service.list_resources(params);
        let result = run_with_timeout(fut, timeout, "resources/list").await?;
        self.persist_oauth_tokens().await;
        Ok(result)
    }

    pub async fn list_resource_templates(
        &self,
        params: Option<PaginatedRequestParams>,
        timeout: Option<Duration>,
    ) -> Result<ListResourceTemplatesResult> {
        self.refresh_oauth_if_needed().await;
        let service = self.service().await?;

        let fut = service.list_resource_templates(params);
        let result = run_with_timeout(fut, timeout, "resources/templates/list").await?;
        self.persist_oauth_tokens().await;
        Ok(result)
    }

    pub async fn read_resource(
        &self,
        params: ReadResourceRequestParams,
        timeout: Option<Duration>,
    ) -> Result<ReadResourceResult> {
        self.refresh_oauth_if_needed().await;
        let service = self.service().await?;
        let fut = service.read_resource(params);
        let result = run_with_timeout(fut, timeout, "resources/read").await?;
        self.persist_oauth_tokens().await;
        Ok(result)
    }

    pub async fn call_tool(
        &self,
        name: String,
        arguments: Option<serde_json::Value>,
        timeout: Option<Duration>,
    ) -> Result<CallToolResult> {
        self.refresh_oauth_if_needed().await;
        let service = self.service().await?;
        let arguments = match arguments {
            Some(Value::Object(map)) => Some(map),
            Some(other) => {
                return Err(anyhow!(
                    "MCP tool arguments must be a JSON object, got {other}"
                ));
            }
            None => None,
        };
        let rmcp_params = CallToolRequestParams {
            meta: None,
            name: name.into(),
            arguments,
            task: None,
        };
        let fut = service.call_tool(rmcp_params);
        let result = run_with_timeout(fut, timeout, "tools/call").await?;
        self.persist_oauth_tokens().await;
        Ok(result)
    }

    pub async fn send_custom_notification(
        &self,
        method: &str,
        params: Option<serde_json::Value>,
    ) -> Result<()> {
        let service: Arc<RunningService<RoleClient, LoggingClientHandler>> = self.service().await?;
        service
            .send_notification(ClientNotification::CustomNotification(CustomNotification {
                method: method.to_string(),
                params,
                extensions: Extensions::new(),
            }))
            .await?;
        Ok(())
    }

    pub async fn send_custom_request(
        &self,
        method: &str,
        params: Option<serde_json::Value>,
    ) -> Result<ServerResult> {
        let service: Arc<RunningService<RoleClient, LoggingClientHandler>> = self.service().await?;
        let response = service
            .send_request(ClientRequest::CustomRequest(CustomRequest::new(
                method, params,
            )))
            .await?;
        Ok(response)
    }

    async fn service(&self) -> Result<Arc<RunningService<RoleClient, LoggingClientHandler>>> {
        let guard = self.state.lock().await;
        match &*guard {
            ClientState::Ready { service, .. } => Ok(Arc::clone(service)),
            ClientState::Connecting { .. } => Err(anyhow!("MCP client not initialized")),
        }
    }

    async fn oauth_persistor(&self) -> Option<OAuthPersistor> {
        let guard = self.state.lock().await;
        match &*guard {
            ClientState::Ready {
                oauth: Some(runtime),
                ..
            } => Some(runtime.clone()),
            _ => None,
        }
    }

    /// This should be called after every tool call so that if a given tool call triggered
    /// a refresh of the OAuth tokens, they are persisted.
    async fn persist_oauth_tokens(&self) {
        if let Some(runtime) = self.oauth_persistor().await
            && let Err(error) = runtime.persist_if_needed().await
        {
            warn!("failed to persist OAuth tokens: {error}");
        }
    }

    async fn refresh_oauth_if_needed(&self) {
        if let Some(runtime) = self.oauth_persistor().await
            && let Err(error) = runtime.refresh_if_needed().await
        {
            warn!("failed to refresh OAuth tokens: {error}");
        }
    }
}

async fn create_oauth_transport_and_runtime(
    server_name: &str,
    url: &str,
    initial_tokens: StoredOAuthTokens,
    credentials_store: OAuthCredentialsStoreMode,
    default_headers: HeaderMap,
) -> Result<(
    StreamableHttpClientTransport<AuthClient<StreamableHttpResponseClient>>,
    OAuthPersistor,
)> {
    let http_client =
        apply_default_headers(reqwest::Client::builder(), &default_headers).build()?;
    let mut oauth_state = OAuthState::new(url.to_string(), Some(http_client.clone())).await?;

    oauth_state
        .set_credentials(
            &initial_tokens.client_id,
            initial_tokens.token_response.0.clone(),
        )
        .await?;

    let manager = match oauth_state {
        OAuthState::Authorized(manager) => manager,
        OAuthState::Unauthorized(manager) => manager,
        OAuthState::Session(_) | OAuthState::AuthorizedHttpClient(_) => {
            return Err(anyhow!("unexpected OAuth state during client setup"));
        }
    };

    let auth_client = AuthClient::new(StreamableHttpResponseClient::new(http_client), manager);
    let auth_manager = auth_client.auth_manager.clone();

    let transport = StreamableHttpClientTransport::with_client(
        auth_client,
        StreamableHttpClientTransportConfig::with_uri(url.to_string()),
    );

    let runtime = OAuthPersistor::new(
        server_name.to_string(),
        url.to_string(),
        auth_manager,
        credentials_store,
        Some(initial_tokens),
    );

    Ok((transport, runtime))
}
