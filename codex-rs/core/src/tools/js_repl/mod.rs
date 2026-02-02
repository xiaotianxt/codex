use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::fmt;
#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;

use codex_protocol::ThreadId;
use serde::Deserialize;
use serde::Serialize;
use serde_json::Value as JsonValue;
use tokio::io::AsyncBufReadExt;
use tokio::io::AsyncWriteExt;
use tokio::io::BufReader;
use tokio::process::Child;
use tokio::process::ChildStdin;
use tokio::sync::Mutex;
use tokio::sync::Notify;
use tokio::sync::OnceCell;
use tokio::sync::RwLock;
use tokio::sync::Semaphore;
use tokio_util::sync::CancellationToken;
use tracing::warn;
use uuid::Uuid;

use crate::client_common::tools::ToolSpec;
use crate::codex::Session;
use crate::codex::TurnContext;
use crate::exec::ExecExpiration;
use crate::exec::ExecToolCallOutput;
use crate::exec::MAX_EXEC_OUTPUT_DELTAS_PER_CALL;
use crate::exec::StreamOutput;
use crate::exec_env::create_env;
use crate::function_tool::FunctionCallError;
use crate::protocol::EventMsg;
use crate::protocol::ExecCommandOutputDeltaEvent;
use crate::protocol::ExecCommandSource;
use crate::protocol::ExecOutputStream;
use crate::sandboxing::CommandSpec;
use crate::sandboxing::SandboxManager;
use crate::sandboxing::SandboxPermissions;
use crate::tools::ToolRouter;
use crate::tools::context::SharedTurnDiffTracker;
use crate::tools::events::ToolEmitter;
use crate::tools::events::ToolEventCtx;
use crate::tools::events::ToolEventFailure;
use crate::tools::events::ToolEventStage;
use crate::tools::sandboxing::SandboxablePreference;

pub(crate) const JS_REPL_PRAGMA_PREFIX: &str = "// codex-js-repl:";
const KERNEL_SOURCE: &str = include_str!("kernel.js");
const MERIYAH_UMD: &str = include_str!("meriyah.umd.min.js");
const JS_REPL_MIN_NODE_VERSION: &str = include_str!("../../../../node-version.txt");
const JS_REPL_STDERR_TAIL_LINE_LIMIT: usize = 20;
const JS_REPL_STDERR_TAIL_LINE_MAX_BYTES: usize = 512;
const JS_REPL_STDERR_TAIL_MAX_BYTES: usize = 4_096;
const JS_REPL_STDERR_TAIL_SEPARATOR: &str = " | ";
const JS_REPL_EXEC_ID_LOG_LIMIT: usize = 8;
const JS_REPL_MODEL_DIAG_STDERR_MAX_BYTES: usize = 1_024;
const JS_REPL_MODEL_DIAG_ERROR_MAX_BYTES: usize = 256;
const JS_REPL_POLL_MIN_MS: u64 = 50;
const JS_REPL_POLL_MAX_MS: u64 = 5_000;
const JS_REPL_POLL_DEFAULT_MS: u64 = 1_000;
const JS_REPL_POLL_MAX_SESSIONS: usize = 16;
const JS_REPL_POLL_ALL_LOGS_MAX_BYTES: usize = crate::unified_exec::UNIFIED_EXEC_OUTPUT_MAX_BYTES;
const JS_REPL_POLL_LOG_QUEUE_MAX_BYTES: usize = 64 * 1024;
const JS_REPL_OUTPUT_DELTA_MAX_BYTES: usize = 8192;
const JS_REPL_POLL_COMPLETED_EXEC_RETENTION: Duration = Duration::from_secs(300);
const JS_REPL_POLL_LOGS_TRUNCATED_MARKER: &str =
    "[js_repl logs truncated; poll more frequently for complete streaming logs]";
const JS_REPL_POLL_ALL_LOGS_TRUNCATED_MARKER: &str =
    "[js_repl logs truncated; output exceeds byte limit]";
pub(crate) const JS_REPL_TIMEOUT_ERROR_MESSAGE: &str =
    "js_repl execution timed out; kernel reset, rerun your request";
const JS_REPL_CANCEL_ERROR_MESSAGE: &str = "js_repl execution canceled";
pub(crate) const JS_REPL_POLL_TIMEOUT_ARG_ERROR_MESSAGE: &str =
    "js_repl timeout_ms is not supported when poll=true; use js_repl_poll yield_time_ms";

/// Per-task js_repl handle stored on the turn context.
pub(crate) struct JsReplHandle {
    node_path: Option<PathBuf>,
    node_module_dirs: Vec<PathBuf>,
    cell: OnceCell<Arc<JsReplManager>>,
}

impl fmt::Debug for JsReplHandle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("JsReplHandle").finish_non_exhaustive()
    }
}

impl JsReplHandle {
    pub(crate) fn with_node_path(
        node_path: Option<PathBuf>,
        node_module_dirs: Vec<PathBuf>,
    ) -> Self {
        Self {
            node_path,
            node_module_dirs,
            cell: OnceCell::new(),
        }
    }

    pub(crate) async fn manager(&self) -> Result<Arc<JsReplManager>, FunctionCallError> {
        self.cell
            .get_or_try_init(|| async {
                JsReplManager::new(self.node_path.clone(), self.node_module_dirs.clone()).await
            })
            .await
            .cloned()
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JsReplArgs {
    pub code: String,
    #[serde(default)]
    pub timeout_ms: Option<u64>,
    #[serde(default)]
    pub poll: bool,
    #[serde(default)]
    pub session_id: Option<String>,
}

#[derive(Clone, Debug)]
pub struct JsExecResult {
    pub output: String,
}

#[derive(Clone, Debug)]
pub struct JsExecSubmission {
    pub exec_id: String,
    pub session_id: String,
}

#[derive(Clone, Debug)]
pub struct JsExecPollResult {
    pub exec_id: String,
    pub session_id: String,
    pub logs: Vec<String>,
    pub output: Option<String>,
    pub error: Option<String>,
    pub done: bool,
}

#[derive(Clone)]
struct KernelState {
    child: Arc<Mutex<Child>>,
    recent_stderr: Arc<Mutex<VecDeque<String>>>,
    stdin: Arc<Mutex<ChildStdin>>,
    pending_execs: Arc<Mutex<HashMap<String, tokio::sync::oneshot::Sender<ExecResultMessage>>>>,
    exec_contexts: Arc<Mutex<HashMap<String, ExecContext>>>,
    shutdown: CancellationToken,
}

struct PollSessionState {
    kernel: KernelState,
    active_exec: Option<String>,
    last_used: Instant,
}

#[derive(Clone)]
struct ExecContext {
    session: Arc<Session>,
    turn: Arc<TurnContext>,
    tracker: SharedTurnDiffTracker,
}

#[derive(Default)]
struct ExecToolCalls {
    in_flight: usize,
    notify: Arc<Notify>,
    cancel: CancellationToken,
}

struct ExecBuffer {
    event_call_id: String,
    session_id: Option<String>,
    session: Arc<Session>,
    turn: Arc<TurnContext>,
    logs: VecDeque<String>,
    logs_bytes: usize,
    logs_truncated: bool,
    all_logs: Vec<String>,
    all_logs_bytes: usize,
    all_logs_truncated: bool,
    output: Option<String>,
    error: Option<String>,
    done: bool,
    host_terminating: bool,
    terminal_kind: Option<ExecTerminalKind>,
    started_at: Instant,
    notify: Arc<Notify>,
    emitted_deltas: usize,
}

impl ExecBuffer {
    fn new(
        event_call_id: String,
        session_id: Option<String>,
        session: Arc<Session>,
        turn: Arc<TurnContext>,
    ) -> Self {
        Self {
            event_call_id,
            session_id,
            session,
            turn,
            logs: VecDeque::new(),
            logs_bytes: 0,
            logs_truncated: false,
            all_logs: Vec::new(),
            all_logs_bytes: 0,
            all_logs_truncated: false,
            output: None,
            error: None,
            done: false,
            host_terminating: false,
            terminal_kind: None,
            started_at: Instant::now(),
            notify: Arc::new(Notify::new()),
            emitted_deltas: 0,
        }
    }

    fn push_log(&mut self, text: String) {
        self.logs.push_back(text.clone());
        self.logs_bytes = self.logs_bytes.saturating_add(text.len());
        while self.logs_bytes > JS_REPL_POLL_LOG_QUEUE_MAX_BYTES {
            let Some(removed) = self.logs.pop_front() else {
                break;
            };
            self.logs_bytes = self.logs_bytes.saturating_sub(removed.len());
            self.logs_truncated = true;
        }
        if self.logs_truncated
            && self
                .logs
                .front()
                .is_none_or(|line| line != JS_REPL_POLL_LOGS_TRUNCATED_MARKER)
        {
            let marker_len = JS_REPL_POLL_LOGS_TRUNCATED_MARKER.len();
            while self.logs_bytes.saturating_add(marker_len) > JS_REPL_POLL_LOG_QUEUE_MAX_BYTES {
                let Some(removed) = self.logs.pop_front() else {
                    break;
                };
                self.logs_bytes = self.logs_bytes.saturating_sub(removed.len());
            }
            self.logs
                .push_front(JS_REPL_POLL_LOGS_TRUNCATED_MARKER.to_string());
            self.logs_bytes = self.logs_bytes.saturating_add(marker_len);
        }

        if self.all_logs_truncated {
            return;
        }
        let separator_bytes = if self.all_logs.is_empty() { 0 } else { 1 };
        let next_bytes = text.len() + separator_bytes;
        if self.all_logs_bytes.saturating_add(next_bytes) > JS_REPL_POLL_ALL_LOGS_MAX_BYTES {
            self.all_logs
                .push(JS_REPL_POLL_ALL_LOGS_TRUNCATED_MARKER.to_string());
            self.all_logs_truncated = true;
            return;
        }

        self.all_logs.push(text);
        self.all_logs_bytes = self.all_logs_bytes.saturating_add(next_bytes);
    }

    fn poll_logs(&mut self) -> Vec<String> {
        let drained: Vec<String> = self.logs.drain(..).collect();
        self.logs_bytes = 0;
        self.logs_truncated = false;
        drained
    }

    fn display_output(&self) -> String {
        if let Some(output) = self.output.as_deref()
            && !output.is_empty()
        {
            return output.to_string();
        }
        self.all_logs.join("\n")
    }

    fn output_delta_chunks_for_log_line(&mut self, line: &str) -> Vec<Vec<u8>> {
        if self.emitted_deltas >= MAX_EXEC_OUTPUT_DELTAS_PER_CALL {
            return Vec::new();
        }

        let mut text = String::with_capacity(line.len() + 1);
        text.push_str(line);
        text.push('\n');

        let remaining = MAX_EXEC_OUTPUT_DELTAS_PER_CALL - self.emitted_deltas;
        let chunks =
            split_utf8_chunks_with_limits(&text, JS_REPL_OUTPUT_DELTA_MAX_BYTES, remaining);
        self.emitted_deltas += chunks.len();
        chunks
    }
}

fn split_utf8_chunks_with_limits(input: &str, max_bytes: usize, max_chunks: usize) -> Vec<Vec<u8>> {
    if input.is_empty() || max_bytes == 0 || max_chunks == 0 {
        return Vec::new();
    }

    let bytes = input.as_bytes();
    let mut output = Vec::new();
    let mut start = 0usize;
    while start < input.len() && output.len() < max_chunks {
        let mut end = (start + max_bytes).min(input.len());
        while end > start && !input.is_char_boundary(end) {
            end -= 1;
        }
        if end == start {
            if let Some(ch) = input[start..].chars().next() {
                end = (start + ch.len_utf8()).min(input.len());
            } else {
                break;
            }
        }

        output.push(bytes[start..end].to_vec());
        start = end;
    }
    output
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExecTerminalKind {
    Success,
    Error,
    KernelExit,
    Cancelled,
}

struct ExecCompletionEvent {
    session: Arc<Session>,
    turn: Arc<TurnContext>,
    event_call_id: String,
    output: String,
    error: Option<String>,
    duration: Duration,
    timed_out: bool,
}

enum KernelStreamEnd {
    Shutdown,
    StdoutEof,
    StdoutReadError(String),
}

impl KernelStreamEnd {
    fn reason(&self) -> &'static str {
        match self {
            Self::Shutdown => "shutdown",
            Self::StdoutEof => "stdout_eof",
            Self::StdoutReadError(_) => "stdout_read_error",
        }
    }

    fn error(&self) -> Option<&str> {
        match self {
            Self::StdoutReadError(err) => Some(err),
            _ => None,
        }
    }
}

struct KernelDebugSnapshot {
    pid: Option<u32>,
    status: String,
    stderr_tail: String,
}

fn format_exit_status(status: std::process::ExitStatus) -> String {
    if let Some(code) = status.code() {
        return format!("code={code}");
    }
    #[cfg(unix)]
    if let Some(signal) = status.signal() {
        return format!("signal={signal}");
    }
    "unknown".to_string()
}

fn format_stderr_tail(lines: &VecDeque<String>) -> String {
    if lines.is_empty() {
        return "<empty>".to_string();
    }
    lines
        .iter()
        .cloned()
        .collect::<Vec<_>>()
        .join(JS_REPL_STDERR_TAIL_SEPARATOR)
}

fn truncate_utf8_prefix_by_bytes(input: &str, max_bytes: usize) -> String {
    if input.len() <= max_bytes {
        return input.to_string();
    }
    if max_bytes == 0 {
        return String::new();
    }
    let mut end = max_bytes;
    while end > 0 && !input.is_char_boundary(end) {
        end -= 1;
    }
    input[..end].to_string()
}

fn stderr_tail_formatted_bytes(lines: &VecDeque<String>) -> usize {
    if lines.is_empty() {
        return 0;
    }
    let payload_bytes: usize = lines.iter().map(String::len).sum();
    let separator_bytes = JS_REPL_STDERR_TAIL_SEPARATOR.len() * (lines.len() - 1);
    payload_bytes + separator_bytes
}

fn stderr_tail_bytes_with_candidate(lines: &VecDeque<String>, line: &str) -> usize {
    if lines.is_empty() {
        return line.len();
    }
    stderr_tail_formatted_bytes(lines) + JS_REPL_STDERR_TAIL_SEPARATOR.len() + line.len()
}

fn push_stderr_tail_line(lines: &mut VecDeque<String>, line: &str) -> String {
    let max_line_bytes = JS_REPL_STDERR_TAIL_LINE_MAX_BYTES.min(JS_REPL_STDERR_TAIL_MAX_BYTES);
    let bounded_line = truncate_utf8_prefix_by_bytes(line, max_line_bytes);
    if bounded_line.is_empty() {
        return bounded_line;
    }

    while !lines.is_empty()
        && (lines.len() >= JS_REPL_STDERR_TAIL_LINE_LIMIT
            || stderr_tail_bytes_with_candidate(lines, &bounded_line)
                > JS_REPL_STDERR_TAIL_MAX_BYTES)
    {
        lines.pop_front();
    }

    lines.push_back(bounded_line.clone());
    bounded_line
}

fn is_kernel_status_exited(status: &str) -> bool {
    status.starts_with("exited(")
}

fn should_include_model_diagnostics_for_write_error(
    err_message: &str,
    snapshot: &KernelDebugSnapshot,
) -> bool {
    is_kernel_status_exited(&snapshot.status)
        || err_message.to_ascii_lowercase().contains("broken pipe")
}

fn format_model_kernel_failure_details(
    reason: &str,
    stream_error: Option<&str>,
    snapshot: &KernelDebugSnapshot,
) -> String {
    let payload = serde_json::json!({
        "reason": reason,
        "stream_error": stream_error
            .map(|err| truncate_utf8_prefix_by_bytes(err, JS_REPL_MODEL_DIAG_ERROR_MAX_BYTES)),
        "kernel_pid": snapshot.pid,
        "kernel_status": snapshot.status,
        "kernel_stderr_tail": truncate_utf8_prefix_by_bytes(
            &snapshot.stderr_tail,
            JS_REPL_MODEL_DIAG_STDERR_MAX_BYTES,
        ),
    });
    let encoded = serde_json::to_string(&payload)
        .unwrap_or_else(|err| format!(r#"{{"reason":"serialization_error","error":"{err}"}}"#));
    format!("js_repl diagnostics: {encoded}")
}

fn with_model_kernel_failure_message(
    base_message: &str,
    reason: &str,
    stream_error: Option<&str>,
    snapshot: &KernelDebugSnapshot,
) -> String {
    format!(
        "{base_message}\n\n{}",
        format_model_kernel_failure_details(reason, stream_error, snapshot)
    )
}

fn join_outputs(stdout: &str, stderr: &str) -> String {
    if stdout.is_empty() {
        stderr.to_string()
    } else if stderr.is_empty() {
        stdout.to_string()
    } else {
        format!("{stdout}\n{stderr}")
    }
}

fn build_js_repl_exec_output(
    output: &str,
    error: Option<&str>,
    duration: Duration,
    timed_out: bool,
) -> ExecToolCallOutput {
    let stdout = output.to_string();
    let stderr = error.unwrap_or("").to_string();
    let aggregated_output = join_outputs(&stdout, &stderr);
    ExecToolCallOutput {
        exit_code: if error.is_some() { 1 } else { 0 },
        stdout: StreamOutput::new(stdout),
        stderr: StreamOutput::new(stderr),
        aggregated_output: StreamOutput::new(aggregated_output),
        duration,
        timed_out,
    }
}

pub(crate) async fn emit_js_repl_exec_end(
    session: &crate::codex::Session,
    turn: &crate::codex::TurnContext,
    call_id: &str,
    output: &str,
    error: Option<&str>,
    duration: Duration,
    timed_out: bool,
) {
    let exec_output = build_js_repl_exec_output(output, error, duration, timed_out);
    let emitter = ToolEmitter::shell(
        vec!["js_repl".to_string()],
        turn.cwd.clone(),
        ExecCommandSource::Agent,
        false,
    );
    let ctx = ToolEventCtx::new(session, turn, call_id, None);
    let stage = if error.is_some() {
        ToolEventStage::Failure(ToolEventFailure::Output(exec_output))
    } else {
        ToolEventStage::Success(exec_output)
    };
    emitter.emit(ctx, stage).await;
}
pub struct JsReplManager {
    node_path: Option<PathBuf>,
    node_module_dirs: Vec<PathBuf>,
    tmp_dir: tempfile::TempDir,
    kernel_script_path: PathBuf,
    kernel: Mutex<Option<KernelState>>,
    exec_lock: Arc<Semaphore>,
    exec_tool_calls: Arc<Mutex<HashMap<String, ExecToolCalls>>>,
    exec_store: Arc<Mutex<HashMap<String, ExecBuffer>>>,
    poll_sessions: Arc<Mutex<HashMap<String, PollSessionState>>>,
    exec_to_session: Arc<Mutex<HashMap<String, String>>>,
    poll_lifecycle: Arc<RwLock<()>>,
}

impl JsReplManager {
    async fn new(
        node_path: Option<PathBuf>,
        node_module_dirs: Vec<PathBuf>,
    ) -> Result<Arc<Self>, FunctionCallError> {
        let tmp_dir = tempfile::tempdir().map_err(|err| {
            FunctionCallError::RespondToModel(format!("failed to create js_repl temp dir: {err}"))
        })?;
        let kernel_script_path =
            Self::write_kernel_script(tmp_dir.path())
                .await
                .map_err(|err| {
                    FunctionCallError::RespondToModel(format!(
                        "failed to stage js_repl kernel script: {err}"
                    ))
                })?;

        let manager = Arc::new(Self {
            node_path,
            node_module_dirs,
            tmp_dir,
            kernel_script_path,
            kernel: Mutex::new(None),
            exec_lock: Arc::new(Semaphore::new(1)),
            exec_tool_calls: Arc::new(Mutex::new(HashMap::new())),
            exec_store: Arc::new(Mutex::new(HashMap::new())),
            poll_sessions: Arc::new(Mutex::new(HashMap::new())),
            exec_to_session: Arc::new(Mutex::new(HashMap::new())),
            poll_lifecycle: Arc::new(RwLock::new(())),
        });

        Ok(manager)
    }

    async fn register_exec_tool_calls(&self, exec_id: &str) {
        self.exec_tool_calls
            .lock()
            .await
            .insert(exec_id.to_string(), ExecToolCalls::default());
    }

    async fn clear_exec_tool_calls(&self, exec_id: &str) {
        if let Some(state) = self.exec_tool_calls.lock().await.remove(exec_id) {
            state.cancel.cancel();
            state.notify.notify_waiters();
        }
    }

    async fn cancel_exec_tool_calls(&self, exec_id: &str) {
        let notify = {
            let calls = self.exec_tool_calls.lock().await;
            calls.get(exec_id).map(|state| {
                state.cancel.cancel();
                Arc::clone(&state.notify)
            })
        };
        if let Some(notify) = notify {
            notify.notify_waiters();
        }
    }

    async fn wait_for_exec_tool_calls(&self, exec_id: &str) {
        loop {
            let notified = {
                let calls = self.exec_tool_calls.lock().await;
                calls
                    .get(exec_id)
                    .filter(|state| state.in_flight > 0)
                    .map(|state| Arc::clone(&state.notify).notified_owned())
            };
            match notified {
                Some(notified) => notified.await,
                None => return,
            }
        }
    }

    async fn begin_exec_tool_call(
        exec_tool_calls: &Arc<Mutex<HashMap<String, ExecToolCalls>>>,
        exec_id: &str,
    ) -> Option<CancellationToken> {
        let mut calls = exec_tool_calls.lock().await;
        let state = calls.get_mut(exec_id)?;
        state.in_flight += 1;
        Some(state.cancel.clone())
    }

    async fn finish_exec_tool_call(
        exec_tool_calls: &Arc<Mutex<HashMap<String, ExecToolCalls>>>,
        exec_id: &str,
    ) {
        let notify = {
            let mut calls = exec_tool_calls.lock().await;
            let Some(state) = calls.get_mut(exec_id) else {
                return;
            };
            if state.in_flight == 0 {
                return;
            }
            state.in_flight -= 1;
            if state.in_flight == 0 {
                Some(Arc::clone(&state.notify))
            } else {
                None
            }
        };
        if let Some(notify) = notify {
            notify.notify_waiters();
        }
    }

    async fn wait_for_exec_tool_calls_map(
        exec_tool_calls: &Arc<Mutex<HashMap<String, ExecToolCalls>>>,
        exec_id: &str,
    ) {
        loop {
            let notified = {
                let calls = exec_tool_calls.lock().await;
                calls
                    .get(exec_id)
                    .filter(|state| state.in_flight > 0)
                    .map(|state| Arc::clone(&state.notify).notified_owned())
            };
            match notified {
                Some(notified) => notified.await,
                None => return,
            }
        }
    }

    async fn clear_exec_tool_calls_map(
        exec_tool_calls: &Arc<Mutex<HashMap<String, ExecToolCalls>>>,
        exec_id: &str,
    ) {
        if let Some(state) = exec_tool_calls.lock().await.remove(exec_id) {
            state.cancel.cancel();
            state.notify.notify_waiters();
        }
    }

    async fn cancel_exec_tool_calls_map(
        exec_tool_calls: &Arc<Mutex<HashMap<String, ExecToolCalls>>>,
        exec_id: &str,
    ) {
        let notify = {
            let calls = exec_tool_calls.lock().await;
            calls.get(exec_id).map(|state| {
                state.cancel.cancel();
                Arc::clone(&state.notify)
            })
        };
        if let Some(notify) = notify {
            notify.notify_waiters();
        }
    }

    async fn clear_all_exec_tool_calls_map(
        exec_tool_calls: &Arc<Mutex<HashMap<String, ExecToolCalls>>>,
    ) {
        let states = {
            let mut calls = exec_tool_calls.lock().await;
            calls.drain().map(|(_, state)| state).collect::<Vec<_>>()
        };
        for state in states {
            state.cancel.cancel();
            state.notify.notify_waiters();
        }
    }

    fn schedule_completed_exec_eviction(
        exec_store: Arc<Mutex<HashMap<String, ExecBuffer>>>,
        exec_id: String,
    ) {
        tokio::spawn(async move {
            tokio::time::sleep(JS_REPL_POLL_COMPLETED_EXEC_RETENTION).await;
            let mut store = exec_store.lock().await;
            if store.get(&exec_id).is_some_and(|entry| entry.done) {
                store.remove(&exec_id);
            }
        });
    }

    async fn emit_completion_event(event: ExecCompletionEvent) {
        emit_js_repl_exec_end(
            event.session.as_ref(),
            event.turn.as_ref(),
            &event.event_call_id,
            &event.output,
            event.error.as_deref(),
            event.duration,
            event.timed_out,
        )
        .await;
    }

    async fn complete_exec_in_store(
        exec_store: &Arc<Mutex<HashMap<String, ExecBuffer>>>,
        exec_id: &str,
        terminal_kind: ExecTerminalKind,
        output: Option<String>,
        error: Option<String>,
        override_kernel_exit: bool,
    ) -> bool {
        let event = {
            let mut store = exec_store.lock().await;
            let Some(entry) = store.get_mut(exec_id) else {
                return false;
            };
            if terminal_kind == ExecTerminalKind::KernelExit && entry.host_terminating {
                return false;
            }
            let should_override = override_kernel_exit
                && entry.done
                && matches!(entry.terminal_kind, Some(ExecTerminalKind::KernelExit));
            if entry.done && !should_override {
                return false;
            }

            if !entry.done {
                entry.done = true;
            }
            entry.host_terminating = false;
            if let Some(output) = output {
                entry.output = Some(output);
            }
            if error.is_some() || terminal_kind != ExecTerminalKind::Success {
                entry.error = error;
            } else {
                entry.error = None;
            }
            entry.terminal_kind = Some(terminal_kind);
            entry.notify.notify_waiters();

            Some(ExecCompletionEvent {
                session: Arc::clone(&entry.session),
                turn: Arc::clone(&entry.turn),
                event_call_id: entry.event_call_id.clone(),
                output: entry.display_output(),
                error: entry.error.clone(),
                duration: entry.started_at.elapsed(),
                timed_out: false,
            })
        };

        if let Some(event) = event {
            Self::schedule_completed_exec_eviction(Arc::clone(exec_store), exec_id.to_string());
            Self::emit_completion_event(event).await;
            return true;
        }
        false
    }

    async fn complete_exec(
        &self,
        exec_id: &str,
        terminal_kind: ExecTerminalKind,
        output: Option<String>,
        error: Option<String>,
        override_kernel_exit: bool,
    ) -> bool {
        Self::complete_exec_in_store(
            &self.exec_store,
            exec_id,
            terminal_kind,
            output,
            error,
            override_kernel_exit,
        )
        .await
    }

    pub async fn reset(&self) -> Result<(), FunctionCallError> {
        let _permit = self.exec_lock.clone().acquire_owned().await.map_err(|_| {
            FunctionCallError::RespondToModel("js_repl execution unavailable".to_string())
        })?;
        let _poll_lifecycle = self.poll_lifecycle.write().await;
        self.reset_kernel().await;
        self.reset_all_poll_sessions().await;
        Self::clear_all_exec_tool_calls_map(&self.exec_tool_calls).await;
        Ok(())
    }

    pub async fn reset_session(&self, session_id: &str) -> Result<(), FunctionCallError> {
        let _poll_lifecycle = self.poll_lifecycle.write().await;
        if self.reset_poll_session(session_id, "poll_reset").await {
            return Ok(());
        }
        Err(FunctionCallError::RespondToModel(
            "js_repl session id not found".to_string(),
        ))
    }

    async fn reset_kernel(&self) {
        let state = {
            let mut guard = self.kernel.lock().await;
            guard.take()
        };
        if let Some(state) = state {
            state.shutdown.cancel();
            Self::kill_kernel_child(&state.child, "reset").await;
        }
    }

    async fn mark_exec_host_terminating(&self, exec_id: &str) {
        let mut store = self.exec_store.lock().await;
        if let Some(entry) = store.get_mut(exec_id)
            && !entry.done
        {
            entry.host_terminating = true;
        }
    }

    async fn reset_poll_session(&self, session_id: &str, kill_reason: &'static str) -> bool {
        let state = {
            let mut sessions = self.poll_sessions.lock().await;
            sessions.remove(session_id)
        };
        let Some(mut state) = state else {
            return false;
        };
        if let Some(exec_id) = state.active_exec.as_deref() {
            self.mark_exec_host_terminating(exec_id).await;
        }
        state.kernel.shutdown.cancel();
        Self::kill_kernel_child(&state.kernel.child, kill_reason).await;
        if let Some(exec_id) = state.active_exec.take() {
            self.exec_to_session.lock().await.remove(&exec_id);
            self.cancel_exec_tool_calls(&exec_id).await;
            self.wait_for_exec_tool_calls(&exec_id).await;
            self.complete_exec(
                &exec_id,
                ExecTerminalKind::Cancelled,
                None,
                Some(JS_REPL_CANCEL_ERROR_MESSAGE.to_string()),
                true,
            )
            .await;
            self.clear_exec_tool_calls(&exec_id).await;
        }
        true
    }

    async fn reset_all_poll_sessions(&self) {
        let states = {
            let mut sessions = self.poll_sessions.lock().await;
            sessions.drain().collect::<Vec<_>>()
        };
        for (_session_id, mut state) in states {
            if let Some(exec_id) = state.active_exec.as_deref() {
                self.mark_exec_host_terminating(exec_id).await;
            }
            state.kernel.shutdown.cancel();
            Self::kill_kernel_child(&state.kernel.child, "poll_reset_all").await;
            if let Some(exec_id) = state.active_exec.take() {
                self.exec_to_session.lock().await.remove(&exec_id);
                self.cancel_exec_tool_calls(&exec_id).await;
                self.wait_for_exec_tool_calls(&exec_id).await;
                self.complete_exec(
                    &exec_id,
                    ExecTerminalKind::Cancelled,
                    None,
                    Some(JS_REPL_CANCEL_ERROR_MESSAGE.to_string()),
                    true,
                )
                .await;
                self.clear_exec_tool_calls(&exec_id).await;
            }
        }
    }

    pub async fn execute(
        &self,
        session: Arc<Session>,
        turn: Arc<TurnContext>,
        tracker: SharedTurnDiffTracker,
        args: JsReplArgs,
    ) -> Result<JsExecResult, FunctionCallError> {
        if args.session_id.is_some() {
            return Err(FunctionCallError::RespondToModel(
                "js_repl session_id is only supported when poll=true".to_string(),
            ));
        }
        let _permit = self.exec_lock.clone().acquire_owned().await.map_err(|_| {
            FunctionCallError::RespondToModel("js_repl execution unavailable".to_string())
        })?;

        let (stdin, pending_execs, exec_contexts, child, recent_stderr) = {
            let mut kernel = self.kernel.lock().await;
            if kernel.is_none() {
                let state = self
                    .start_kernel(Arc::clone(&turn), Some(session.conversation_id), None)
                    .await
                    .map_err(FunctionCallError::RespondToModel)?;
                *kernel = Some(state);
            }

            let state = match kernel.as_ref() {
                Some(state) => state,
                None => {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl kernel unavailable".to_string(),
                    ));
                }
            };
            (
                Arc::clone(&state.stdin),
                Arc::clone(&state.pending_execs),
                Arc::clone(&state.exec_contexts),
                Arc::clone(&state.child),
                Arc::clone(&state.recent_stderr),
            )
        };

        let (req_id, rx) = {
            let req_id = Uuid::new_v4().to_string();
            let mut pending = pending_execs.lock().await;
            let (tx, rx) = tokio::sync::oneshot::channel();
            pending.insert(req_id.clone(), tx);
            exec_contexts.lock().await.insert(
                req_id.clone(),
                ExecContext {
                    session: Arc::clone(&session),
                    turn: Arc::clone(&turn),
                    tracker,
                },
            );
            (req_id, rx)
        };
        self.register_exec_tool_calls(&req_id).await;

        let payload = HostToKernel::Exec {
            id: req_id.clone(),
            code: args.code,
            timeout_ms: args.timeout_ms,
            stream_logs: false,
        };

        if let Err(err) = Self::write_message(&stdin, &payload).await {
            pending_execs.lock().await.remove(&req_id);
            exec_contexts.lock().await.remove(&req_id);
            self.clear_exec_tool_calls(&req_id).await;
            let snapshot = Self::kernel_debug_snapshot(&child, &recent_stderr).await;
            let err_message = err.to_string();
            warn!(
                exec_id = %req_id,
                error = %err_message,
                kernel_pid = ?snapshot.pid,
                kernel_status = %snapshot.status,
                kernel_stderr_tail = %snapshot.stderr_tail,
                "failed to submit js_repl exec request to kernel"
            );
            let message =
                if should_include_model_diagnostics_for_write_error(&err_message, &snapshot) {
                    with_model_kernel_failure_message(
                        &err_message,
                        "write_failed",
                        Some(&err_message),
                        &snapshot,
                    )
                } else {
                    err_message
                };
            return Err(FunctionCallError::RespondToModel(message));
        }

        let timeout_ms = args.timeout_ms.unwrap_or(30_000);
        let response = match tokio::time::timeout(Duration::from_millis(timeout_ms), rx).await {
            Ok(Ok(msg)) => msg,
            Ok(Err(_)) => {
                let mut pending = pending_execs.lock().await;
                pending.remove(&req_id);
                exec_contexts.lock().await.remove(&req_id);
                self.cancel_exec_tool_calls(&req_id).await;
                self.wait_for_exec_tool_calls(&req_id).await;
                self.clear_exec_tool_calls(&req_id).await;
                let snapshot = Self::kernel_debug_snapshot(&child, &recent_stderr).await;
                let message = if is_kernel_status_exited(&snapshot.status) {
                    with_model_kernel_failure_message(
                        "js_repl kernel closed unexpectedly",
                        "response_channel_closed",
                        None,
                        &snapshot,
                    )
                } else {
                    "js_repl kernel closed unexpectedly".to_string()
                };
                return Err(FunctionCallError::RespondToModel(message));
            }
            Err(_) => {
                pending_execs.lock().await.remove(&req_id);
                exec_contexts.lock().await.remove(&req_id);
                self.reset_kernel().await;
                self.cancel_exec_tool_calls(&req_id).await;
                self.wait_for_exec_tool_calls(&req_id).await;
                self.clear_exec_tool_calls(&req_id).await;
                return Err(FunctionCallError::RespondToModel(
                    JS_REPL_TIMEOUT_ERROR_MESSAGE.to_string(),
                ));
            }
        };

        match response {
            ExecResultMessage::Ok { output } => Ok(JsExecResult { output }),
            ExecResultMessage::Err { message } => Err(FunctionCallError::RespondToModel(message)),
        }
    }

    pub async fn submit(
        self: Arc<Self>,
        session: Arc<Session>,
        turn: Arc<TurnContext>,
        tracker: SharedTurnDiffTracker,
        event_call_id: String,
        args: JsReplArgs,
    ) -> Result<JsExecSubmission, FunctionCallError> {
        if args.timeout_ms.is_some() {
            return Err(FunctionCallError::RespondToModel(
                JS_REPL_POLL_TIMEOUT_ARG_ERROR_MESSAGE.to_string(),
            ));
        }
        let user_provided_session_id = args.session_id.is_some();
        let session_id = args
            .session_id
            .unwrap_or_else(|| Uuid::new_v4().to_string());
        if session_id.trim().is_empty() {
            return Err(FunctionCallError::RespondToModel(
                "js_repl session_id must not be empty".to_string(),
            ));
        }
        let _poll_lifecycle = self.poll_lifecycle.read().await;

        let mut pruned_idle_session: Option<PollSessionState> = None;
        let mut needs_new_session = false;
        {
            let mut sessions = self.poll_sessions.lock().await;
            if let Some(state) = sessions.get_mut(&session_id) {
                if let Some(active_exec) = state.active_exec.as_deref() {
                    return Err(FunctionCallError::RespondToModel(format!(
                        "js_repl session `{session_id}` already has a running exec: `{active_exec}`"
                    )));
                }
                state.last_used = Instant::now();
            } else if user_provided_session_id {
                return Err(FunctionCallError::RespondToModel(
                    "js_repl session id not found".to_string(),
                ));
            } else {
                if sessions.len() >= JS_REPL_POLL_MAX_SESSIONS {
                    let lru_idle_session = sessions
                        .iter()
                        .filter(|(_, state)| state.active_exec.is_none())
                        .min_by_key(|(_, state)| state.last_used)
                        .map(|(id, _)| id.clone());
                    let Some(lru_idle_session) = lru_idle_session else {
                        return Err(FunctionCallError::RespondToModel(format!(
                            "js_repl polling has reached the maximum of {JS_REPL_POLL_MAX_SESSIONS} active sessions; reset a session before creating another"
                        )));
                    };
                    pruned_idle_session = sessions.remove(&lru_idle_session);
                }
                needs_new_session = true;
            }
        }
        if let Some(state) = pruned_idle_session {
            state.kernel.shutdown.cancel();
            Self::kill_kernel_child(&state.kernel.child, "poll_prune_idle_session").await;
        }
        if needs_new_session {
            let mut new_kernel = Some(
                self.start_kernel(
                    Arc::clone(&turn),
                    Some(session.conversation_id),
                    Some(session_id.clone()),
                )
                .await
                .map_err(FunctionCallError::RespondToModel)?,
            );
            let mut stale_kernel = None;
            let mut capacity_kernel = None;
            {
                let mut sessions = self.poll_sessions.lock().await;
                if sessions.contains_key(&session_id) {
                    stale_kernel = new_kernel.take();
                } else if sessions.len() >= JS_REPL_POLL_MAX_SESSIONS {
                    capacity_kernel = new_kernel.take();
                } else if let Some(kernel) = new_kernel.take() {
                    sessions.insert(
                        session_id.clone(),
                        PollSessionState {
                            kernel,
                            active_exec: None,
                            last_used: Instant::now(),
                        },
                    );
                }
            }
            if let Some(kernel) = stale_kernel {
                kernel.shutdown.cancel();
                Self::kill_kernel_child(&kernel.child, "poll_submit_session_race").await;
            }
            if let Some(kernel) = capacity_kernel {
                kernel.shutdown.cancel();
                Self::kill_kernel_child(&kernel.child, "poll_submit_capacity_race").await;
                return Err(FunctionCallError::RespondToModel(format!(
                    "js_repl polling has reached the maximum of {JS_REPL_POLL_MAX_SESSIONS} active sessions; reset a session before creating another"
                )));
            }
        }

        let req_id = Uuid::new_v4().to_string();
        let (stdin, exec_contexts, child, recent_stderr) = {
            let mut sessions = self.poll_sessions.lock().await;
            let Some(state) = sessions.get_mut(&session_id) else {
                return Err(FunctionCallError::RespondToModel(format!(
                    "js_repl session `{session_id}` is unavailable"
                )));
            };
            if let Some(active_exec) = state.active_exec.as_deref() {
                return Err(FunctionCallError::RespondToModel(format!(
                    "js_repl session `{session_id}` already has a running exec: `{active_exec}`"
                )));
            }
            state.active_exec = Some(req_id.clone());
            state.last_used = Instant::now();
            (
                Arc::clone(&state.kernel.stdin),
                Arc::clone(&state.kernel.exec_contexts),
                Arc::clone(&state.kernel.child),
                Arc::clone(&state.kernel.recent_stderr),
            )
        };

        exec_contexts.lock().await.insert(
            req_id.clone(),
            ExecContext {
                session: Arc::clone(&session),
                turn: Arc::clone(&turn),
                tracker,
            },
        );
        self.exec_store.lock().await.insert(
            req_id.clone(),
            ExecBuffer::new(
                event_call_id,
                Some(session_id.clone()),
                Arc::clone(&session),
                Arc::clone(&turn),
            ),
        );
        self.exec_to_session
            .lock()
            .await
            .insert(req_id.clone(), session_id.clone());
        self.register_exec_tool_calls(&req_id).await;

        let payload = HostToKernel::Exec {
            id: req_id.clone(),
            code: args.code,
            timeout_ms: args.timeout_ms,
            stream_logs: true,
        };
        if let Err(err) = Self::write_message(&stdin, &payload).await {
            self.exec_store.lock().await.remove(&req_id);
            exec_contexts.lock().await.remove(&req_id);
            self.exec_to_session.lock().await.remove(&req_id);
            self.clear_exec_tool_calls(&req_id).await;
            let removed_state = {
                let mut sessions = self.poll_sessions.lock().await;
                let should_remove = sessions
                    .get(&session_id)
                    .is_some_and(|state| state.active_exec.as_deref() == Some(req_id.as_str()));
                if should_remove {
                    sessions.remove(&session_id)
                } else {
                    None
                }
            };
            if let Some(state) = removed_state {
                state.kernel.shutdown.cancel();
                Self::kill_kernel_child(&state.kernel.child, "poll_submit_write_failed").await;
            }
            let snapshot = Self::kernel_debug_snapshot(&child, &recent_stderr).await;
            let err_message = err.to_string();
            warn!(
                exec_id = %req_id,
                session_id = %session_id,
                error = %err_message,
                kernel_pid = ?snapshot.pid,
                kernel_status = %snapshot.status,
                kernel_stderr_tail = %snapshot.stderr_tail,
                "failed to submit polled js_repl exec request to kernel"
            );
            let message =
                if should_include_model_diagnostics_for_write_error(&err_message, &snapshot) {
                    with_model_kernel_failure_message(
                        &err_message,
                        "write_failed",
                        Some(&err_message),
                        &snapshot,
                    )
                } else {
                    err_message
                };
            return Err(FunctionCallError::RespondToModel(message));
        }

        Ok(JsExecSubmission {
            exec_id: req_id,
            session_id,
        })
    }

    pub async fn poll(
        &self,
        exec_id: &str,
        yield_time_ms: Option<u64>,
    ) -> Result<JsExecPollResult, FunctionCallError> {
        let deadline = Instant::now() + Duration::from_millis(clamp_poll_ms(yield_time_ms));

        loop {
            let (notify, session_id) = {
                let mut store = self.exec_store.lock().await;
                let Some(entry) = store.get_mut(exec_id) else {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl exec id not found".to_string(),
                    ));
                };
                let Some(session_id) = entry.session_id.clone() else {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl exec id is not pollable".to_string(),
                    ));
                };
                if !entry.logs.is_empty() || entry.done {
                    let drained_logs = entry.poll_logs();
                    let output = entry.output.clone();
                    let error = entry.error.clone();
                    let done = entry.done;
                    return Ok(JsExecPollResult {
                        exec_id: exec_id.to_string(),
                        session_id,
                        logs: drained_logs,
                        output,
                        error,
                        done,
                    });
                }
                (Arc::clone(&entry.notify), session_id)
            };
            if let Some(state) = self.poll_sessions.lock().await.get_mut(&session_id) {
                state.last_used = Instant::now();
            }

            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                let mut store = self.exec_store.lock().await;
                let Some(entry) = store.get_mut(exec_id) else {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl exec id not found".to_string(),
                    ));
                };
                let Some(session_id) = entry.session_id.clone() else {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl exec id is not pollable".to_string(),
                    ));
                };
                return Ok(JsExecPollResult {
                    exec_id: exec_id.to_string(),
                    session_id,
                    logs: entry.poll_logs(),
                    output: entry.output.clone(),
                    error: entry.error.clone(),
                    done: entry.done,
                });
            }

            if tokio::time::timeout(remaining, notify.notified())
                .await
                .is_err()
            {
                // Re-snapshot after timeout so a missed notify cannot return stale data.
                let mut store = self.exec_store.lock().await;
                let Some(entry) = store.get_mut(exec_id) else {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl exec id not found".to_string(),
                    ));
                };
                let Some(session_id) = entry.session_id.clone() else {
                    return Err(FunctionCallError::RespondToModel(
                        "js_repl exec id is not pollable".to_string(),
                    ));
                };
                return Ok(JsExecPollResult {
                    exec_id: exec_id.to_string(),
                    session_id,
                    logs: entry.poll_logs(),
                    output: entry.output.clone(),
                    error: entry.error.clone(),
                    done: entry.done,
                });
            }
        }
    }
    async fn start_kernel(
        &self,
        turn: Arc<TurnContext>,
        thread_id: Option<ThreadId>,
        poll_session_id: Option<String>,
    ) -> Result<KernelState, String> {
        let node_path = resolve_node(self.node_path.as_deref()).ok_or_else(|| {
            "Node runtime not found; install Node or set CODEX_JS_REPL_NODE_PATH".to_string()
        })?;
        ensure_node_version(&node_path).await?;

        let kernel_path = self.kernel_script_path.clone();

        let mut env = create_env(&turn.shell_environment_policy, thread_id);
        env.insert(
            "CODEX_JS_TMP_DIR".to_string(),
            self.tmp_dir.path().to_string_lossy().to_string(),
        );
        let node_module_dirs_key = "CODEX_JS_REPL_NODE_MODULE_DIRS";
        if !self.node_module_dirs.is_empty() && !env.contains_key(node_module_dirs_key) {
            let joined = std::env::join_paths(&self.node_module_dirs)
                .map_err(|err| format!("failed to join js_repl_node_module_dirs: {err}"))?;
            env.insert(
                node_module_dirs_key.to_string(),
                joined.to_string_lossy().to_string(),
            );
        }

        let spec = CommandSpec {
            program: node_path.to_string_lossy().to_string(),
            args: vec![
                "--experimental-vm-modules".to_string(),
                kernel_path.to_string_lossy().to_string(),
            ],
            cwd: turn.cwd.clone(),
            env,
            expiration: ExecExpiration::DefaultTimeout,
            sandbox_permissions: SandboxPermissions::UseDefault,
            justification: None,
        };

        let sandbox = SandboxManager::new();
        let has_managed_network_requirements = turn
            .config
            .config_layer_stack
            .requirements_toml()
            .network
            .is_some();
        let sandbox_type = sandbox.select_initial(
            &turn.sandbox_policy,
            SandboxablePreference::Auto,
            turn.windows_sandbox_level,
            has_managed_network_requirements,
        );
        let exec_env = sandbox
            .transform(crate::sandboxing::SandboxTransformRequest {
                spec,
                policy: &turn.sandbox_policy,
                sandbox: sandbox_type,
                enforce_managed_network: has_managed_network_requirements,
                network: None,
                sandbox_policy_cwd: &turn.cwd,
                codex_linux_sandbox_exe: turn.codex_linux_sandbox_exe.as_ref(),
                use_linux_sandbox_bwrap: turn
                    .features
                    .enabled(crate::features::Feature::UseLinuxSandboxBwrap),
                windows_sandbox_level: turn.windows_sandbox_level,
            })
            .map_err(|err| format!("failed to configure sandbox for js_repl: {err}"))?;

        let mut cmd =
            tokio::process::Command::new(exec_env.command.first().cloned().unwrap_or_default());
        if exec_env.command.len() > 1 {
            cmd.args(&exec_env.command[1..]);
        }
        #[cfg(unix)]
        cmd.arg0(
            exec_env
                .arg0
                .clone()
                .unwrap_or_else(|| exec_env.command.first().cloned().unwrap_or_default()),
        );
        cmd.current_dir(&exec_env.cwd);
        cmd.env_clear();
        cmd.envs(exec_env.env);
        cmd.stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .kill_on_drop(true);

        let mut child = cmd
            .spawn()
            .map_err(|err| format!("failed to start Node runtime: {err}"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| "js_repl kernel missing stdout".to_string())?;
        let stderr = child.stderr.take();
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| "js_repl kernel missing stdin".to_string())?;

        let shutdown = CancellationToken::new();
        let pending_execs: Arc<
            Mutex<HashMap<String, tokio::sync::oneshot::Sender<ExecResultMessage>>>,
        > = Arc::new(Mutex::new(HashMap::new()));
        let exec_contexts: Arc<Mutex<HashMap<String, ExecContext>>> =
            Arc::new(Mutex::new(HashMap::new()));
        let stdin_arc = Arc::new(Mutex::new(stdin));
        let child = Arc::new(Mutex::new(child));
        let recent_stderr = Arc::new(Mutex::new(VecDeque::with_capacity(
            JS_REPL_STDERR_TAIL_LINE_LIMIT,
        )));

        tokio::spawn(Self::read_stdout(
            stdout,
            Arc::clone(&child),
            Arc::clone(&recent_stderr),
            Arc::clone(&pending_execs),
            Arc::clone(&exec_contexts),
            Arc::clone(&self.exec_tool_calls),
            Arc::clone(&self.exec_store),
            Arc::clone(&self.poll_sessions),
            Arc::clone(&self.exec_to_session),
            Arc::clone(&stdin_arc),
            poll_session_id,
            shutdown.clone(),
        ));
        if let Some(stderr) = stderr {
            tokio::spawn(Self::read_stderr(
                stderr,
                Arc::clone(&recent_stderr),
                shutdown.clone(),
            ));
        } else {
            warn!("js_repl kernel missing stderr");
        }

        Ok(KernelState {
            child,
            recent_stderr,
            stdin: stdin_arc,
            pending_execs,
            exec_contexts,
            shutdown,
        })
    }

    async fn write_kernel_script(dir: &Path) -> Result<PathBuf, std::io::Error> {
        let kernel_path = dir.join("js_repl_kernel.js");
        let meriyah_path = dir.join("meriyah.umd.min.js");
        tokio::fs::write(&kernel_path, KERNEL_SOURCE).await?;
        tokio::fs::write(&meriyah_path, MERIYAH_UMD).await?;
        Ok(kernel_path)
    }

    async fn write_message(
        stdin: &Arc<Mutex<ChildStdin>>,
        msg: &HostToKernel,
    ) -> Result<(), FunctionCallError> {
        let encoded = serde_json::to_string(msg).map_err(|err| {
            FunctionCallError::RespondToModel(format!("failed to serialize kernel message: {err}"))
        })?;
        let mut guard = stdin.lock().await;
        guard.write_all(encoded.as_bytes()).await.map_err(|err| {
            FunctionCallError::RespondToModel(format!("failed to write to kernel: {err}"))
        })?;
        guard.write_all(b"\n").await.map_err(|err| {
            FunctionCallError::RespondToModel(format!("failed to flush kernel message: {err}"))
        })?;
        Ok(())
    }

    async fn kernel_stderr_tail_snapshot(recent_stderr: &Arc<Mutex<VecDeque<String>>>) -> String {
        let tail = recent_stderr.lock().await;
        format_stderr_tail(&tail)
    }

    async fn kernel_debug_snapshot(
        child: &Arc<Mutex<Child>>,
        recent_stderr: &Arc<Mutex<VecDeque<String>>>,
    ) -> KernelDebugSnapshot {
        let (pid, status) = {
            let mut guard = child.lock().await;
            let pid = guard.id();
            let status = match guard.try_wait() {
                Ok(Some(status)) => format!("exited({})", format_exit_status(status)),
                Ok(None) => "running".to_string(),
                Err(err) => format!("unknown ({err})"),
            };
            (pid, status)
        };
        let stderr_tail = {
            let tail = recent_stderr.lock().await;
            format_stderr_tail(&tail)
        };
        KernelDebugSnapshot {
            pid,
            status,
            stderr_tail,
        }
    }

    async fn kill_kernel_child(child: &Arc<Mutex<Child>>, reason: &'static str) {
        let mut guard = child.lock().await;
        let pid = guard.id();
        match guard.try_wait() {
            Ok(Some(_)) => return,
            Ok(None) => {}
            Err(err) => {
                warn!(
                    kernel_pid = ?pid,
                    kill_reason = reason,
                    error = %err,
                    "failed to inspect js_repl kernel before kill"
                );
            }
        }

        if let Err(err) = guard.start_kill() {
            warn!(
                kernel_pid = ?pid,
                kill_reason = reason,
                error = %err,
                "failed to send kill signal to js_repl kernel"
            );
            return;
        }

        match tokio::time::timeout(Duration::from_secs(2), guard.wait()).await {
            Ok(Ok(_status)) => {}
            Ok(Err(err)) => {
                warn!(
                    kernel_pid = ?pid,
                    kill_reason = reason,
                    error = %err,
                    "failed while waiting for js_repl kernel exit"
                );
            }
            Err(_) => {
                warn!(
                    kernel_pid = ?pid,
                    kill_reason = reason,
                    "timed out waiting for js_repl kernel to exit after kill"
                );
            }
        }
    }

    fn truncate_id_list(ids: &[String]) -> Vec<String> {
        if ids.len() <= JS_REPL_EXEC_ID_LOG_LIMIT {
            return ids.to_vec();
        }
        let mut output = ids[..JS_REPL_EXEC_ID_LOG_LIMIT].to_vec();
        output.push(format!("...+{}", ids.len() - JS_REPL_EXEC_ID_LOG_LIMIT));
        output
    }

    #[allow(clippy::too_many_arguments)]
    async fn read_stdout(
        stdout: tokio::process::ChildStdout,
        child: Arc<Mutex<Child>>,
        recent_stderr: Arc<Mutex<VecDeque<String>>>,
        pending_execs: Arc<Mutex<HashMap<String, tokio::sync::oneshot::Sender<ExecResultMessage>>>>,
        exec_contexts: Arc<Mutex<HashMap<String, ExecContext>>>,
        exec_tool_calls: Arc<Mutex<HashMap<String, ExecToolCalls>>>,
        exec_store: Arc<Mutex<HashMap<String, ExecBuffer>>>,
        poll_sessions: Arc<Mutex<HashMap<String, PollSessionState>>>,
        exec_to_session: Arc<Mutex<HashMap<String, String>>>,
        stdin: Arc<Mutex<ChildStdin>>,
        poll_session_id: Option<String>,
        shutdown: CancellationToken,
    ) {
        let mut reader = BufReader::new(stdout).lines();
        let end_reason = loop {
            let line = tokio::select! {
                _ = shutdown.cancelled() => break KernelStreamEnd::Shutdown,
                res = reader.next_line() => match res {
                    Ok(Some(line)) => line,
                    Ok(None) => break KernelStreamEnd::StdoutEof,
                    Err(err) => break KernelStreamEnd::StdoutReadError(err.to_string()),
                },
            };

            let parsed: Result<KernelToHost, _> = serde_json::from_str(&line);
            let msg = match parsed {
                Ok(m) => m,
                Err(err) => {
                    warn!("js_repl kernel sent invalid json: {err} (line: {line})");
                    continue;
                }
            };

            match msg {
                KernelToHost::ExecStarted { id } => {
                    drop(id);
                }
                KernelToHost::ExecLog { id, text } => {
                    let (session, turn, event_call_id, delta_chunks) = {
                        let mut store = exec_store.lock().await;
                        let Some(entry) = store.get_mut(&id) else {
                            continue;
                        };
                        entry.push_log(text.clone());
                        let delta_chunks = entry.output_delta_chunks_for_log_line(&text);
                        entry.notify.notify_waiters();
                        (
                            Arc::clone(&entry.session),
                            Arc::clone(&entry.turn),
                            entry.event_call_id.clone(),
                            delta_chunks,
                        )
                    };

                    for chunk in delta_chunks {
                        let event = ExecCommandOutputDeltaEvent {
                            call_id: event_call_id.clone(),
                            stream: ExecOutputStream::Stdout,
                            chunk,
                        };
                        session
                            .send_event(turn.as_ref(), EventMsg::ExecCommandOutputDelta(event))
                            .await;
                    }
                }
                KernelToHost::ExecResult {
                    id,
                    ok,
                    output,
                    error,
                } => {
                    let session_id = exec_to_session.lock().await.remove(&id);
                    JsReplManager::wait_for_exec_tool_calls_map(&exec_tool_calls, &id).await;
                    let mut pending = pending_execs.lock().await;
                    if let Some(tx) = pending.remove(&id) {
                        let payload = if ok {
                            ExecResultMessage::Ok {
                                output: output.clone(),
                            }
                        } else {
                            ExecResultMessage::Err {
                                message: error
                                    .clone()
                                    .unwrap_or_else(|| "js_repl execution failed".to_string()),
                            }
                        };
                        let _ = tx.send(payload);
                    }
                    drop(pending);
                    let terminal_kind = if ok {
                        ExecTerminalKind::Success
                    } else {
                        ExecTerminalKind::Error
                    };
                    let completion_error = if ok {
                        None
                    } else {
                        Some(error.unwrap_or_else(|| "js_repl execution failed".to_string()))
                    };
                    Self::complete_exec_in_store(
                        &exec_store,
                        &id,
                        terminal_kind,
                        Some(output),
                        completion_error,
                        false,
                    )
                    .await;
                    exec_contexts.lock().await.remove(&id);
                    JsReplManager::clear_exec_tool_calls_map(&exec_tool_calls, &id).await;
                    if let Some(session_id) = session_id {
                        let mut sessions = poll_sessions.lock().await;
                        if let Some(state) = sessions.get_mut(&session_id)
                            && state.active_exec.as_deref() == Some(id.as_str())
                        {
                            state.active_exec = None;
                            state.last_used = Instant::now();
                        }
                    }
                }
                KernelToHost::RunTool(req) => {
                    let Some(reset_cancel) =
                        JsReplManager::begin_exec_tool_call(&exec_tool_calls, &req.exec_id).await
                    else {
                        let exec_id = req.exec_id.clone();
                        let tool_call_id = req.id.clone();
                        let payload = HostToKernel::RunToolResult(RunToolResult {
                            id: req.id,
                            ok: false,
                            response: None,
                            error: Some("js_repl exec context not found".to_string()),
                        });
                        if let Err(err) = JsReplManager::write_message(&stdin, &payload).await {
                            let snapshot =
                                JsReplManager::kernel_debug_snapshot(&child, &recent_stderr).await;
                            warn!(
                                exec_id = %exec_id,
                                tool_call_id = %tool_call_id,
                                error = %err,
                                kernel_pid = ?snapshot.pid,
                                kernel_status = %snapshot.status,
                                kernel_stderr_tail = %snapshot.stderr_tail,
                                "failed to reply to kernel run_tool request"
                            );
                        }
                        continue;
                    };
                    let stdin_clone = Arc::clone(&stdin);
                    let exec_contexts = Arc::clone(&exec_contexts);
                    let exec_tool_calls_for_task = Arc::clone(&exec_tool_calls);
                    let recent_stderr = Arc::clone(&recent_stderr);
                    tokio::spawn(async move {
                        let exec_id = req.exec_id.clone();
                        let tool_call_id = req.id.clone();
                        let tool_name = req.tool_name.clone();
                        let context = { exec_contexts.lock().await.get(&exec_id).cloned() };
                        let result = match context {
                            Some(ctx) => {
                                tokio::select! {
                                    _ = reset_cancel.cancelled() => RunToolResult {
                                        id: tool_call_id.clone(),
                                        ok: false,
                                        response: None,
                                        error: Some("js_repl execution reset".to_string()),
                                    },
                                    result = JsReplManager::run_tool_request(ctx, req) => result,
                                }
                            }
                            None => RunToolResult {
                                id: tool_call_id.clone(),
                                ok: false,
                                response: None,
                                error: Some("js_repl exec context not found".to_string()),
                            },
                        };
                        JsReplManager::finish_exec_tool_call(&exec_tool_calls_for_task, &exec_id)
                            .await;
                        let payload = HostToKernel::RunToolResult(result);
                        if let Err(err) = JsReplManager::write_message(&stdin_clone, &payload).await
                        {
                            let stderr_tail =
                                JsReplManager::kernel_stderr_tail_snapshot(&recent_stderr).await;
                            warn!(
                                exec_id = %exec_id,
                                tool_call_id = %tool_call_id,
                                tool_name = %tool_name,
                                error = %err,
                                kernel_stderr_tail = %stderr_tail,
                                "failed to reply to kernel run_tool request"
                            );
                        }
                    });
                }
            }
        };

        let mut exec_ids_from_contexts = {
            let mut contexts = exec_contexts.lock().await;
            let ids = contexts.keys().cloned().collect::<Vec<_>>();
            contexts.clear();
            ids
        };
        for exec_id in &exec_ids_from_contexts {
            JsReplManager::cancel_exec_tool_calls_map(&exec_tool_calls, exec_id).await;
            JsReplManager::wait_for_exec_tool_calls_map(&exec_tool_calls, exec_id).await;
            JsReplManager::clear_exec_tool_calls_map(&exec_tool_calls, exec_id).await;
        }
        let unexpected_snapshot = if matches!(end_reason, KernelStreamEnd::Shutdown) {
            None
        } else {
            Some(Self::kernel_debug_snapshot(&child, &recent_stderr).await)
        };
        let kernel_failure_message = unexpected_snapshot.as_ref().map(|snapshot| {
            with_model_kernel_failure_message(
                "js_repl kernel exited unexpectedly",
                end_reason.reason(),
                end_reason.error(),
                snapshot,
            )
        });
        let kernel_exit_message = kernel_failure_message
            .clone()
            .unwrap_or_else(|| "js_repl kernel exited unexpectedly".to_string());

        let mut pending = pending_execs.lock().await;
        let pending_exec_ids = pending.keys().cloned().collect::<Vec<_>>();
        for (_id, tx) in pending.drain() {
            let _ = tx.send(ExecResultMessage::Err {
                message: kernel_exit_message.clone(),
            });
        }
        drop(pending);
        let mut affected_exec_ids: HashSet<String> = exec_ids_from_contexts.drain(..).collect();
        affected_exec_ids.extend(pending_exec_ids.iter().cloned());
        if let Some(poll_session_id) = poll_session_id.as_ref() {
            let removed_session = {
                let mut sessions = poll_sessions.lock().await;
                let should_remove = sessions
                    .get(poll_session_id)
                    .is_some_and(|state| Arc::ptr_eq(&state.kernel.child, &child));
                if should_remove {
                    sessions.remove(poll_session_id)
                } else {
                    None
                }
            };
            if let Some(state) = removed_session
                && let Some(active_exec) = state.active_exec
            {
                affected_exec_ids.insert(active_exec);
            }
        }
        for exec_id in &affected_exec_ids {
            exec_to_session.lock().await.remove(exec_id);
        }
        for exec_id in &affected_exec_ids {
            Self::complete_exec_in_store(
                &exec_store,
                exec_id,
                ExecTerminalKind::KernelExit,
                None,
                Some(kernel_exit_message.clone()),
                false,
            )
            .await;
        }
        let mut affected_exec_ids = affected_exec_ids.into_iter().collect::<Vec<_>>();
        affected_exec_ids.sort_unstable();

        if let Some(snapshot) = unexpected_snapshot {
            let mut pending_exec_ids = pending_exec_ids;
            pending_exec_ids.sort_unstable();
            warn!(
                reason = %end_reason.reason(),
                stream_error = %end_reason.error().unwrap_or(""),
                kernel_pid = ?snapshot.pid,
                kernel_status = %snapshot.status,
                pending_exec_count = pending_exec_ids.len(),
                pending_exec_ids = ?Self::truncate_id_list(&pending_exec_ids),
                affected_exec_count = affected_exec_ids.len(),
                affected_exec_ids = ?Self::truncate_id_list(&affected_exec_ids),
                kernel_stderr_tail = %snapshot.stderr_tail,
                "js_repl kernel terminated unexpectedly"
            );
        }
    }

    async fn run_tool_request(exec: ExecContext, req: RunToolRequest) -> RunToolResult {
        if is_js_repl_internal_tool(&req.tool_name) {
            return RunToolResult {
                id: req.id,
                ok: false,
                response: None,
                error: Some("js_repl cannot invoke itself".to_string()),
            };
        }

        let mcp_tools = exec
            .session
            .services
            .mcp_connection_manager
            .read()
            .await
            .list_all_tools()
            .await;

        let router = ToolRouter::from_config(
            &exec.turn.tools_config,
            Some(
                mcp_tools
                    .into_iter()
                    .map(|(name, tool)| (name, tool.tool))
                    .collect(),
            ),
            None,
            exec.turn.dynamic_tools.as_slice(),
        );

        let payload =
            if let Some((server, tool)) = exec.session.parse_mcp_tool_name(&req.tool_name).await {
                crate::tools::context::ToolPayload::Mcp {
                    server,
                    tool,
                    raw_arguments: req.arguments.clone(),
                }
            } else if is_freeform_tool(&router.specs(), &req.tool_name) {
                crate::tools::context::ToolPayload::Custom {
                    input: req.arguments.clone(),
                }
            } else {
                crate::tools::context::ToolPayload::Function {
                    arguments: req.arguments.clone(),
                }
            };

        let call = crate::tools::router::ToolCall {
            tool_name: req.tool_name,
            call_id: req.id.clone(),
            payload,
        };

        match router
            .dispatch_tool_call(
                exec.session,
                exec.turn,
                exec.tracker,
                call,
                crate::tools::router::ToolCallSource::JsRepl,
            )
            .await
        {
            Ok(response) => match serde_json::to_value(response) {
                Ok(value) => RunToolResult {
                    id: req.id,
                    ok: true,
                    response: Some(value),
                    error: None,
                },
                Err(err) => RunToolResult {
                    id: req.id,
                    ok: false,
                    response: None,
                    error: Some(format!("failed to serialize tool output: {err}")),
                },
            },
            Err(err) => RunToolResult {
                id: req.id,
                ok: false,
                response: None,
                error: Some(err.to_string()),
            },
        }
    }

    async fn read_stderr(
        stderr: tokio::process::ChildStderr,
        recent_stderr: Arc<Mutex<VecDeque<String>>>,
        shutdown: CancellationToken,
    ) {
        let mut reader = BufReader::new(stderr).lines();

        loop {
            let line = tokio::select! {
                _ = shutdown.cancelled() => break,
                res = reader.next_line() => match res {
                    Ok(Some(line)) => line,
                    Ok(None) => break,
                    Err(err) => {
                        warn!("js_repl kernel stderr ended: {err}");
                        break;
                    }
                },
            };
            let trimmed = line.trim();
            if !trimmed.is_empty() {
                let bounded_line = {
                    let mut tail = recent_stderr.lock().await;
                    push_stderr_tail_line(&mut tail, trimmed)
                };
                if bounded_line.is_empty() {
                    continue;
                }
                warn!("js_repl stderr: {bounded_line}");
            }
        }
    }
}

fn is_freeform_tool(specs: &[ToolSpec], name: &str) -> bool {
    specs
        .iter()
        .any(|spec| spec.name() == name && matches!(spec, ToolSpec::Freeform(_)))
}

fn is_js_repl_internal_tool(name: &str) -> bool {
    matches!(name, "js_repl" | "js_repl_poll" | "js_repl_reset")
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum KernelToHost {
    ExecStarted {
        id: String,
    },
    ExecLog {
        id: String,
        text: String,
    },
    ExecResult {
        id: String,
        ok: bool,
        output: String,
        #[serde(default)]
        error: Option<String>,
    },
    RunTool(RunToolRequest),
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
enum HostToKernel {
    Exec {
        id: String,
        code: String,
        #[serde(default)]
        timeout_ms: Option<u64>,
        #[serde(default)]
        stream_logs: bool,
    },
    RunToolResult(RunToolResult),
}

#[derive(Clone, Debug, Deserialize)]
struct RunToolRequest {
    id: String,
    exec_id: String,
    tool_name: String,
    arguments: String,
}

#[derive(Clone, Debug, Serialize)]
struct RunToolResult {
    id: String,
    ok: bool,
    #[serde(default)]
    response: Option<JsonValue>,
    #[serde(default)]
    error: Option<String>,
}

#[derive(Debug)]
enum ExecResultMessage {
    Ok { output: String },
    Err { message: String },
}

fn clamp_poll_ms(value: Option<u64>) -> u64 {
    value
        .unwrap_or(JS_REPL_POLL_DEFAULT_MS)
        .clamp(JS_REPL_POLL_MIN_MS, JS_REPL_POLL_MAX_MS)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct NodeVersion {
    major: u64,
    minor: u64,
    patch: u64,
}

impl fmt::Display for NodeVersion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)
    }
}

impl NodeVersion {
    fn parse(input: &str) -> Result<Self, String> {
        let trimmed = input.trim().trim_start_matches('v');
        let mut parts = trimmed.split(['.', '-', '+']);
        let major = parts
            .next()
            .ok_or_else(|| "missing major version".to_string())?
            .parse::<u64>()
            .map_err(|err| format!("invalid major version: {err}"))?;
        let minor = parts
            .next()
            .ok_or_else(|| "missing minor version".to_string())?
            .parse::<u64>()
            .map_err(|err| format!("invalid minor version: {err}"))?;
        let patch = parts
            .next()
            .ok_or_else(|| "missing patch version".to_string())?
            .parse::<u64>()
            .map_err(|err| format!("invalid patch version: {err}"))?;
        Ok(Self {
            major,
            minor,
            patch,
        })
    }
}

fn required_node_version() -> Result<NodeVersion, String> {
    NodeVersion::parse(JS_REPL_MIN_NODE_VERSION)
}

async fn read_node_version(node_path: &Path) -> Result<NodeVersion, String> {
    let output = tokio::process::Command::new(node_path)
        .arg("--version")
        .output()
        .await
        .map_err(|err| format!("failed to execute Node: {err}"))?;

    if !output.status.success() {
        let mut details = String::new();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = stdout.trim();
        let stderr = stderr.trim();
        if !stdout.is_empty() {
            details.push_str(" stdout: ");
            details.push_str(stdout);
        }
        if !stderr.is_empty() {
            details.push_str(" stderr: ");
            details.push_str(stderr);
        }
        let details = if details.is_empty() {
            String::new()
        } else {
            format!(" ({details})")
        };
        return Err(format!(
            "failed to read Node version (status {status}){details}",
            status = output.status
        ));
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stdout = stdout.trim();
    NodeVersion::parse(stdout)
        .map_err(|err| format!("failed to parse Node version output `{stdout}`: {err}"))
}

async fn ensure_node_version(node_path: &Path) -> Result<(), String> {
    let required = required_node_version()?;
    let found = read_node_version(node_path).await?;
    if found < required {
        return Err(format!(
            "Node runtime too old for js_repl (resolved {node_path}): found v{found}, requires >= v{required}. Install/update Node or set js_repl_node_path to a newer runtime.",
            node_path = node_path.display()
        ));
    }
    Ok(())
}

pub(crate) fn resolve_node(config_path: Option<&Path>) -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("CODEX_JS_REPL_NODE_PATH") {
        let p = PathBuf::from(path);
        if p.exists() {
            return Some(p);
        }
    }

    if let Some(path) = config_path
        && path.exists()
    {
        return Some(path.to_path_buf());
    }

    if let Ok(path) = which::which("node") {
        return Some(path);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocol::AskForApproval;
    use crate::protocol::EventMsg;
    use crate::protocol::SandboxPolicy;
    use crate::turn_diff_tracker::TurnDiffTracker;
    use codex_protocol::models::ContentItem;
    use codex_protocol::models::ResponseInputItem;
    use codex_protocol::openai_models::InputModality;
    #[cfg(target_os = "linux")]
    use ctor::ctor;
    use pretty_assertions::assert_eq;
    use std::fs;
    use std::path::Path;
    #[cfg(target_os = "linux")]
    use std::path::PathBuf;
    use tempfile::tempdir;

    #[cfg(target_os = "linux")]
    #[ctor]
    fn dispatch_codex_linux_sandbox_arg0_for_js_repl_tests() {
        let argv0 = std::env::args_os().next().unwrap_or_default();
        let argv0_path = PathBuf::from(argv0);
        let exe_name = argv0_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("");
        if exe_name == "codex-linux-sandbox" {
            // In sandbox subprocesses, route directly to the linux sandbox entrypoint.
            let _ = codex_arg0::arg0_dispatch();
        }
    }

    fn configure_js_repl_test_sandbox(turn: &mut crate::codex::TurnContext) {
        turn.sandbox_policy = SandboxPolicy::new_workspace_write_policy();
        #[cfg(target_os = "linux")]
        {
            turn.codex_linux_sandbox_exe =
                Some(std::env::current_exe().expect("test harness path should resolve on Linux"));
        }
    }

    async fn make_session_and_context() -> (crate::codex::Session, crate::codex::TurnContext) {
        let (session, mut turn) = crate::codex::make_session_and_context().await;
        configure_js_repl_test_sandbox(&mut turn);
        (session, turn)
    }

    #[test]
    fn node_version_parses_v_prefix_and_suffix() {
        let version = NodeVersion::parse("v25.1.0-nightly.2024").unwrap();
        assert_eq!(
            version,
            NodeVersion {
                major: 25,
                minor: 1,
                patch: 0,
            }
        );
    }

    #[test]
    fn truncate_utf8_prefix_by_bytes_preserves_character_boundaries() {
        let input = "aé🙂z";
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 0), "");
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 1), "a");
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 2), "a");
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 3), "aé");
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 6), "aé");
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 7), "aé🙂");
        assert_eq!(truncate_utf8_prefix_by_bytes(input, 8), "aé🙂z");
    }

    #[test]
    fn split_utf8_chunks_with_limits_respects_boundaries_and_limits() {
        let chunks = split_utf8_chunks_with_limits("éé🙂z", 3, 2);
        assert_eq!(chunks.len(), 2);
        assert_eq!(std::str::from_utf8(&chunks[0]).unwrap(), "é");
        assert_eq!(std::str::from_utf8(&chunks[1]).unwrap(), "é");
    }

    #[tokio::test]
    async fn exec_buffer_output_deltas_honor_remaining_budget() {
        let (session, turn) = make_session_and_context().await;
        let mut entry = ExecBuffer::new(
            "call-1".to_string(),
            None,
            Arc::new(session),
            Arc::new(turn),
        );
        entry.emitted_deltas = MAX_EXEC_OUTPUT_DELTAS_PER_CALL - 1;

        let first = entry.output_delta_chunks_for_log_line("hello");
        assert_eq!(first.len(), 1);
        assert_eq!(String::from_utf8(first[0].clone()).unwrap(), "hello\n");

        let second = entry.output_delta_chunks_for_log_line("world");
        assert!(second.is_empty());
    }

    #[test]
    fn stderr_tail_applies_line_and_byte_limits() {
        let mut lines = VecDeque::new();
        let per_line_cap = JS_REPL_STDERR_TAIL_LINE_MAX_BYTES.min(JS_REPL_STDERR_TAIL_MAX_BYTES);
        let long = "x".repeat(per_line_cap + 128);
        let bounded = push_stderr_tail_line(&mut lines, &long);
        assert_eq!(bounded.len(), per_line_cap);

        for i in 0..50 {
            let line = format!("line-{i}-{}", "y".repeat(200));
            push_stderr_tail_line(&mut lines, &line);
        }

        assert!(lines.len() <= JS_REPL_STDERR_TAIL_LINE_LIMIT);
        assert!(lines.iter().all(|line| line.len() <= per_line_cap));
        assert!(stderr_tail_formatted_bytes(&lines) <= JS_REPL_STDERR_TAIL_MAX_BYTES);
        assert_eq!(
            format_stderr_tail(&lines).len(),
            stderr_tail_formatted_bytes(&lines)
        );
    }

    #[test]
    fn model_kernel_failure_details_are_structured_and_truncated() {
        let snapshot = KernelDebugSnapshot {
            pid: Some(42),
            status: "exited(code=1)".to_string(),
            stderr_tail: "s".repeat(JS_REPL_MODEL_DIAG_STDERR_MAX_BYTES + 400),
        };
        let stream_error = "e".repeat(JS_REPL_MODEL_DIAG_ERROR_MAX_BYTES + 200);
        let message = with_model_kernel_failure_message(
            "js_repl kernel exited unexpectedly",
            "stdout_eof",
            Some(&stream_error),
            &snapshot,
        );
        assert!(message.starts_with("js_repl kernel exited unexpectedly\n\njs_repl diagnostics: "));
        let (_prefix, encoded) = message
            .split_once("js_repl diagnostics: ")
            .expect("diagnostics suffix should be present");
        let parsed: serde_json::Value =
            serde_json::from_str(encoded).expect("diagnostics should be valid json");
        assert_eq!(
            parsed.get("reason").and_then(|v| v.as_str()),
            Some("stdout_eof")
        );
        assert_eq!(
            parsed.get("kernel_pid").and_then(serde_json::Value::as_u64),
            Some(42)
        );
        assert_eq!(
            parsed.get("kernel_status").and_then(|v| v.as_str()),
            Some("exited(code=1)")
        );
        assert!(
            parsed
                .get("kernel_stderr_tail")
                .and_then(|v| v.as_str())
                .expect("kernel_stderr_tail should be present")
                .len()
                <= JS_REPL_MODEL_DIAG_STDERR_MAX_BYTES
        );
        assert!(
            parsed
                .get("stream_error")
                .and_then(|v| v.as_str())
                .expect("stream_error should be present")
                .len()
                <= JS_REPL_MODEL_DIAG_ERROR_MAX_BYTES
        );
    }

    #[test]
    fn write_error_diagnostics_only_attach_for_likely_kernel_failures() {
        let running = KernelDebugSnapshot {
            pid: Some(7),
            status: "running".to_string(),
            stderr_tail: "<empty>".to_string(),
        };
        let exited = KernelDebugSnapshot {
            pid: Some(7),
            status: "exited(code=1)".to_string(),
            stderr_tail: "<empty>".to_string(),
        };
        assert!(!should_include_model_diagnostics_for_write_error(
            "failed to flush kernel message: other io error",
            &running
        ));
        assert!(should_include_model_diagnostics_for_write_error(
            "failed to write to kernel: Broken pipe (os error 32)",
            &running
        ));
        assert!(should_include_model_diagnostics_for_write_error(
            "failed to write to kernel: some other io error",
            &exited
        ));
    }

    #[test]
    fn js_repl_internal_tool_guard_matches_expected_names() {
        assert!(is_js_repl_internal_tool("js_repl"));
        assert!(is_js_repl_internal_tool("js_repl_poll"));
        assert!(is_js_repl_internal_tool("js_repl_reset"));
        assert!(!is_js_repl_internal_tool("shell_command"));
        assert!(!is_js_repl_internal_tool("list_mcp_resources"));
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn wait_for_exec_tool_calls_map_drains_inflight_calls_without_hanging() {
        let exec_tool_calls = Arc::new(Mutex::new(HashMap::new()));

        for _ in 0..128 {
            let exec_id = Uuid::new_v4().to_string();
            exec_tool_calls
                .lock()
                .await
                .insert(exec_id.clone(), ExecToolCalls::default());
            assert!(
                JsReplManager::begin_exec_tool_call(&exec_tool_calls, &exec_id)
                    .await
                    .is_some()
            );

            let wait_map = Arc::clone(&exec_tool_calls);
            let wait_exec_id = exec_id.clone();
            let waiter = tokio::spawn(async move {
                JsReplManager::wait_for_exec_tool_calls_map(&wait_map, &wait_exec_id).await;
            });

            let finish_map = Arc::clone(&exec_tool_calls);
            let finish_exec_id = exec_id.clone();
            let finisher = tokio::spawn(async move {
                tokio::task::yield_now().await;
                JsReplManager::finish_exec_tool_call(&finish_map, &finish_exec_id).await;
            });

            tokio::time::timeout(Duration::from_secs(1), waiter)
                .await
                .expect("wait_for_exec_tool_calls_map should not hang")
                .expect("wait task should not panic");
            finisher.await.expect("finish task should not panic");

            JsReplManager::clear_exec_tool_calls_map(&exec_tool_calls, &exec_id).await;
        }
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn reset_waits_for_exec_lock_before_clearing_exec_tool_calls() {
        let manager = JsReplManager::new(None, Vec::new())
            .await
            .expect("manager should initialize");
        let permit = manager
            .exec_lock
            .clone()
            .acquire_owned()
            .await
            .expect("lock should be acquirable");
        let exec_id = Uuid::new_v4().to_string();
        manager.register_exec_tool_calls(&exec_id).await;

        let reset_manager = Arc::clone(&manager);
        let mut reset_task = tokio::spawn(async move { reset_manager.reset().await });
        tokio::time::sleep(Duration::from_millis(50)).await;

        assert!(
            !reset_task.is_finished(),
            "reset should wait until execute lock is released"
        );
        assert!(
            manager.exec_tool_calls.lock().await.contains_key(&exec_id),
            "reset must not clear tool-call contexts while execute lock is held"
        );

        drop(permit);

        tokio::time::timeout(Duration::from_secs(1), &mut reset_task)
            .await
            .expect("reset should complete after execute lock release")
            .expect("reset task should not panic")
            .expect("reset should succeed");
        assert!(
            !manager.exec_tool_calls.lock().await.contains_key(&exec_id),
            "reset should clear tool-call contexts after lock acquisition"
        );
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn reset_clears_inflight_exec_tool_calls_without_waiting() {
        let manager = JsReplManager::new(None, Vec::new())
            .await
            .expect("manager should initialize");
        let exec_id = Uuid::new_v4().to_string();
        manager.register_exec_tool_calls(&exec_id).await;
        assert!(
            JsReplManager::begin_exec_tool_call(&manager.exec_tool_calls, &exec_id)
                .await
                .is_some()
        );

        let wait_manager = Arc::clone(&manager);
        let wait_exec_id = exec_id.clone();
        let waiter = tokio::spawn(async move {
            wait_manager.wait_for_exec_tool_calls(&wait_exec_id).await;
        });
        tokio::task::yield_now().await;

        tokio::time::timeout(Duration::from_secs(1), manager.reset())
            .await
            .expect("reset should not hang")
            .expect("reset should succeed");

        tokio::time::timeout(Duration::from_secs(1), waiter)
            .await
            .expect("waiter should be released")
            .expect("wait task should not panic");

        assert!(manager.exec_tool_calls.lock().await.is_empty());
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn reset_aborts_inflight_exec_tool_tasks() {
        let manager = JsReplManager::new(None, Vec::new())
            .await
            .expect("manager should initialize");
        let exec_id = Uuid::new_v4().to_string();
        manager.register_exec_tool_calls(&exec_id).await;
        let reset_cancel = JsReplManager::begin_exec_tool_call(&manager.exec_tool_calls, &exec_id)
            .await
            .expect("exec should be registered");

        let task = tokio::spawn(async move {
            tokio::select! {
                _ = reset_cancel.cancelled() => "cancelled",
                _ = tokio::time::sleep(Duration::from_secs(60)) => "timed_out",
            }
        });

        tokio::time::timeout(Duration::from_secs(1), manager.reset())
            .await
            .expect("reset should not hang")
            .expect("reset should succeed");

        let outcome = tokio::time::timeout(Duration::from_secs(1), task)
            .await
            .expect("cancelled task should resolve promptly")
            .expect("task should not panic");
        assert_eq!(outcome, "cancelled");
    }
    #[tokio::test]
    async fn exec_buffer_caps_all_logs_by_bytes() {
        let (session, turn) = make_session_and_context().await;
        let mut entry = ExecBuffer::new(
            "call-1".to_string(),
            None,
            Arc::new(session),
            Arc::new(turn),
        );
        let chunk = "x".repeat(16 * 1024);
        for _ in 0..96 {
            entry.push_log(chunk.clone());
        }
        assert!(entry.all_logs_truncated);
        assert!(entry.all_logs_bytes <= JS_REPL_POLL_ALL_LOGS_MAX_BYTES);
        assert!(
            entry
                .all_logs
                .last()
                .is_some_and(|line| line.contains("logs truncated"))
        );
    }

    #[tokio::test]
    async fn exec_buffer_log_marker_keeps_newest_logs() {
        let (session, turn) = make_session_and_context().await;
        let mut entry = ExecBuffer::new(
            "call-1".to_string(),
            None,
            Arc::new(session),
            Arc::new(turn),
        );
        let filler = "x".repeat(8 * 1024);
        for i in 0..20 {
            entry.push_log(format!("id{i}:{filler}"));
        }

        let drained = entry.poll_logs();
        assert_eq!(
            drained.first().map(String::as_str),
            Some(JS_REPL_POLL_LOGS_TRUNCATED_MARKER)
        );
        assert!(drained.iter().any(|line| line.starts_with("id19:")));
        assert!(!drained.iter().any(|line| line.starts_with("id0:")));
    }

    #[tokio::test]
    async fn complete_exec_in_store_suppresses_kernel_exit_when_host_terminating() {
        let (session, turn) = make_session_and_context().await;
        let exec_id = "exec-1";
        let exec_store = Arc::new(tokio::sync::Mutex::new(HashMap::new()));

        let mut entry = ExecBuffer::new(
            "call-1".to_string(),
            None,
            Arc::new(session),
            Arc::new(turn),
        );
        entry.host_terminating = true;
        exec_store.lock().await.insert(exec_id.to_string(), entry);

        let kernel_exit_completed = JsReplManager::complete_exec_in_store(
            &exec_store,
            exec_id,
            ExecTerminalKind::KernelExit,
            None,
            Some("js_repl kernel exited unexpectedly".to_string()),
            false,
        )
        .await;
        assert!(!kernel_exit_completed);

        {
            let store = exec_store.lock().await;
            let entry = store.get(exec_id).expect("exec entry should exist");
            assert!(!entry.done);
            assert!(entry.terminal_kind.is_none());
            assert!(entry.error.is_none());
            assert!(entry.host_terminating);
        }

        let cancelled_completed = JsReplManager::complete_exec_in_store(
            &exec_store,
            exec_id,
            ExecTerminalKind::Cancelled,
            None,
            Some(JS_REPL_CANCEL_ERROR_MESSAGE.to_string()),
            false,
        )
        .await;
        assert!(cancelled_completed);

        let store = exec_store.lock().await;
        let entry = store.get(exec_id).expect("exec entry should exist");
        assert!(entry.done);
        assert_eq!(entry.terminal_kind, Some(ExecTerminalKind::Cancelled));
        assert_eq!(entry.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));
        assert!(!entry.host_terminating);
    }

    #[test]
    fn build_js_repl_exec_output_sets_timed_out() {
        let out = build_js_repl_exec_output("", Some("timeout"), Duration::from_millis(50), true);
        assert!(out.timed_out);
    }
    fn write_js_repl_test_package(base: &Path, name: &str, value: &str) -> anyhow::Result<()> {
        let pkg_dir = base.join("node_modules").join(name);
        fs::create_dir_all(&pkg_dir)?;
        fs::write(
            pkg_dir.join("package.json"),
            format!(
                "{{\n  \"name\": \"{name}\",\n  \"version\": \"1.0.0\",\n  \"type\": \"module\",\n  \"exports\": {{\n    \"import\": \"./index.js\"\n  }}\n}}\n"
            ),
        )?;
        fs::write(
            pkg_dir.join("index.js"),
            format!("export const value = \"{value}\";\n"),
        )?;
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_persists_top_level_bindings_and_supports_tla() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let first = manager
            .execute(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                JsReplArgs {
                    code: "let x = await Promise.resolve(41); console.log(x);".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(first.output.contains("41"));

        let second = manager
            .execute(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                JsReplArgs {
                    code: "console.log(x + 1);".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;

        assert!(second.output.contains("42"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_timeout_does_not_deadlock() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = tokio::time::timeout(
            Duration::from_secs(3),
            manager.execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "while (true) {}".to_string(),
                    timeout_ms: Some(50),
                    poll: false,
                    session_id: None,
                },
            ),
        )
        .await
        .expect("execute should return, not deadlock")
        .expect_err("expected timeout error");

        assert_eq!(
            result.to_string(),
            "js_repl execution timed out; kernel reset, rerun your request"
        );
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_timeout_kills_kernel_process() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        manager
            .execute(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                JsReplArgs {
                    code: "console.log('warmup');".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;

        let child = {
            let guard = manager.kernel.lock().await;
            let state = guard.as_ref().expect("kernel should exist after warmup");
            Arc::clone(&state.child)
        };

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "while (true) {}".to_string(),
                    timeout_ms: Some(50),
                    poll: false,
                    session_id: None,
                },
            )
            .await
            .expect_err("expected timeout error");

        assert_eq!(
            result.to_string(),
            "js_repl execution timed out; kernel reset, rerun your request"
        );

        let exit_state = {
            let mut child = child.lock().await;
            child.try_wait()?
        };
        assert!(
            exit_state.is_some(),
            "timed out js_repl execution should kill previous kernel process"
        );
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_kernel_failure_includes_model_diagnostics() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        manager
            .execute(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                JsReplArgs {
                    code: "console.log('warmup');".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;

        let child = {
            let guard = manager.kernel.lock().await;
            let state = guard.as_ref().expect("kernel should exist after warmup");
            Arc::clone(&state.child)
        };
        JsReplManager::kill_kernel_child(&child, "test_crash").await;
        tokio::time::sleep(Duration::from_millis(50)).await;

        let err = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "console.log('after-kill');".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await
            .expect_err("expected kernel failure after forced kill");

        let message = err.to_string();
        assert!(message.contains("js_repl diagnostics:"));
        assert!(message.contains("\"reason\":\"write_failed\""));
        assert!(message.contains("\"kernel_status\":\"exited("));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_can_call_tools() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let shell = manager
            .execute(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                JsReplArgs {
                    code: "const shellOut = await codex.tool(\"shell_command\", { command: \"printf js_repl_shell_ok\" }); console.log(JSON.stringify(shellOut));".to_string(),
                    timeout_ms: Some(15_000),
                    poll: false,
                session_id: None,
                },
            )
            .await?;
        assert!(shell.output.contains("js_repl_shell_ok"));

        let tool = manager
            .execute(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                JsReplArgs {
                    code: "const toolOut = await codex.tool(\"list_mcp_resources\", {}); console.log(toolOut.type);".to_string(),
                    timeout_ms: Some(15_000),
                    poll: false,
                session_id: None,
                },
            )
            .await?;
        assert!(tool.output.contains("function_call_output"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_tool_call_rejects_recursive_js_repl_invocation() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: r#"
try {
  await codex.tool("js_repl", "console.log('recursive')");
  console.log("unexpected-success");
} catch (err) {
  console.log(String(err));
}
"#
                    .to_string(),
                    timeout_ms: Some(15_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;

        assert!(
            result.output.contains("js_repl cannot invoke itself"),
            "expected recursion guard message, got output: {}",
            result.output
        );
        assert!(
            !result.output.contains("unexpected-success"),
            "recursive js_repl tool call unexpectedly succeeded: {}",
            result.output
        );
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_waits_for_unawaited_tool_calls_before_completion() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let marker = turn
            .cwd
            .join(format!("js-repl-unawaited-marker-{}.txt", Uuid::new_v4()));
        let marker_json = serde_json::to_string(&marker.to_string_lossy().to_string())?;
        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: format!(
                        r#"
const marker = {marker_json};
void codex.tool("shell_command", {{ command: `sleep 0.35; printf js_repl_unawaited_done > "${{marker}}"` }});
console.log("cell-complete");
"#
                    ),
                    timeout_ms: Some(10_000),
                    poll: false,
                session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("cell-complete"));
        let marker_contents = tokio::fs::read_to_string(&marker).await?;
        assert_eq!(marker_contents, "js_repl_unawaited_done");
        let _ = tokio::fs::remove_file(&marker).await;
        Ok(())
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn js_repl_can_attach_image_via_view_image_tool() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        if !turn
            .model_info
            .input_modalities
            .contains(&InputModality::Image)
        {
            return Ok(());
        }
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        *session.active_turn.lock().await = Some(crate::state::ActiveTurn::default());

        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;
        let code = r#"
const fs = await import("node:fs/promises");
const path = await import("node:path");
const imagePath = path.join(codex.tmpDir, "js-repl-view-image.png");
const png = Buffer.from(
  "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGP4z8DwHwAFAAH/iZk9HQAAAABJRU5ErkJggg==",
  "base64"
);
await fs.writeFile(imagePath, png);
const out = await codex.tool("view_image", { path: imagePath });
console.log(out.type);
console.log(out.output?.body?.text ?? "");
"#;

        let result = manager
            .execute(
                Arc::clone(&session),
                turn,
                tracker,
                JsReplArgs {
                    code: code.to_string(),
                    timeout_ms: Some(15_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("function_call_output"));

        let pending_input = session.get_pending_input().await;
        let image_url = pending_input
            .iter()
            .find_map(|item| match item {
                ResponseInputItem::Message { content, .. } => {
                    content.iter().find_map(|content_item| match content_item {
                        ContentItem::InputImage { image_url } => Some(image_url.as_str()),
                        _ => None,
                    })
                }
                _ => None,
            })
            .expect("view_image should inject an input_image message for the active turn");
        assert!(image_url.starts_with("data:image/png;base64,"));

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_does_not_expose_process_global() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "console.log(typeof process);".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("undefined"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_blocks_sensitive_builtin_imports() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let err = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "await import(\"node:process\");".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await
            .expect_err("node:process import should be blocked");
        assert!(
            err.to_string()
                .contains("Importing module \"node:process\" is not allowed in js_repl")
        );
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_prefers_env_node_module_dirs_over_config() -> anyhow::Result<()> {
        let env_base = tempdir()?;
        write_js_repl_test_package(env_base.path(), "repl_probe", "env")?;

        let config_base = tempdir()?;
        let cwd_dir = tempdir()?;

        let (session, mut turn) = make_session_and_context().await;
        turn.shell_environment_policy.r#set.insert(
            "CODEX_JS_REPL_NODE_MODULE_DIRS".to_string(),
            env_base.path().to_string_lossy().to_string(),
        );
        turn.cwd = cwd_dir.path().to_path_buf();
        turn.js_repl = Arc::new(JsReplHandle::with_node_path(
            turn.config.js_repl_node_path.clone(),
            vec![config_base.path().to_path_buf()],
        ));

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "const mod = await import(\"repl_probe\"); console.log(mod.value);"
                        .to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("env"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_submit_and_complete() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-1".to_string(),
                JsReplArgs {
                    code: "console.log('poll-ok');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;
        assert!(!submission.session_id.is_empty());

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            assert_eq!(result.session_id, submission.session_id);
            if result.done {
                let output = result.output.unwrap_or_default();
                assert!(output.contains("poll-ok"));
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for js_repl poll completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_session_reuse_preserves_state() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let first = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                "call-session-first".to_string(),
                JsReplArgs {
                    code: "let persisted = 41;".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;
        loop {
            let result = manager.poll(&first.exec_id, Some(200)).await?;
            if result.done {
                break;
            }
        }

        let second = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-session-second".to_string(),
                JsReplArgs {
                    code: "console.log(persisted + 1);".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: Some(first.session_id.clone()),
                },
            )
            .await?;
        assert_eq!(second.session_id, first.session_id);

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&second.exec_id, Some(200)).await?;
            if result.done {
                let output = result.output.unwrap_or_default();
                assert!(output.contains("42"));
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for reused polling session completion");
            }
        }

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_rejects_submit_with_unknown_session_id() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;
        let err = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-session-missing".to_string(),
                JsReplArgs {
                    code: "console.log('should not run');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: Some("missing-session".to_string()),
                },
            )
            .await
            .expect_err("expected missing session submit rejection");
        assert_eq!(err.to_string(), "js_repl session id not found");

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_rejects_timeout_ms_on_submit() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;
        let err = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-session-timeout-unsupported".to_string(),
                JsReplArgs {
                    code: "console.log('should not run');".to_string(),
                    timeout_ms: Some(5_000),
                    poll: true,
                    session_id: None,
                },
            )
            .await
            .expect_err("expected timeout_ms polling submit rejection");
        assert_eq!(err.to_string(), JS_REPL_POLL_TIMEOUT_ARG_ERROR_MESSAGE);

        Ok(())
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn js_repl_poll_concurrent_submit_same_session_rejects_second_exec() -> anyhow::Result<()>
    {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;
        let seed_submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-concurrent-seed".to_string(),
                JsReplArgs {
                    code: "console.log('seed');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;
        loop {
            let result = manager.poll(&seed_submission.exec_id, Some(200)).await?;
            if result.done {
                break;
            }
        }
        let shared_session_id = seed_submission.session_id.clone();

        let manager_a = Arc::clone(&manager);
        let session_a = Arc::clone(&session);
        let turn_a = Arc::clone(&turn);
        let shared_session_id_a = shared_session_id.clone();
        let submit_a = tokio::spawn(async move {
            Arc::clone(&manager_a)
                .submit(
                    Arc::clone(&session_a),
                    Arc::clone(&turn_a),
                    Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                    "call-concurrent-a".to_string(),
                    JsReplArgs {
                        code: "await new Promise((resolve) => setTimeout(resolve, 500));"
                            .to_string(),
                        timeout_ms: None,
                        poll: true,
                        session_id: Some(shared_session_id_a),
                    },
                )
                .await
        });

        let manager_b = Arc::clone(&manager);
        let session_b = Arc::clone(&session);
        let turn_b = Arc::clone(&turn);
        let shared_session_id_b = shared_session_id.clone();
        let submit_b = tokio::spawn(async move {
            Arc::clone(&manager_b)
                .submit(
                    Arc::clone(&session_b),
                    Arc::clone(&turn_b),
                    Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                    "call-concurrent-b".to_string(),
                    JsReplArgs {
                        code: "console.log('blocked');".to_string(),
                        timeout_ms: None,
                        poll: true,
                        session_id: Some(shared_session_id_b),
                    },
                )
                .await
        });

        let (result_a, result_b) = tokio::join!(submit_a, submit_b);
        let result_a = result_a.expect("task A should not panic");
        let result_b = result_b.expect("task B should not panic");
        let mut outcomes = vec![result_a, result_b];

        let first_error_index = outcomes.iter().position(Result::is_err);
        let Some(error_index) = first_error_index else {
            panic!("expected one submit to fail due to active exec in shared session");
        };
        assert_eq!(
            outcomes.iter().filter(|result| result.is_ok()).count(),
            1,
            "exactly one submit should succeed for a shared session id",
        );
        let err = outcomes
            .swap_remove(error_index)
            .expect_err("expected submit failure");
        assert!(
            err.to_string().contains("already has a running exec"),
            "unexpected concurrent-submit error: {err}",
        );
        let submission = outcomes
            .pop()
            .expect("one submission should remain")
            .expect("remaining submission should succeed");
        assert_eq!(submission.session_id, shared_session_id);

        let deadline = Instant::now() + Duration::from_secs(6);
        loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            if result.done {
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for shared-session winner completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
        let _ = manager.reset_session(&shared_session_id).await;

        Ok(())
    }

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn js_repl_poll_submit_enforces_capacity_during_concurrent_inserts() -> anyhow::Result<()>
    {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;
        let template_kernel = manager
            .start_kernel(Arc::clone(&turn), Some(session.conversation_id), None)
            .await
            .map_err(anyhow::Error::msg)?;

        let submit_a;
        let submit_b;
        {
            let mut sessions = manager.poll_sessions.lock().await;
            for idx in 0..(JS_REPL_POLL_MAX_SESSIONS - 1) {
                sessions.insert(
                    format!("prefill-{idx}"),
                    PollSessionState {
                        kernel: template_kernel.clone(),
                        active_exec: Some(format!("busy-{idx}")),
                        last_used: Instant::now(),
                    },
                );
            }

            let manager_a = Arc::clone(&manager);
            let session_a = Arc::clone(&session);
            let turn_a = Arc::clone(&turn);
            submit_a = tokio::spawn(async move {
                Arc::clone(&manager_a)
                    .submit(
                        Arc::clone(&session_a),
                        Arc::clone(&turn_a),
                        Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                        "call-capacity-a".to_string(),
                        JsReplArgs {
                            code: "await new Promise((resolve) => setTimeout(resolve, 300));"
                                .to_string(),
                            timeout_ms: None,
                            poll: true,
                            session_id: None,
                        },
                    )
                    .await
            });

            let manager_b = Arc::clone(&manager);
            let session_b = Arc::clone(&session);
            let turn_b = Arc::clone(&turn);
            submit_b = tokio::spawn(async move {
                Arc::clone(&manager_b)
                    .submit(
                        Arc::clone(&session_b),
                        Arc::clone(&turn_b),
                        Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                        "call-capacity-b".to_string(),
                        JsReplArgs {
                            code: "await new Promise((resolve) => setTimeout(resolve, 300));"
                                .to_string(),
                            timeout_ms: None,
                            poll: true,
                            session_id: None,
                        },
                    )
                    .await
            });

            tokio::task::yield_now().await;
        }

        let (result_a, result_b) = tokio::join!(submit_a, submit_b);
        let result_a = result_a.expect("task A should not panic");
        let result_b = result_b.expect("task B should not panic");
        let outcomes = vec![result_a, result_b];
        assert_eq!(
            outcomes.iter().filter(|result| result.is_ok()).count(),
            1,
            "exactly one concurrent submit should succeed when one slot remains",
        );
        assert_eq!(
            outcomes.iter().filter(|result| result.is_err()).count(),
            1,
            "exactly one concurrent submit should fail when one slot remains",
        );
        let err = outcomes
            .iter()
            .find_map(|result| result.as_ref().err())
            .expect("one submission should fail");
        assert!(
            err.to_string()
                .contains("has reached the maximum of 16 active sessions"),
            "unexpected capacity error: {err}",
        );
        assert!(
            manager.poll_sessions.lock().await.len() <= JS_REPL_POLL_MAX_SESSIONS,
            "poll session map must never exceed configured capacity",
        );

        manager.reset().await?;
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_rejects_submit_when_session_has_active_exec() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-session-active".to_string(),
                JsReplArgs {
                    code: "await new Promise((resolve) => setTimeout(resolve, 10_000));"
                        .to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let err = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-session-active-conflict".to_string(),
                JsReplArgs {
                    code: "console.log('should not run');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: Some(submission.session_id.clone()),
                },
            )
            .await
            .expect_err("expected active session submit rejection");
        assert_eq!(
            err.to_string(),
            format!(
                "js_repl session `{}` already has a running exec: `{}`",
                submission.session_id, submission.exec_id
            )
        );

        manager.reset_session(&submission.session_id).await?;
        let done = manager.poll(&submission.exec_id, Some(200)).await?;
        assert!(done.done);

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_emits_exec_output_delta_events() -> anyhow::Result<()> {
        let (session, mut turn, rx) = crate::codex::make_session_and_context_with_rx().await;
        let turn_mut = Arc::get_mut(&mut turn).expect("turn context should be uniquely owned");
        configure_js_repl_test_sandbox(turn_mut);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-delta-stream".to_string(),
                JsReplArgs {
                    code: "console.log('delta-one'); console.log('delta-two');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let deadline = Instant::now() + Duration::from_secs(5);
        let mut saw_one = false;
        let mut saw_two = false;
        loop {
            if saw_one && saw_two {
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for js_repl output delta events");
            }
            if let Ok(Ok(event)) = tokio::time::timeout(Duration::from_millis(200), rx.recv()).await
                && let EventMsg::ExecCommandOutputDelta(delta) = event.msg
                && delta.call_id == "call-delta-stream"
            {
                let text = String::from_utf8_lossy(&delta.chunk);
                if text.contains("delta-one") {
                    saw_one = true;
                }
                if text.contains("delta-two") {
                    saw_two = true;
                }
            }
            let result = manager.poll(&submission.exec_id, Some(50)).await?;
            if result.done && saw_one && saw_two {
                break;
            }
        }

        let completion_deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&submission.exec_id, Some(100)).await?;
            if result.done {
                break;
            }
            if Instant::now() >= completion_deadline {
                panic!("timed out waiting for js_repl poll completion");
            }
        }

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_submit_supports_parallel_execs() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let slow_submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::clone(&tracker),
                "call-slow".to_string(),
                JsReplArgs {
                    code: "await new Promise((resolve) => setTimeout(resolve, 2000)); console.log('slow-done');".to_string(),
                    timeout_ms: None,
                    poll: true,
                session_id: None,
                },
            )
            .await?;

        let fast_submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-fast".to_string(),
                JsReplArgs {
                    code: "console.log('fast-done');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;
        assert_ne!(slow_submission.session_id, fast_submission.session_id);

        let fast_start = Instant::now();
        let fast_output = loop {
            let result = manager.poll(&fast_submission.exec_id, Some(200)).await?;
            if result.done {
                break result.output.unwrap_or_default();
            }
            if fast_start.elapsed() > Duration::from_millis(1_500) {
                panic!("fast polled exec did not complete quickly; submit appears serialized");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        };
        assert!(fast_output.contains("fast-done"));

        let slow_deadline = Instant::now() + Duration::from_secs(8);
        loop {
            let result = manager.poll(&slow_submission.exec_id, Some(200)).await?;
            if result.done {
                let output = result.output.unwrap_or_default();
                assert!(output.contains("slow-done"));
                break;
            }
            if Instant::now() >= slow_deadline {
                panic!("timed out waiting for slow polled exec completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_completed_exec_is_replayable() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-replay".to_string(),
                JsReplArgs {
                    code: "console.log('replay-ok');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let deadline = Instant::now() + Duration::from_secs(5);
        let first_result = loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            if result.done {
                break result;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for js_repl poll completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        };
        assert!(
            first_result
                .output
                .as_deref()
                .is_some_and(|output| output.contains("replay-ok"))
        );
        assert_eq!(first_result.session_id, submission.session_id);

        let second_result = manager.poll(&submission.exec_id, Some(50)).await?;
        assert!(second_result.done);
        assert_eq!(second_result.session_id, submission.session_id);
        assert!(
            second_result
                .output
                .as_deref()
                .is_some_and(|output| output.contains("replay-ok"))
        );

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_timeout_resnapshots_state_before_returning() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let exec_id = format!("exec-missed-notify-{}", Uuid::new_v4());
        let poll_session_id = format!("session-missed-notify-{}", Uuid::new_v4());
        manager.exec_store.lock().await.insert(
            exec_id.clone(),
            ExecBuffer::new(
                "call-missed-notify".to_string(),
                Some(poll_session_id.clone()),
                Arc::clone(&session),
                Arc::clone(&turn),
            ),
        );

        let manager_for_poll = Arc::clone(&manager);
        let exec_id_for_poll = exec_id.clone();
        let poll_task =
            tokio::spawn(async move { manager_for_poll.poll(&exec_id_for_poll, Some(80)).await });

        tokio::time::sleep(Duration::from_millis(20)).await;
        {
            let mut store = manager.exec_store.lock().await;
            let entry = store
                .get_mut(&exec_id)
                .expect("exec entry should exist while polling");
            entry.push_log("late log".to_string());
            entry.output = Some("late log".to_string());
            entry.done = true;
            // Intentionally skip notify_waiters to emulate a missed wake window.
        }

        let result = poll_task
            .await
            .expect("poll task should not panic")
            .expect("poll should succeed");
        assert!(result.done);
        assert_eq!(result.session_id, poll_session_id);
        assert_eq!(result.logs, vec!["late log".to_string()]);
        assert_eq!(result.output.as_deref(), Some("late log"));

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_reset_session_succeeds_for_idle_session() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-reset-idle".to_string(),
                JsReplArgs {
                    code: "console.log('idle');".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            if result.done {
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for js_repl poll completion");
            }
        }

        manager.reset_session(&submission.session_id).await?;
        let err = manager
            .reset_session(&submission.session_id)
            .await
            .expect_err("expected missing session id after reset");
        assert_eq!(err.to_string(), "js_repl session id not found");

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_resolves_from_first_config_dir() -> anyhow::Result<()> {
        let first_base = tempdir()?;
        let second_base = tempdir()?;
        write_js_repl_test_package(first_base.path(), "repl_probe", "first")?;
        write_js_repl_test_package(second_base.path(), "repl_probe", "second")?;

        let cwd_dir = tempdir()?;

        let (session, mut turn) = make_session_and_context().await;
        turn.shell_environment_policy
            .r#set
            .remove("CODEX_JS_REPL_NODE_MODULE_DIRS");
        turn.cwd = cwd_dir.path().to_path_buf();
        turn.js_repl = Arc::new(JsReplHandle::with_node_path(
            turn.config.js_repl_node_path.clone(),
            vec![
                first_base.path().to_path_buf(),
                second_base.path().to_path_buf(),
            ],
        ));

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "const mod = await import(\"repl_probe\"); console.log(mod.value);"
                        .to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("first"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_falls_back_to_cwd_node_modules() -> anyhow::Result<()> {
        let config_base = tempdir()?;
        let cwd_dir = tempdir()?;
        write_js_repl_test_package(cwd_dir.path(), "repl_probe", "cwd")?;

        let (session, mut turn) = make_session_and_context().await;
        turn.shell_environment_policy
            .r#set
            .remove("CODEX_JS_REPL_NODE_MODULE_DIRS");
        turn.cwd = cwd_dir.path().to_path_buf();
        turn.js_repl = Arc::new(JsReplHandle::with_node_path(
            turn.config.js_repl_node_path.clone(),
            vec![config_base.path().to_path_buf()],
        ));

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "const mod = await import(\"repl_probe\"); console.log(mod.value);"
                        .to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("cwd"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_accepts_node_modules_dir_entries() -> anyhow::Result<()> {
        let base_dir = tempdir()?;
        let cwd_dir = tempdir()?;
        write_js_repl_test_package(base_dir.path(), "repl_probe", "normalized")?;

        let (session, mut turn) = make_session_and_context().await;
        turn.shell_environment_policy
            .r#set
            .remove("CODEX_JS_REPL_NODE_MODULE_DIRS");
        turn.cwd = cwd_dir.path().to_path_buf();
        turn.js_repl = Arc::new(JsReplHandle::with_node_path(
            turn.config.js_repl_node_path.clone(),
            vec![base_dir.path().join("node_modules")],
        ));

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let result = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "const mod = await import(\"repl_probe\"); console.log(mod.value);"
                        .to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await?;
        assert!(result.output.contains("normalized"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_rejects_path_specifiers() -> anyhow::Result<()> {
        let (session, turn) = make_session_and_context().await;
        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let err = manager
            .execute(
                session,
                turn,
                tracker,
                JsReplArgs {
                    code: "await import(\"./local.js\");".to_string(),
                    timeout_ms: Some(10_000),
                    poll: false,
                    session_id: None,
                },
            )
            .await
            .expect_err("expected path specifier to be rejected");
        assert!(err.to_string().contains("Unsupported import specifier"));
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_does_not_auto_timeout_running_execs() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-timeout".to_string(),
                JsReplArgs {
                    code: "await new Promise((resolve) => setTimeout(resolve, 5_000));".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let no_timeout_deadline = Instant::now() + Duration::from_millis(800);
        while Instant::now() < no_timeout_deadline {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            assert!(
                !result.done,
                "polling exec should remain running without reset"
            );
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        manager.reset_session(&submission.session_id).await?;

        let cancel_deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));
                break;
            }
            if Instant::now() >= cancel_deadline {
                panic!("timed out waiting for reset cancellation");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_reset_session_cancels_inflight_tool_call_promptly() -> anyhow::Result<()>
    {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let started_marker = turn.cwd.join(format!(
            "js-repl-poll-reset-timeout-race-started-{}.txt",
            Uuid::new_v4()
        ));
        let done_marker = turn.cwd.join(format!(
            "js-repl-poll-reset-timeout-race-done-{}.txt",
            Uuid::new_v4()
        ));
        let started_json = serde_json::to_string(&started_marker.to_string_lossy().to_string())?;
        let done_json = serde_json::to_string(&done_marker.to_string_lossy().to_string())?;
        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-reset-timeout-race".to_string(),
                JsReplArgs {
                    code: format!(
                        r#"
const started = {started_json};
const done = {done_json};
await codex.tool("shell_command", {{ command: `printf started > "${{started}}"; sleep 8; printf done > "${{done}}"` }});
console.log("unexpected");
"#
                    ),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let started_deadline = Instant::now() + Duration::from_secs(5);
        loop {
            if tokio::fs::metadata(&started_marker).await.is_ok() {
                break;
            }
            if Instant::now() >= started_deadline {
                panic!("timed out waiting for in-flight tool call to start");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        tokio::time::timeout(
            Duration::from_secs(2),
            manager.reset_session(&submission.session_id),
        )
        .await
        .expect("reset_session should complete promptly")
        .expect("reset_session should succeed");

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for reset_session cancellation completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let _ = tokio::fs::remove_file(&started_marker).await;
        let _ = tokio::fs::remove_file(&done_marker).await;

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_reset_all_cancels_inflight_tool_call_promptly() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let started_marker = turn.cwd.join(format!(
            "js-repl-poll-reset-all-timeout-race-started-{}.txt",
            Uuid::new_v4()
        ));
        let done_marker = turn.cwd.join(format!(
            "js-repl-poll-reset-all-timeout-race-done-{}.txt",
            Uuid::new_v4()
        ));
        let started_json = serde_json::to_string(&started_marker.to_string_lossy().to_string())?;
        let done_json = serde_json::to_string(&done_marker.to_string_lossy().to_string())?;
        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-reset-all-timeout-race".to_string(),
                JsReplArgs {
                    code: format!(
                        r#"
const started = {started_json};
const done = {done_json};
await codex.tool("shell_command", {{ command: `printf started > "${{started}}"; sleep 8; printf done > "${{done}}"` }});
console.log("unexpected");
"#
                    ),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let started_deadline = Instant::now() + Duration::from_secs(5);
        loop {
            if tokio::fs::metadata(&started_marker).await.is_ok() {
                break;
            }
            if Instant::now() >= started_deadline {
                panic!("timed out waiting for in-flight tool call to start");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        tokio::time::timeout(Duration::from_secs(2), manager.reset())
            .await
            .expect("reset should complete promptly")
            .expect("reset should succeed");

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&submission.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));
                break;
            }
            if Instant::now() >= deadline {
                panic!("timed out waiting for reset-all cancellation completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let _ = tokio::fs::remove_file(&started_marker).await;
        let _ = tokio::fs::remove_file(&done_marker).await;

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_reset_session_cancels_only_target_session_tool_calls()
    -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let started_a = turn
            .cwd
            .join(format!("js-repl-poll-reset-scope-a-{}.txt", Uuid::new_v4()));
        let started_b = turn
            .cwd
            .join(format!("js-repl-poll-reset-scope-b-{}.txt", Uuid::new_v4()));
        let started_a_json = serde_json::to_string(&started_a.to_string_lossy().to_string())?;
        let started_b_json = serde_json::to_string(&started_b.to_string_lossy().to_string())?;

        let session_a = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-reset-scope-a".to_string(),
                JsReplArgs {
                    code: format!(
                        r#"
const started = {started_a_json};
await codex.tool("shell_command", {{ command: `printf started > "${{started}}"; sleep 8` }});
console.log("session-a-complete");
"#
                    ),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let session_b = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-reset-scope-b".to_string(),
                JsReplArgs {
                    code: format!(
                        r#"
const started = {started_b_json};
await codex.tool("shell_command", {{ command: `printf started > "${{started}}"; sleep 0.4` }});
console.log("session-b-complete");
"#
                    ),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let started_deadline = Instant::now() + Duration::from_secs(5);
        let mut saw_started_a = false;
        let mut saw_started_b = false;
        while !(saw_started_a && saw_started_b) {
            if tokio::fs::metadata(&started_a).await.is_ok() {
                saw_started_a = true;
            }
            if tokio::fs::metadata(&started_b).await.is_ok() {
                saw_started_b = true;
            }
            if Instant::now() >= started_deadline {
                panic!("timed out waiting for both sessions to start tool calls");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        tokio::time::timeout(
            Duration::from_secs(2),
            manager.reset_session(&session_a.session_id),
        )
        .await
        .expect("session-scoped reset should complete promptly")
        .expect("session-scoped reset should succeed");

        let session_a_deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let result = manager.poll(&session_a.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));
                break;
            }
            if Instant::now() >= session_a_deadline {
                panic!("timed out waiting for target session cancellation");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let session_b_deadline = Instant::now() + Duration::from_secs(8);
        loop {
            let result = manager.poll(&session_b.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error, None);
                assert!(
                    result
                        .output
                        .as_deref()
                        .is_some_and(|output| output.contains("session-b-complete"))
                );
                break;
            }
            if Instant::now() >= session_b_deadline {
                panic!("timed out waiting for non-target session completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let _ = tokio::fs::remove_file(&started_a).await;
        let _ = tokio::fs::remove_file(&started_b).await;
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_unawaited_tool_result_preserves_session() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        let done_marker = turn.cwd.join(format!(
            "js-repl-poll-unawaited-done-{}.txt",
            Uuid::new_v4()
        ));
        let done_marker_json = serde_json::to_string(&done_marker.to_string_lossy().to_string())?;
        let first = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-unawaited-timeout-race".to_string(),
                JsReplArgs {
                    code: format!(
                        r#"
let persisted = 7;
const done = {done_marker_json};
void codex.tool("shell_command", {{ command: `sleep 0.35; printf done > "${{done}}"` }});
console.log("main-complete");
"#
                    ),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        let first_deadline = Instant::now() + Duration::from_secs(6);
        loop {
            let result = manager.poll(&first.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error, None);
                assert!(
                    result
                        .output
                        .as_deref()
                        .is_some_and(|output| output.contains("main-complete")),
                    "first exec should complete successfully before timeout teardown",
                );
                break;
            }
            if Instant::now() >= first_deadline {
                panic!("timed out waiting for first exec completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let marker_deadline = Instant::now() + Duration::from_secs(6);
        loop {
            if tokio::fs::metadata(&done_marker).await.is_ok() {
                break;
            }
            if Instant::now() >= marker_deadline {
                panic!("timed out waiting for unawaited tool call completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let second = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default())),
                "call-unawaited-timeout-race-reuse".to_string(),
                JsReplArgs {
                    code: "console.log(persisted);".to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: Some(first.session_id.clone()),
                },
            )
            .await?;
        assert_eq!(second.session_id, first.session_id);

        let second_deadline = Instant::now() + Duration::from_secs(6);
        loop {
            let result = manager.poll(&second.exec_id, Some(200)).await?;
            if result.done {
                assert_eq!(result.error, None);
                assert!(
                    result
                        .output
                        .as_deref()
                        .is_some_and(|output| output.contains("7")),
                    "session should remain reusable after first exec completion",
                );
                break;
            }
            if Instant::now() >= second_deadline {
                panic!("timed out waiting for second exec completion");
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }

        let _ = tokio::fs::remove_file(&done_marker).await;
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_reset_session_marks_exec_canceled() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let manager = turn.js_repl.manager().await?;

        for attempt in 0..4 {
            let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
            let submission = Arc::clone(&manager)
                .submit(
                    Arc::clone(&session),
                    Arc::clone(&turn),
                    tracker,
                    format!("call-cancel-{attempt}"),
                    JsReplArgs {
                        code: "await new Promise((resolve) => setTimeout(resolve, 10_000));"
                            .to_string(),
                        timeout_ms: None,
                        poll: true,
                        session_id: None,
                    },
                )
                .await?;

            tokio::time::sleep(Duration::from_millis(100)).await;
            manager.reset_session(&submission.session_id).await?;

            let deadline = Instant::now() + Duration::from_secs(5);
            loop {
                let result = manager.poll(&submission.exec_id, Some(200)).await?;
                if result.done {
                    let err = result.error.as_deref();
                    assert_eq!(err, Some(JS_REPL_CANCEL_ERROR_MESSAGE));
                    assert!(
                        !err.is_some_and(|message| message.contains("kernel exited unexpectedly"))
                    );
                    break;
                }
                if Instant::now() >= deadline {
                    panic!("timed out waiting for js_repl poll reset completion");
                }
                tokio::time::sleep(Duration::from_millis(25)).await;
            }
        }

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_reset_session_rejects_unknown_session_id() -> anyhow::Result<()> {
        let (_session, turn) = make_session_and_context().await;
        let manager = turn.js_repl.manager().await?;
        let err = manager
            .reset_session("missing-session")
            .await
            .expect_err("expected missing session id error");
        assert_eq!(err.to_string(), "js_repl session id not found");
        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_reset_marks_running_exec_canceled() -> anyhow::Result<()> {
        let (session, mut turn) = make_session_and_context().await;
        turn.approval_policy = AskForApproval::Never;
        turn.sandbox_policy = SandboxPolicy::DangerFullAccess;

        let session = Arc::new(session);
        let turn = Arc::new(turn);
        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;

        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-reset".to_string(),
                JsReplArgs {
                    code: "await new Promise((resolve) => setTimeout(resolve, 10_000));"
                        .to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        tokio::time::sleep(Duration::from_millis(100)).await;
        manager.reset().await?;

        let result = manager.poll(&submission.exec_id, Some(200)).await?;
        assert!(result.done);
        assert_eq!(result.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_reset_emits_exec_end_for_running_exec() -> anyhow::Result<()> {
        let (session, mut turn, rx) = crate::codex::make_session_and_context_with_rx().await;
        let turn_mut = Arc::get_mut(&mut turn).expect("turn context should be uniquely owned");
        configure_js_repl_test_sandbox(turn_mut);

        let tracker = Arc::new(tokio::sync::Mutex::new(TurnDiffTracker::default()));
        let manager = turn.js_repl.manager().await?;
        let submission = Arc::clone(&manager)
            .submit(
                Arc::clone(&session),
                Arc::clone(&turn),
                tracker,
                "call-reset-end".to_string(),
                JsReplArgs {
                    code: "await new Promise((resolve) => setTimeout(resolve, 10_000));"
                        .to_string(),
                    timeout_ms: None,
                    poll: true,
                    session_id: None,
                },
            )
            .await?;

        tokio::time::sleep(Duration::from_millis(100)).await;
        manager.reset().await?;

        let end = tokio::time::timeout(Duration::from_secs(5), async {
            loop {
                let event = rx.recv().await.expect("event");
                if let EventMsg::ExecCommandEnd(end) = event.msg
                    && end.call_id == "call-reset-end"
                {
                    break end;
                }
            }
        })
        .await
        .expect("timed out waiting for js_repl reset exec end event");
        assert_eq!(end.stderr, JS_REPL_CANCEL_ERROR_MESSAGE);

        let result = manager.poll(&submission.exec_id, Some(200)).await?;
        assert!(result.done);
        assert_eq!(result.error.as_deref(), Some(JS_REPL_CANCEL_ERROR_MESSAGE));

        Ok(())
    }

    #[tokio::test]
    async fn js_repl_poll_rejects_unknown_exec_id() -> anyhow::Result<()> {
        let (_session, turn) = make_session_and_context().await;
        let manager = turn.js_repl.manager().await?;
        let err = manager
            .poll("missing-exec-id", Some(50))
            .await
            .expect_err("expected missing exec id error");
        assert_eq!(err.to_string(), "js_repl exec id not found");
        Ok(())
    }
}
