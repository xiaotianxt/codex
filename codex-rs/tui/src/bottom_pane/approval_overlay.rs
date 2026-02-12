use std::collections::HashMap;
use std::collections::HashSet;
use std::path::PathBuf;

use crate::app_event::AppEvent;
use crate::app_event_sender::AppEventSender;
use crate::bottom_pane::BottomPaneView;
use crate::bottom_pane::CancellationEvent;
use crate::bottom_pane::ChatComposer;
use crate::bottom_pane::ChatComposerConfig;
use crate::bottom_pane::list_selection_view::ListSelectionView;
use crate::bottom_pane::list_selection_view::SelectionItem;
use crate::bottom_pane::list_selection_view::SelectionViewParams;
use crate::diff_render::DiffSummary;
use crate::exec_command::strip_bash_lc_and_escape;
use crate::history_cell;
use crate::key_hint;
use crate::key_hint::KeyBinding;
use crate::render::highlight::highlight_bash_to_lines;
use crate::render::renderable::ColumnRenderable;
use crate::render::renderable::Renderable;
use codex_core::features::Feature;
use codex_core::features::Features;
use codex_core::protocol::ElicitationAction;
use codex_core::protocol::ExecPolicyAmendment;
use codex_core::protocol::FileChange;
use codex_core::protocol::NetworkApprovalContext;
use codex_core::protocol::Op;
use codex_core::protocol::ReviewDecision;
use codex_protocol::mcp::RequestId;
use crossterm::event::KeyCode;
use crossterm::event::KeyEvent;
use crossterm::event::KeyEventKind;
use crossterm::event::KeyModifiers;
use ratatui::buffer::Buffer;
use ratatui::layout::Rect;
use ratatui::style::Stylize;
use ratatui::text::Line;
use ratatui::text::Span;
use ratatui::widgets::Paragraph;
use ratatui::widgets::Wrap;
use serde_json::Map;
use serde_json::Value;
use textwrap::wrap;

/// Request coming from the agent that needs user approval.
#[derive(Clone, Debug)]
pub(crate) enum ApprovalRequest {
    Exec {
        id: String,
        command: Vec<String>,
        reason: Option<String>,
        network_approval_context: Option<NetworkApprovalContext>,
        proposed_execpolicy_amendment: Option<ExecPolicyAmendment>,
    },
    ApplyPatch {
        id: String,
        reason: Option<String>,
        cwd: PathBuf,
        changes: HashMap<PathBuf, FileChange>,
    },
    McpElicitation {
        server_name: String,
        request_id: RequestId,
        message: String,
        requested_schema: Option<Value>,
        url: Option<String>,
    },
}

/// Modal overlay asking the user to approve or deny one or more requests.
pub(crate) struct ApprovalOverlay {
    current_request: Option<ApprovalRequest>,
    current_variant: Option<ApprovalVariant>,
    queue: Vec<ApprovalRequest>,
    app_event_tx: AppEventSender,
    list: ListSelectionView,
    elicitation_form: Option<ElicitationFormState>,
    options: Vec<ApprovalOption>,
    current_complete: bool,
    done: bool,
    features: Features,
}

impl ApprovalOverlay {
    pub fn new(request: ApprovalRequest, app_event_tx: AppEventSender, features: Features) -> Self {
        let mut view = Self {
            current_request: None,
            current_variant: None,
            queue: Vec::new(),
            app_event_tx: app_event_tx.clone(),
            list: ListSelectionView::new(Default::default(), app_event_tx),
            elicitation_form: None,
            options: Vec::new(),
            current_complete: false,
            done: false,
            features,
        };
        view.set_current(request);
        view
    }

    pub fn enqueue_request(&mut self, req: ApprovalRequest) {
        self.queue.push(req);
    }

    fn set_current(&mut self, request: ApprovalRequest) {
        let request = if self.features.enabled(Feature::ElicitationAppsGateway) {
            request
        } else {
            match request {
                ApprovalRequest::McpElicitation {
                    server_name,
                    request_id,
                    message,
                    ..
                } => ApprovalRequest::McpElicitation {
                    server_name,
                    request_id,
                    message,
                    requested_schema: None,
                    url: None,
                },
                request => request,
            }
        };
        self.current_request = Some(request.clone());
        self.elicitation_form =
            Self::build_form_state(&request, &self.app_event_tx, &self.features);
        let ApprovalRequestState { variant, header } = ApprovalRequestState::from(request);
        self.current_variant = Some(variant.clone());
        self.current_complete = false;
        let (options, params) = Self::build_options(variant, header, &self.features);
        self.options = options;
        self.list = ListSelectionView::new(params, self.app_event_tx.clone());
    }

    fn build_form_state(
        request: &ApprovalRequest,
        app_event_tx: &AppEventSender,
        features: &Features,
    ) -> Option<ElicitationFormState> {
        if !features.enabled(Feature::ElicitationAppsGateway) {
            return None;
        }
        let ApprovalRequest::McpElicitation {
            requested_schema, ..
        } = request
        else {
            return None;
        };
        let requested_schema = requested_schema.as_ref()?;
        let fields = parse_elicitation_schema_fields(requested_schema)
            .filter(|fields| !fields.is_empty())
            .unwrap_or_else(|| vec![ElicitationFormField::notes()]);
        Some(ElicitationFormState::new(fields, app_event_tx))
    }

    fn build_options(
        variant: ApprovalVariant,
        header: Box<dyn Renderable>,
        _features: &Features,
    ) -> (Vec<ApprovalOption>, SelectionViewParams) {
        let (options, title) = match &variant {
            ApprovalVariant::Exec {
                network_approval_context,
                proposed_execpolicy_amendment,
                ..
            } => (
                exec_options(
                    proposed_execpolicy_amendment.clone(),
                    network_approval_context.as_ref(),
                ),
                network_approval_context.as_ref().map_or_else(
                    || "Would you like to run the following command?".to_string(),
                    |network_approval_context| {
                        format!(
                            "Do you want to approve access to \"{}\"?",
                            network_approval_context.host
                        )
                    },
                ),
            ),
            ApprovalVariant::ApplyPatch { .. } => (
                patch_options(),
                "Would you like to make the following edits?".to_string(),
            ),
            ApprovalVariant::McpElicitation { server_name, .. } => (
                elicitation_options(),
                format!("{server_name} needs your approval."),
            ),
        };

        let header = if matches!(variant, ApprovalVariant::McpElicitation { .. }) {
            Box::new(ColumnRenderable::with([
                Line::from(title.bold()).into(),
                header,
            ]))
        } else {
            Box::new(ColumnRenderable::with([
                Line::from(title.bold()).into(),
                Line::from("").into(),
                header,
            ]))
        };

        let items = options
            .iter()
            .map(|opt| SelectionItem {
                name: opt.label.clone(),
                display_shortcut: opt
                    .display_shortcut
                    .or_else(|| opt.additional_shortcuts.first().copied()),
                dismiss_on_select: false,
                ..Default::default()
            })
            .collect();

        let params = SelectionViewParams {
            footer_hint: Some(Line::from(vec![
                "Press ".into(),
                key_hint::plain(KeyCode::Enter).into(),
                " to confirm or ".into(),
                key_hint::plain(KeyCode::Esc).into(),
                " to cancel".into(),
            ])),
            items,
            header,
            ..Default::default()
        };

        (options, params)
    }

    fn apply_selection(&mut self, actual_idx: usize) {
        if self.current_complete {
            return;
        }
        let Some(option) = self.options.get(actual_idx).cloned() else {
            return;
        };
        if let Some(variant) = self.current_variant.clone() {
            match (variant, option.decision) {
                (ApprovalVariant::Exec { id, command, .. }, ApprovalDecision::Review(decision)) => {
                    self.handle_exec_decision(&id, &command, decision);
                }
                (ApprovalVariant::ApplyPatch { id, .. }, ApprovalDecision::Review(decision)) => {
                    self.handle_patch_decision(&id, decision);
                }
                (
                    ApprovalVariant::McpElicitation {
                        server_name,
                        request_id,
                    },
                    ApprovalDecision::McpElicitation(decision),
                ) => {
                    let mcp_elicitations_enabled =
                        self.features.enabled(Feature::ElicitationAppsGateway);
                    if mcp_elicitations_enabled
                        && matches!(decision, ElicitationAction::Accept)
                        && !self.ensure_elicitation_required_fields_ready()
                    {
                        return;
                    }
                    self.handle_elicitation_decision(
                        &server_name,
                        &request_id,
                        decision,
                        if mcp_elicitations_enabled {
                            self.elicitation_form_payload()
                        } else {
                            None
                        },
                    );
                }
                _ => {}
            }
        }

        self.current_complete = true;
        self.advance_queue();
    }

    fn handle_exec_decision(&self, id: &str, command: &[String], decision: ReviewDecision) {
        let cell = history_cell::new_approval_decision_cell(command.to_vec(), decision.clone());
        self.app_event_tx.send(AppEvent::InsertHistoryCell(cell));
        self.app_event_tx.send(AppEvent::CodexOp(Op::ExecApproval {
            id: id.to_string(),
            turn_id: None,
            decision,
        }));
    }

    fn handle_patch_decision(&self, id: &str, decision: ReviewDecision) {
        self.app_event_tx.send(AppEvent::CodexOp(Op::PatchApproval {
            id: id.to_string(),
            decision,
        }));
    }

    fn handle_elicitation_decision(
        &self,
        server_name: &str,
        request_id: &RequestId,
        decision: ElicitationAction,
        response_content: Option<Value>,
    ) {
        self.app_event_tx
            .send(AppEvent::CodexOp(Op::ResolveElicitation {
                server_name: server_name.to_string(),
                request_id: request_id.clone(),
                decision,
                response_content,
            }));
    }

    fn elicitation_form_payload(&self) -> Option<Value> {
        self.elicitation_form
            .as_ref()
            .and_then(ElicitationFormState::to_value)
    }

    fn ensure_elicitation_required_fields_ready(&mut self) -> bool {
        let Some(form) = self.elicitation_form.as_mut() else {
            return true;
        };
        if form.has_missing_required_fields() {
            form.focus_first_missing_required_field();
            return false;
        }
        true
    }

    fn advance_queue(&mut self) {
        if let Some(next) = self.queue.pop() {
            self.set_current(next);
        } else {
            self.done = true;
        }
    }

    fn try_handle_form_key_event(&mut self, key_event: &KeyEvent) -> bool {
        let Some(form) = self.elicitation_form.as_mut() else {
            return false;
        };
        if !matches!(key_event.kind, KeyEventKind::Press) {
            return false;
        }

        if !form.is_editing {
            if matches!(key_event.code, KeyCode::Tab) {
                form.start_editing();
                return true;
            }
            if Self::is_form_input_key(key_event) {
                form.start_editing();
                let (_result, handled) = form.composer.handle_key_event(*key_event);
                return handled;
            }
            return false;
        }

        match key_event.code {
            KeyCode::Enter | KeyCode::Tab => {
                form.submit_current_field();
                true
            }
            _ => {
                let (_result, handled) = form.composer.handle_key_event(*key_event);
                handled
            }
        }
    }

    fn is_form_input_key(key_event: &KeyEvent) -> bool {
        matches!(
            key_event,
            KeyEvent {
                code: KeyCode::Char(ch),
                modifiers,
                kind: KeyEventKind::Press,
                ..
            } if modifiers.is_empty() && !matches!(ch, 'y' | 'Y' | 'n' | 'N' | 'c' | 'C')
        )
    }

    fn try_handle_shortcut(&mut self, key_event: &KeyEvent) -> bool {
        if self
            .elicitation_form
            .as_ref()
            .is_some_and(|form| form.is_editing)
            && matches!(
                key_event,
                KeyEvent {
                    code: KeyCode::Char('a')
                        | KeyCode::Char('c')
                        | KeyCode::Char('n')
                        | KeyCode::Char('y'),
                    modifiers: KeyModifiers::NONE,
                    ..
                }
            )
        {
            return false;
        }
        match key_event {
            KeyEvent {
                kind: KeyEventKind::Press,
                code: KeyCode::Char('a'),
                modifiers,
                ..
            } if modifiers.contains(KeyModifiers::CONTROL) => {
                if let Some(request) = self.current_request.as_ref() {
                    self.app_event_tx
                        .send(AppEvent::FullScreenApprovalRequest(request.clone()));
                    true
                } else {
                    false
                }
            }
            e => {
                if let Some(idx) = self
                    .options
                    .iter()
                    .position(|opt| opt.shortcuts().any(|s| s.is_press(*e)))
                {
                    self.apply_selection(idx);
                    true
                } else {
                    false
                }
            }
        }
    }
}

impl BottomPaneView for ApprovalOverlay {
    fn handle_key_event(&mut self, key_event: KeyEvent) {
        if self.try_handle_form_key_event(&key_event) {
            return;
        }
        if self.try_handle_shortcut(&key_event) {
            return;
        }
        self.list.handle_key_event(key_event);
        if let Some(idx) = self.list.take_last_selected_index() {
            self.apply_selection(idx);
        }
    }

    fn on_ctrl_c(&mut self) -> CancellationEvent {
        if self.done {
            return CancellationEvent::Handled;
        }
        if !self.current_complete
            && let Some(variant) = self.current_variant.as_ref()
        {
            match &variant {
                ApprovalVariant::Exec { id, command, .. } => {
                    self.handle_exec_decision(id, command, ReviewDecision::Abort);
                }
                ApprovalVariant::ApplyPatch { id, .. } => {
                    self.handle_patch_decision(id, ReviewDecision::Abort);
                }
                ApprovalVariant::McpElicitation {
                    server_name,
                    request_id,
                } => {
                    self.handle_elicitation_decision(
                        server_name,
                        request_id,
                        ElicitationAction::Cancel,
                        None,
                    );
                }
            }
        }
        self.queue.clear();
        self.done = true;
        CancellationEvent::Handled
    }

    fn is_complete(&self) -> bool {
        self.done
    }

    fn try_consume_approval_request(
        &mut self,
        request: ApprovalRequest,
    ) -> Option<ApprovalRequest> {
        self.enqueue_request(request);
        None
    }
}

impl Renderable for ApprovalOverlay {
    fn desired_height(&self, width: u16) -> u16 {
        let list_height = self.list.desired_height(width);
        list_height.saturating_add(
            self.elicitation_form
                .as_ref()
                .map_or(0, |form| form.height(width)),
        )
    }

    fn render(&self, area: Rect, buf: &mut Buffer) {
        if let Some(form) = self.elicitation_form.as_ref() {
            let composer_height = form.height(area.width);
            if composer_height > 0 && composer_height < area.height {
                let list_area = Rect {
                    x: area.x,
                    y: area.y,
                    width: area.width,
                    height: area.height - composer_height,
                };
                let composer_area = Rect {
                    x: area.x,
                    y: area.y + list_area.height,
                    width: area.width,
                    height: composer_height,
                };
                self.list.render(list_area, buf);
                form.composer.render(composer_area, buf);
                return;
            }
        }

        self.list.render(area, buf);
    }

    fn cursor_pos(&self, area: Rect) -> Option<(u16, u16)> {
        if let Some(form) = self.elicitation_form.as_ref()
            && form.is_editing
        {
            let composer_height = form.height(area.width);
            if composer_height > 0 && composer_height < area.height {
                let list_area = Rect {
                    x: area.x,
                    y: area.y,
                    width: area.width,
                    height: area.height - composer_height,
                };
                let composer_area = Rect {
                    x: area.x,
                    y: area.y + list_area.height,
                    width: area.width,
                    height: composer_height,
                };
                return form.composer.cursor_pos(composer_area);
            }
        }
        self.list.cursor_pos(area)
    }
}

struct ApprovalRequestState {
    variant: ApprovalVariant,
    header: Box<dyn Renderable>,
}

impl From<ApprovalRequest> for ApprovalRequestState {
    fn from(value: ApprovalRequest) -> Self {
        match value {
            ApprovalRequest::Exec {
                id,
                command,
                reason,
                network_approval_context,
                proposed_execpolicy_amendment,
            } => {
                let mut header: Vec<Line<'static>> = Vec::new();
                if let Some(reason) = reason {
                    header.push(Line::from(vec!["Reason: ".into(), reason.italic()]));
                    header.push(Line::from(""));
                }
                let full_cmd = strip_bash_lc_and_escape(&command);
                let mut full_cmd_lines = highlight_bash_to_lines(&full_cmd);
                if let Some(first) = full_cmd_lines.first_mut() {
                    first.spans.insert(0, Span::from("$ "));
                }
                header.extend(full_cmd_lines);
                Self {
                    variant: ApprovalVariant::Exec {
                        id,
                        command,
                        network_approval_context,
                        proposed_execpolicy_amendment,
                    },
                    header: Box::new(Paragraph::new(header).wrap(Wrap { trim: false })),
                }
            }
            ApprovalRequest::ApplyPatch {
                id,
                reason,
                cwd,
                changes,
            } => {
                let mut header: Vec<Box<dyn Renderable>> = Vec::new();
                if let Some(reason) = reason
                    && !reason.is_empty()
                {
                    header.push(Box::new(
                        Paragraph::new(Line::from_iter(["Reason: ".into(), reason.italic()]))
                            .wrap(Wrap { trim: false }),
                    ));
                    header.push(Box::new(Line::from("")));
                }
                header.push(DiffSummary::new(changes, cwd).into());
                Self {
                    variant: ApprovalVariant::ApplyPatch { id },
                    header: Box::new(ColumnRenderable::with(header)),
                }
            }
            ApprovalRequest::McpElicitation {
                server_name,
                request_id,
                message,
                requested_schema,
                url,
            } => {
                let app_name = parse_elicitation_app_name(&message);
                let mut header_lines = vec![
                    Line::from(vec!["  Server: ".into(), server_name.clone().bold()]),
                    Line::from(message),
                ];
                if let Some(app_name) = app_name {
                    header_lines.insert(1, Line::from(vec!["  App: ".into(), app_name.bold()]));
                }
                if let Some(url) = url {
                    header_lines.push(Line::from(vec!["  URL: ".into(), url.cyan()]));
                }
                if let Some(requested_schema) = requested_schema {
                    let properties = requested_schema
                        .get("properties")
                        .and_then(|properties| properties.as_object())
                        .map(|properties| properties.keys().cloned().collect::<Vec<_>>())
                        .unwrap_or_default();
                    if !properties.is_empty() {
                        let schema_line = format!("  Schema properties: {}", properties.join(", "));
                        for wrapped_line in wrap(&schema_line, 80) {
                            header_lines.push(Line::from(wrapped_line.into_owned()));
                        }
                    }
                }
                let header = Paragraph::new(header_lines).wrap(Wrap { trim: false });
                Self {
                    variant: ApprovalVariant::McpElicitation {
                        server_name,
                        request_id,
                    },
                    header: Box::new(header),
                }
            }
        }
    }
}

fn parse_elicitation_app_name(message: &str) -> Option<String> {
    let marker = " from `";
    let start = message.find(marker)? + marker.len();
    let end = message[start..].find('`')?;
    let app_name = message.get(start..start + end)?;
    (!app_name.is_empty()).then_some(app_name.to_string())
}

#[derive(Clone)]
enum ApprovalVariant {
    Exec {
        id: String,
        command: Vec<String>,
        network_approval_context: Option<NetworkApprovalContext>,
        proposed_execpolicy_amendment: Option<ExecPolicyAmendment>,
    },
    ApplyPatch {
        id: String,
    },
    McpElicitation {
        server_name: String,
        request_id: RequestId,
    },
}

#[derive(Clone)]
enum ElicitationFieldType {
    Boolean,
    Integer,
    Number,
    Array,
    Object,
    String,
    Unknown,
}

#[derive(Clone)]
struct ElicitationFormField {
    name: String,
    field_type: ElicitationFieldType,
    required: bool,
    title: Option<String>,
}

impl ElicitationFormField {
    fn notes() -> Self {
        Self {
            name: "response".to_string(),
            field_type: ElicitationFieldType::String,
            required: false,
            title: None,
        }
    }
}

struct ElicitationFormState {
    fields: Vec<ElicitationFormField>,
    values: Vec<String>,
    current_field: usize,
    is_editing: bool,
    composer: ChatComposer,
}

impl ElicitationFormState {
    fn new(fields: Vec<ElicitationFormField>, app_event_tx: &AppEventSender) -> Self {
        let mut composer = ChatComposer::new_with_config(
            true,
            app_event_tx.clone(),
            false,
            String::new(),
            true,
            ChatComposerConfig::plain_text(),
        );
        composer.set_footer_hint_override(Some(Vec::<(String, String)>::new()));
        let mut state = Self {
            fields,
            values: Vec::new(),
            current_field: 0,
            is_editing: false,
            composer,
        };
        state.values = state.fields.iter().map(|_| String::new()).collect();
        state.update_placeholder();
        state
    }

    fn height(&self, width: u16) -> u16 {
        self.composer.desired_height(width)
    }

    fn start_editing(&mut self) {
        self.is_editing = true;
        if let Some(value) = self.values.get(self.current_field) {
            self.composer
                .set_text_content(value.to_owned(), Vec::new(), Vec::new());
        }
        self.update_placeholder();
    }

    fn submit_current_field(&mut self) {
        self.composer.flush_paste_burst_if_due();
        let current_text = self.composer.current_text_with_pending();
        if let Some(current_value) = self.values.get_mut(self.current_field) {
            *current_value = current_text;
        }
        self.composer
            .set_text_content(String::new(), Vec::new(), Vec::new());
        if self.current_field + 1 < self.fields.len() {
            self.current_field += 1;
            self.update_placeholder();
            return;
        }
        self.is_editing = false;
    }

    fn update_placeholder(&mut self) {
        let label = self
            .fields
            .get(self.current_field)
            .map(|field| {
                if let Some(title) = &field.title {
                    if field.required {
                        format!("{} ({title}) *", field.name)
                    } else {
                        format!("{} ({title})", field.name)
                    }
                } else if field.required {
                    format!("{} *", field.name)
                } else {
                    field.name.clone()
                }
            })
            .unwrap_or_else(|| "Response".to_string());
        self.composer.set_placeholder_text(format!("{label}: "));
    }

    fn to_value(&self) -> Option<Value> {
        let mut fields = Map::new();
        for (field, value) in self.fields.iter().zip(self.values.iter()) {
            if value.trim().is_empty() {
                continue;
            }
            fields.insert(
                field.name.clone(),
                parse_input_value(value, &field.field_type),
            );
        }
        (!fields.is_empty()).then_some(Value::Object(fields))
    }

    fn has_missing_required_fields(&self) -> bool {
        self.fields
            .iter()
            .zip(self.values.iter())
            .any(|(field, value)| field.required && value.trim().is_empty())
    }

    fn focus_first_missing_required_field(&mut self) {
        if let Some(missing_index) = self
            .fields
            .iter()
            .zip(self.values.iter())
            .position(|(field, value)| field.required && value.trim().is_empty())
        {
            self.current_field = missing_index;
            self.start_editing();
        }
    }
}

fn parse_elicitation_schema_fields(requested_schema: &Value) -> Option<Vec<ElicitationFormField>> {
    let properties = requested_schema.get("properties")?.as_object()?;
    let required = requested_schema
        .get("required")
        .and_then(Value::as_array)
        .map(|required| {
            required
                .iter()
                .filter_map(Value::as_str)
                .map(ToString::to_string)
                .collect::<HashSet<_>>()
        })
        .unwrap_or_default();

    Some(
        properties
            .iter()
            .map(|(name, schema)| {
                let field_type = schema
                    .get("type")
                    .map(parse_schema_type)
                    .unwrap_or(ElicitationFieldType::Unknown);
                ElicitationFormField {
                    name: name.to_string(),
                    required: required.contains(name),
                    title: schema
                        .get("title")
                        .and_then(Value::as_str)
                        .map(ToString::to_string),
                    field_type,
                }
            })
            .collect(),
    )
}

fn parse_schema_type(value: &Value) -> ElicitationFieldType {
    if let Some(field_type) = value.as_str() {
        return parse_schema_type_str(field_type);
    }
    let Some(types) = value.as_array() else {
        return ElicitationFieldType::Unknown;
    };
    types
        .iter()
        .filter_map(Value::as_str)
        .filter(|field_type| *field_type != "null")
        .map(parse_schema_type_str)
        .find(|field_type| !matches!(field_type, ElicitationFieldType::Unknown))
        .unwrap_or(ElicitationFieldType::Unknown)
}

fn parse_schema_type_str(field_type: &str) -> ElicitationFieldType {
    match field_type {
        "boolean" => ElicitationFieldType::Boolean,
        "integer" => ElicitationFieldType::Integer,
        "number" => ElicitationFieldType::Number,
        "object" => ElicitationFieldType::Object,
        "array" => ElicitationFieldType::Array,
        "string" => ElicitationFieldType::String,
        _ => ElicitationFieldType::Unknown,
    }
}

fn parse_input_value(input: &str, field_type: &ElicitationFieldType) -> Value {
    let trimmed = input.trim();
    match field_type {
        ElicitationFieldType::Boolean => trimmed
            .parse::<bool>()
            .map(Value::from)
            .unwrap_or_else(|_| Value::String(trimmed.to_string())),
        ElicitationFieldType::Integer => {
            trimmed.parse::<i64>().map(Value::from).unwrap_or_else(|_| {
                trimmed
                    .parse::<f64>()
                    .map_or(Value::String(trimmed.to_string()), Value::from)
            })
        }
        ElicitationFieldType::Number => trimmed
            .parse::<f64>()
            .map(Value::from)
            .unwrap_or_else(|_| Value::String(trimmed.to_string())),
        ElicitationFieldType::Array | ElicitationFieldType::Object => {
            serde_json::from_str(trimmed).unwrap_or_else(|_| Value::String(trimmed.to_string()))
        }
        ElicitationFieldType::String | ElicitationFieldType::Unknown => {
            Value::String(trimmed.to_string())
        }
    }
}

#[derive(Clone)]
enum ApprovalDecision {
    Review(ReviewDecision),
    McpElicitation(ElicitationAction),
}

#[derive(Clone)]
struct ApprovalOption {
    label: String,
    decision: ApprovalDecision,
    display_shortcut: Option<KeyBinding>,
    additional_shortcuts: Vec<KeyBinding>,
}

impl ApprovalOption {
    fn shortcuts(&self) -> impl Iterator<Item = KeyBinding> + '_ {
        self.display_shortcut
            .into_iter()
            .chain(self.additional_shortcuts.iter().copied())
    }
}

fn exec_options(
    proposed_execpolicy_amendment: Option<ExecPolicyAmendment>,
    network_approval_context: Option<&NetworkApprovalContext>,
) -> Vec<ApprovalOption> {
    if network_approval_context.is_some() {
        return vec![
            ApprovalOption {
                label: "Yes, just this once".to_string(),
                decision: ApprovalDecision::Review(ReviewDecision::Approved),
                display_shortcut: None,
                additional_shortcuts: vec![key_hint::plain(KeyCode::Char('y'))],
            },
            ApprovalOption {
                label: "Yes, and allow this host for this session".to_string(),
                decision: ApprovalDecision::Review(ReviewDecision::ApprovedForSession),
                display_shortcut: None,
                additional_shortcuts: vec![key_hint::plain(KeyCode::Char('a'))],
            },
            ApprovalOption {
                label: "No, and tell Codex what to do differently".to_string(),
                decision: ApprovalDecision::Review(ReviewDecision::Abort),
                display_shortcut: Some(key_hint::plain(KeyCode::Esc)),
                additional_shortcuts: vec![key_hint::plain(KeyCode::Char('n'))],
            },
        ];
    }

    vec![ApprovalOption {
        label: "Yes, proceed".to_string(),
        decision: ApprovalDecision::Review(ReviewDecision::Approved),
        display_shortcut: None,
        additional_shortcuts: vec![key_hint::plain(KeyCode::Char('y'))],
    }]
    .into_iter()
    .chain(proposed_execpolicy_amendment.and_then(|prefix| {
        let rendered_prefix = strip_bash_lc_and_escape(prefix.command());
        if rendered_prefix.contains('\n') || rendered_prefix.contains('\r') {
            return None;
        }

        Some(ApprovalOption {
            label: format!(
                "Yes, and don't ask again for commands that start with `{rendered_prefix}`"
            ),
            decision: ApprovalDecision::Review(ReviewDecision::ApprovedExecpolicyAmendment {
                proposed_execpolicy_amendment: prefix,
            }),
            display_shortcut: None,
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('p'))],
        })
    }))
    .chain([ApprovalOption {
        label: "No, and tell Codex what to do differently".to_string(),
        decision: ApprovalDecision::Review(ReviewDecision::Abort),
        display_shortcut: Some(key_hint::plain(KeyCode::Esc)),
        additional_shortcuts: vec![key_hint::plain(KeyCode::Char('n'))],
    }])
    .collect()
}

fn patch_options() -> Vec<ApprovalOption> {
    vec![
        ApprovalOption {
            label: "Yes, proceed".to_string(),
            decision: ApprovalDecision::Review(ReviewDecision::Approved),
            display_shortcut: None,
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('y'))],
        },
        ApprovalOption {
            label: "Yes, and don't ask again for these files".to_string(),
            decision: ApprovalDecision::Review(ReviewDecision::ApprovedForSession),
            display_shortcut: None,
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('a'))],
        },
        ApprovalOption {
            label: "No, and tell Codex what to do differently".to_string(),
            decision: ApprovalDecision::Review(ReviewDecision::Abort),
            display_shortcut: Some(key_hint::plain(KeyCode::Esc)),
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('n'))],
        },
    ]
}

fn elicitation_options() -> Vec<ApprovalOption> {
    vec![
        ApprovalOption {
            label: "Yes, provide the requested info".to_string(),
            decision: ApprovalDecision::McpElicitation(ElicitationAction::Accept),
            display_shortcut: None,
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('y'))],
        },
        ApprovalOption {
            label: "No, but continue without it".to_string(),
            decision: ApprovalDecision::McpElicitation(ElicitationAction::Decline),
            display_shortcut: None,
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('n'))],
        },
        ApprovalOption {
            label: "Cancel this request".to_string(),
            decision: ApprovalDecision::McpElicitation(ElicitationAction::Cancel),
            display_shortcut: Some(key_hint::plain(KeyCode::Esc)),
            additional_shortcuts: vec![key_hint::plain(KeyCode::Char('c'))],
        },
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::app_event::AppEvent;
    use codex_core::protocol::NetworkApprovalProtocol;
    use pretty_assertions::assert_eq;
    use tokio::sync::mpsc::unbounded_channel;

    fn make_exec_request() -> ApprovalRequest {
        ApprovalRequest::Exec {
            id: "test".to_string(),
            command: vec!["echo".to_string(), "hi".to_string()],
            reason: Some("reason".to_string()),
            network_approval_context: None,
            proposed_execpolicy_amendment: None,
        }
    }

    fn make_elicitation_request(
        requested_schema: Option<Value>,
        url: Option<&str>,
    ) -> ApprovalRequest {
        ApprovalRequest::McpElicitation {
            server_name: "mcp-server".to_string(),
            request_id: RequestId::String("request-id-1".to_string()),
            message: "Request user details".to_string(),
            requested_schema,
            url: url.map(ToString::to_string),
        }
    }

    fn mcp_elicitations_features() -> Features {
        let mut features = Features::with_defaults();
        features.enable(Feature::ElicitationAppsGateway);
        features
    }

    #[test]
    fn ctrl_c_aborts_and_clears_queue() {
        let (tx, _rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx);
        let mut view = ApprovalOverlay::new(make_exec_request(), tx, Features::with_defaults());
        view.enqueue_request(make_exec_request());
        assert_eq!(CancellationEvent::Handled, view.on_ctrl_c());
        assert!(view.queue.is_empty());
        assert!(view.is_complete());
    }

    #[test]
    fn shortcut_triggers_selection() {
        let (tx, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx);
        let mut view = ApprovalOverlay::new(make_exec_request(), tx, Features::with_defaults());
        assert!(!view.is_complete());
        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));
        // We expect at least one CodexOp message in the queue.
        let mut saw_op = false;
        while let Ok(ev) = rx.try_recv() {
            if matches!(ev, AppEvent::CodexOp(_)) {
                saw_op = true;
                break;
            }
        }
        assert!(saw_op, "expected approval decision to emit an op");
    }

    #[test]
    fn exec_prefix_option_emits_execpolicy_amendment() {
        let (tx, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx);
        let mut view = ApprovalOverlay::new(
            ApprovalRequest::Exec {
                id: "test".to_string(),
                command: vec!["echo".to_string()],
                reason: None,
                network_approval_context: None,
                proposed_execpolicy_amendment: Some(ExecPolicyAmendment::new(vec![
                    "echo".to_string(),
                ])),
            },
            tx,
            Features::with_defaults(),
        );
        view.handle_key_event(KeyEvent::new(KeyCode::Char('p'), KeyModifiers::NONE));
        let mut saw_op = false;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ExecApproval { decision, .. }) = ev {
                assert_eq!(
                    decision,
                    ReviewDecision::ApprovedExecpolicyAmendment {
                        proposed_execpolicy_amendment: ExecPolicyAmendment::new(vec![
                            "echo".to_string()
                        ])
                    }
                );
                saw_op = true;
                break;
            }
        }
        assert!(
            saw_op,
            "expected approval decision to emit an op with command prefix"
        );
    }

    #[test]
    fn header_includes_command_snippet() {
        let (tx, _rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx);
        let command = vec!["echo".into(), "hello".into(), "world".into()];
        let exec_request = ApprovalRequest::Exec {
            id: "test".into(),
            command,
            reason: None,
            network_approval_context: None,
            proposed_execpolicy_amendment: None,
        };

        let view = ApprovalOverlay::new(exec_request, tx, Features::with_defaults());
        let mut buf = Buffer::empty(Rect::new(0, 0, 80, view.desired_height(80)));
        view.render(Rect::new(0, 0, 80, view.desired_height(80)), &mut buf);

        let rendered: Vec<String> = (0..buf.area.height)
            .map(|row| {
                (0..buf.area.width)
                    .map(|col| buf[(col, row)].symbol().to_string())
                    .collect()
            })
            .collect();
        assert!(
            rendered
                .iter()
                .any(|line| line.contains("echo hello world")),
            "expected header to include command snippet, got {rendered:?}"
        );
    }

    #[test]
    fn network_exec_options_use_expected_labels_and_hide_execpolicy_amendment() {
        let network_context = NetworkApprovalContext {
            host: "example.com".to_string(),
            protocol: NetworkApprovalProtocol::Https,
        };
        let options = exec_options(
            Some(ExecPolicyAmendment::new(vec!["curl".to_string()])),
            Some(&network_context),
        );

        let labels: Vec<String> = options.into_iter().map(|option| option.label).collect();
        assert_eq!(
            labels,
            vec![
                "Yes, just this once".to_string(),
                "Yes, and allow this host for this session".to_string(),
                "No, and tell Codex what to do differently".to_string(),
            ]
        );
    }

    #[test]
    fn network_exec_prompt_title_includes_host() {
        let (tx, _rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx);
        let exec_request = ApprovalRequest::Exec {
            id: "test".into(),
            command: vec!["curl".into(), "https://example.com".into()],
            reason: Some("network request blocked".into()),
            network_approval_context: Some(NetworkApprovalContext {
                host: "example.com".to_string(),
                protocol: NetworkApprovalProtocol::Https,
            }),
            proposed_execpolicy_amendment: Some(ExecPolicyAmendment::new(vec!["curl".into()])),
        };

        let view = ApprovalOverlay::new(exec_request, tx, Features::with_defaults());
        let mut buf = Buffer::empty(Rect::new(0, 0, 100, view.desired_height(100)));
        view.render(Rect::new(0, 0, 100, view.desired_height(100)), &mut buf);

        let rendered: Vec<String> = (0..buf.area.height)
            .map(|row| {
                (0..buf.area.width)
                    .map(|col| buf[(col, row)].symbol().to_string())
                    .collect()
            })
            .collect();

        assert!(
            rendered
                .iter()
                .any(|line| line.contains("Do you want to approve access to \"example.com\"?")),
            "expected network title to include host, got {rendered:?}"
        );
        assert!(
            !rendered.iter().any(|line| line.contains("don't ask again")),
            "network prompt should not show execpolicy option, got {rendered:?}"
        );
    }

    #[test]
    fn exec_history_cell_wraps_with_two_space_indent() {
        let command = vec![
            "/bin/zsh".into(),
            "-lc".into(),
            "git add tui/src/render/mod.rs tui/src/render/renderable.rs".into(),
        ];
        let cell = history_cell::new_approval_decision_cell(command, ReviewDecision::Approved);
        let lines = cell.display_lines(28);
        let rendered: Vec<String> = lines
            .iter()
            .map(|line| {
                line.spans
                    .iter()
                    .map(|span| span.content.as_ref())
                    .collect::<String>()
            })
            .collect();
        let expected = vec![
            "✔ You approved codex to run".to_string(),
            "  git add tui/src/render/".to_string(),
            "  mod.rs tui/src/render/".to_string(),
            "  renderable.rs this time".to_string(),
        ];
        assert_eq!(rendered, expected);
    }

    #[test]
    fn enter_sets_last_selected_index_without_dismissing() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(make_exec_request(), tx, Features::with_defaults());
        view.handle_key_event(KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE));

        assert!(
            view.is_complete(),
            "exec approval should complete without queued requests"
        );

        let mut decision = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ExecApproval { decision: d, .. }) = ev {
                decision = Some(d);
                break;
            }
        }
        assert_eq!(decision, Some(ReviewDecision::Approved));
    }

    #[test]
    fn elicitation_accept_sends_structured_payload_for_schema_fields() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(
            make_elicitation_request(
                Some(serde_json::json!({
                    "properties": {
                        "name": {
                            "type": "string"
                        }
                    }
                })),
                None,
            ),
            tx,
            mcp_elicitations_features(),
        );
        assert!(
            view.elicitation_form.as_ref().is_some(),
            "expected schema-backed form state"
        );

        view.handle_key_event(KeyEvent::new(KeyCode::Tab, KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('a'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('l'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('i'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('c'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('e'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));

        let mut saw_resolve = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ResolveElicitation {
                server_name,
                request_id,
                decision,
                response_content,
            }) = ev
            {
                saw_resolve = Some((server_name, request_id, decision, response_content));
                break;
            }
        }

        assert!(
            saw_resolve.is_some(),
            "expected elicitation resolve op after accepting"
        );
        let (server_name, request_id, decision, response_content) = saw_resolve.unwrap();
        assert_eq!(server_name, "mcp-server");
        assert_eq!(request_id, RequestId::String("request-id-1".to_string()));
        assert_eq!(decision, ElicitationAction::Accept);
        assert_eq!(
            response_content,
            Some(serde_json::json!({ "name": "alice" }))
        );
    }

    #[test]
    fn elicitation_accept_without_parsed_form_schema_allows_decision_without_payload() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(
            make_elicitation_request(Some(serde_json::json!({"type": "string"})), None),
            tx,
            mcp_elicitations_features(),
        );
        assert!(view.elicitation_form.is_some());

        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));

        let mut saw_resolve = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ResolveElicitation {
                server_name,
                request_id,
                decision,
                response_content,
            }) = ev
            {
                saw_resolve = Some((server_name, request_id, decision, response_content));
                break;
            }
        }

        assert!(
            saw_resolve.is_some(),
            "expected elicitation resolve op after accepting"
        );
        let (server_name, request_id, decision, response_content) = saw_resolve.unwrap();
        assert_eq!(server_name, "mcp-server");
        assert_eq!(request_id, RequestId::String("request-id-1".to_string()));
        assert_eq!(decision, ElicitationAction::Accept);
        assert_eq!(response_content, None);
    }

    #[test]
    fn elicitation_cancel_does_not_send_content() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(
            make_elicitation_request(
                Some(serde_json::json!({
                    "properties": {
                        "age": {
                            "type": "number"
                        }
                    }
                })),
                None,
            ),
            tx,
            mcp_elicitations_features(),
        );
        view.handle_key_event(KeyEvent::new(KeyCode::Char('c'), KeyModifiers::NONE));

        let mut saw_resolve = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ResolveElicitation {
                server_name,
                request_id,
                decision,
                response_content,
            }) = ev
            {
                saw_resolve = Some((server_name, request_id, decision, response_content));
                break;
            }
        }

        assert!(
            saw_resolve.is_some(),
            "expected elicitation resolve op after cancel"
        );
        let (server_name, request_id, decision, response_content) = saw_resolve.unwrap();
        assert_eq!(server_name, "mcp-server");
        assert_eq!(request_id, RequestId::String("request-id-1".to_string()));
        assert_eq!(decision, ElicitationAction::Cancel);
        assert_eq!(response_content, None);
    }

    #[test]
    fn elicitation_accept_requires_required_schema_fields() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(
            make_elicitation_request(
                Some(serde_json::json!({
                    "type": "object",
                    "properties": {
                        "age": {
                            "type": "integer"
                        }
                    },
                    "required": ["age"]
                })),
                None,
            ),
            tx,
            mcp_elicitations_features(),
        );

        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));

        assert!(
            view.elicitation_form
                .as_ref()
                .is_some_and(|form| form.is_editing),
            "expected form editing to start for missing required field"
        );
        let mut saw_resolve = false;
        while let Ok(ev) = rx.try_recv() {
            if matches!(ev, AppEvent::CodexOp(Op::ResolveElicitation { .. })) {
                saw_resolve = true;
                break;
            }
        }
        assert!(
            !saw_resolve,
            "accept should not resolve with missing required fields"
        );

        view.handle_key_event(KeyEvent::new(KeyCode::Char('4'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('2'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));

        let mut saw_resolve = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ResolveElicitation {
                server_name,
                request_id,
                decision,
                response_content,
            }) = ev
            {
                saw_resolve = Some((server_name, request_id, decision, response_content));
                break;
            }
        }

        assert!(
            saw_resolve.is_some(),
            "expected elicitation resolve op after required field is set"
        );
        let (server_name, request_id, decision, response_content) = saw_resolve.unwrap();
        assert_eq!(server_name, "mcp-server");
        assert_eq!(request_id, RequestId::String("request-id-1".to_string()));
        assert_eq!(decision, ElicitationAction::Accept);
        assert_eq!(response_content, Some(serde_json::json!({ "age": 42 })));
    }

    #[test]
    fn elicitation_union_type_prefers_non_null_supported_type() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(
            make_elicitation_request(
                Some(serde_json::json!({
                    "type": "object",
                    "properties": {
                        "age": {
                            "type": ["null", "integer"]
                        }
                    }
                })),
                None,
            ),
            tx,
            mcp_elicitations_features(),
        );

        view.handle_key_event(KeyEvent::new(KeyCode::Tab, KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('4'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('2'), KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Enter, KeyModifiers::NONE));
        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));

        let mut saw_resolve = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ResolveElicitation {
                server_name,
                request_id,
                decision,
                response_content,
            }) = ev
            {
                saw_resolve = Some((server_name, request_id, decision, response_content));
                break;
            }
        }

        assert!(
            saw_resolve.is_some(),
            "expected elicitation resolve op after accepting"
        );
        let (server_name, request_id, decision, response_content) = saw_resolve.unwrap();
        assert_eq!(server_name, "mcp-server");
        assert_eq!(request_id, RequestId::String("request-id-1".to_string()));
        assert_eq!(decision, ElicitationAction::Accept);
        assert_eq!(response_content, Some(serde_json::json!({ "age": 42 })));
    }

    #[test]
    fn elicitation_schema_is_ignored_when_feature_disabled() {
        let (tx_raw, mut rx) = unbounded_channel::<AppEvent>();
        let tx = AppEventSender::new(tx_raw);
        let mut view = ApprovalOverlay::new(
            make_elicitation_request(
                Some(serde_json::json!({
                    "type": "object",
                    "properties": {
                        "age": {
                            "type": "integer"
                        }
                    },
                    "required": ["age"]
                })),
                Some("https://example.com/elicitation"),
            ),
            tx,
            Features::with_defaults(),
        );

        assert!(
            view.elicitation_form.is_none(),
            "legacy behavior should not render a schema form when feature is disabled"
        );
        view.handle_key_event(KeyEvent::new(KeyCode::Char('y'), KeyModifiers::NONE));

        let mut saw_resolve = None;
        while let Ok(ev) = rx.try_recv() {
            if let AppEvent::CodexOp(Op::ResolveElicitation {
                server_name,
                request_id,
                decision,
                response_content,
            }) = ev
            {
                saw_resolve = Some((server_name, request_id, decision, response_content));
                break;
            }
        }

        assert!(
            saw_resolve.is_some(),
            "expected elicitation resolve op after accepting"
        );
        let (server_name, request_id, decision, response_content) = saw_resolve.unwrap();
        assert_eq!(server_name, "mcp-server");
        assert_eq!(request_id, RequestId::String("request-id-1".to_string()));
        assert_eq!(decision, ElicitationAction::Accept);
        assert_eq!(response_content, None);
    }
}
