export interface LspPosition {
  readonly line: number;
  readonly character: number;
}

export interface LspRange {
  readonly start: LspPosition;
  readonly end: LspPosition;
}

export interface LspLocation {
  readonly uri: string;
  readonly range: LspRange;
}

export interface LspTextEdit {
  readonly range: LspRange;
  readonly newText: string;
}

export interface LspWorkspaceEdit {
  readonly changes?: Readonly<Record<string, readonly LspTextEdit[]>>;
}

export interface LspDiagnostic {
  readonly range: LspRange;
  readonly severity?: number;
  readonly code?: string | number | null;
  readonly source?: string;
  readonly message?: string;
}

export interface LspPublishDiagnosticsParams {
  readonly uri: string;
  readonly diagnostics?: readonly LspDiagnostic[];
}

export interface LspMarkupContent {
  readonly kind?: string;
  readonly value?: string;
}

export interface LspCompletionItem {
  readonly label?: string;
  readonly kind?: number;
  readonly detail?: string;
  readonly sortText?: string;
  readonly filterText?: string;
  readonly documentation?: string | LspMarkupContent;
  readonly insertTextFormat?: number;
  readonly insertText?: string;
  readonly textEdit?: LspTextEdit;
  readonly additionalTextEdits?: readonly LspTextEdit[];
}

export interface LspCompletionList {
  readonly items?: readonly LspCompletionItem[];
}

export interface LspParameterInformation {
  readonly label?: string;
}

export interface LspSignatureInformation {
  readonly label?: string;
  readonly parameters?: readonly LspParameterInformation[];
}

export interface LspSignatureHelp {
  readonly signatures?: readonly LspSignatureInformation[];
  readonly activeSignature?: number;
  readonly activeParameter?: number;
}

export interface LspSemanticTokens {
  readonly data?: readonly number[];
}

export interface LspHover {
  readonly contents?: string | LspMarkupContent;
  readonly range?: LspRange;
}

export interface LspPrepareRenameResult {
  readonly range?: LspRange;
  readonly placeholder?: string;
}

export interface LspDocumentSymbol {
  readonly name?: string;
  readonly detail?: string;
  readonly kind?: number;
  readonly range: LspRange;
  readonly selectionRange?: LspRange;
  readonly children?: readonly LspDocumentSymbol[];
}

export interface LspWorkspaceSymbol {
  readonly name?: string;
  readonly kind?: number;
  readonly location?: LspLocation;
}

export interface LspInlayHint {
  readonly position?: LspPosition;
  readonly label?: string;
  readonly kind?: number;
  readonly paddingLeft?: boolean;
  readonly paddingRight?: boolean;
}

export interface LspCodeAction {
  readonly title?: string;
  readonly isPreferred?: boolean;
  readonly edit?: LspWorkspaceEdit;
}

export interface JsonRpcError {
  readonly code?: number;
  readonly message?: string;
}

export interface JsonRpcMessage {
  readonly jsonrpc?: string;
  readonly id?: number;
  readonly method?: string;
  readonly params?: unknown;
  readonly result?: unknown;
  readonly error?: JsonRpcError;
}

export interface RilSettings {
  readonly dotToPipe: boolean;
  readonly autoImport: boolean;
  readonly inlayHints: boolean;
}
