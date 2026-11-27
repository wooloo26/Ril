import * as vscode from "vscode";
import {
  RilLspClient,
  SEMANTIC_LEGEND,
  toLspRange,
  toLspSeverity,
  toVscodeRange,
} from "./client.js";
import type {
  LspCodeAction,
  LspCompletionItem,
  LspCompletionList,
  LspDocumentSymbol,
  LspHover,
  LspInlayHint,
  LspLocation,
  LspPrepareRenameResult,
  LspSemanticTokens,
  LspSignatureHelp,
  LspTextEdit,
  LspWorkspaceEdit,
  LspWorkspaceSymbol,
} from "./lspTypes.js";

let activeClient: RilLspClient | null = null;
let output: vscode.OutputChannel | null = null;
let diagnostics: vscode.DiagnosticCollection | null = null;
let docExampleDecoration: vscode.TextEditorDecorationType | null = null;

const DOC_FENCE_OPEN_RE = /^\s*--\s*`{3,}\s*ril(?:,(?:no_run|ignore))?\s*$/;
const DOC_FENCE_CLOSE_RE = /^\s*--\s*`{3,}\s*$/;
const DOC_LINE_RE = /^\s*--/;

function isReadonlyArray<T>(value: readonly T[] | unknown): value is readonly T[] {
  return Array.isArray(value);
}

function updateDocExampleDecorations(editor: vscode.TextEditor | undefined): void {
  if (!docExampleDecoration || !editor || editor.document.languageId !== "ril") {
    return;
  }
  const enabled = vscode.workspace
    .getConfiguration("ril")
    .get<boolean>("docExamples.subtleHighlight", true);
  if (!enabled) {
    editor.setDecorations(docExampleDecoration, []);
    return;
  }
  const ranges: vscode.Range[] = [];
  const doc = editor.document;
  let inBlock = false;
  for (let line = 0; line < doc.lineCount; line++) {
    const text = doc.lineAt(line).text;
    if (!inBlock) {
      if (DOC_FENCE_OPEN_RE.test(text)) {
        inBlock = true;
      }
    } else if (DOC_FENCE_CLOSE_RE.test(text) || !DOC_LINE_RE.test(text)) {
      inBlock = false;
    } else {
      ranges.push(new vscode.Range(line, 0, line, text.length));
    }
  }
  editor.setDecorations(docExampleDecoration, ranges);
}

function updateAllVisibleDocDecorations(): void {
  for (const editor of vscode.window.visibleTextEditors) {
    updateDocExampleDecorations(editor);
  }
}

function toVscodeCompletionKind(kind?: number): vscode.CompletionItemKind {
  // LSP CompletionItemKind is 1-based, VS Code CompletionItemKind is 0-based.
  if (typeof kind === "number" && kind >= 1) {
    return (kind - 1) as vscode.CompletionItemKind;
  }
  return vscode.CompletionItemKind.Text;
}

function toVscodeSymbolKind(kind?: number): vscode.SymbolKind {
  // LSP SymbolKind is 1-based, VS Code SymbolKind is 0-based.
  if (typeof kind === "number" && kind >= 1) {
    return (kind - 1) as vscode.SymbolKind;
  }
  return vscode.SymbolKind.Variable;
}

function toVscodeDocumentSymbol(sym: LspDocumentSymbol): vscode.DocumentSymbol {
  const ds = new vscode.DocumentSymbol(
    sym.name ?? "",
    sym.detail ?? "",
    toVscodeSymbolKind(sym.kind),
    toVscodeRange(sym.range),
    toVscodeRange(sym.selectionRange ?? sym.range)
  );
  if (isReadonlyArray(sym.children)) {
    ds.children = sym.children.map(toVscodeDocumentSymbol);
  }
  return ds;
}

function toVscodeWorkspaceEdit(lspEdit: LspWorkspaceEdit | null | undefined): vscode.WorkspaceEdit {
  const edit = new vscode.WorkspaceEdit();
  if (lspEdit?.changes) {
    for (const [uriStr, edits] of Object.entries(lspEdit.changes)) {
      const uri = vscode.Uri.parse(uriStr);
      if (isReadonlyArray(edits)) {
        for (const e of edits) {
          if (e?.range && typeof e.newText === "string") {
            edit.replace(uri, toVscodeRange(e.range), e.newText);
          }
        }
      }
    }
  }
  return edit;
}

async function startClient(): Promise<void> {
  if (activeClient) {
    await activeClient.stop();
    activeClient = null;
  }
  if (!output || !diagnostics) {
    return;
  }
  const folders = vscode.workspace.workspaceFolders;
  const workspaceRoot = folders?.[0]?.uri.fsPath ?? null;
  const client = new RilLspClient(workspaceRoot, output, diagnostics);
  activeClient = client;
  try {
    await client.start();
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    output.appendLine(`[ril-lsp] failed to start: ${msg}`);
    void vscode.window.showWarningMessage(
      `Ril Language Server failed to start: ${msg}`
    );
  }
}

async function ensureReady(): Promise<RilLspClient | null> {
  if (!activeClient?.proc) {
    return null;
  }
  if (activeClient.ready) {
    await activeClient.ready;
  }
  return activeClient?.proc ? activeClient : null;
}

export function activate(context: vscode.ExtensionContext): void {
  output = vscode.window.createOutputChannel("Ril Language Server");
  diagnostics = vscode.languages.createDiagnosticCollection("ril");
  docExampleDecoration = vscode.window.createTextEditorDecorationType({
    isWholeLine: true,
    backgroundColor: "rgba(128, 128, 128, 0.06)",
    opacity: "0.82",
  });
  context.subscriptions.push(output, diagnostics, docExampleDecoration);

  const selector: vscode.DocumentSelector = { language: "ril" };

  context.subscriptions.push(
    vscode.commands.registerCommand("ril.restartServer", async () => {
      diagnostics?.clear();
      await startClient();
    }),
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      updateDocExampleDecorations(editor);
    }),
    vscode.window.onDidChangeVisibleTextEditors(() => {
      updateAllVisibleDocDecorations();
    }),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("ril")) {
        updateAllVisibleDocDecorations();
        if (activeClient?.initialized) {
          activeClient.didChangeConfiguration();
        }
      }
    }),
    vscode.workspace.onDidOpenTextDocument((doc) => {
      if (doc.languageId === "ril" && activeClient?.initialized) {
        activeClient.didOpen(doc);
      }
    }),
    vscode.workspace.onDidChangeTextDocument((event) => {
      if (event.document.languageId === "ril") {
        for (const editor of vscode.window.visibleTextEditors) {
          if (editor.document === event.document) {
            updateDocExampleDecorations(editor);
          }
        }
        if (activeClient?.initialized) {
          activeClient.didChange(event.document);
        }
      }
    }),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      if (doc.languageId === "ril") {
        diagnostics?.delete(doc.uri);
        if (activeClient?.initialized) {
          activeClient.didClose(doc);
        }
      }
    }),
    vscode.languages.registerCompletionItemProvider(
      selector,
      {
        async provideCompletionItems(doc, position, _token, ctx) {
          try {
            const client = await ensureReady();
            if (!client) return [];
            const res = await client.request<LspCompletionItem[] | LspCompletionList | null>(
              "textDocument/completion",
              {
                textDocument: { uri: doc.uri.toString() },
                position: { line: position.line, character: position.character },
                context: {
                  triggerKind: ctx.triggerKind + 1,
                  triggerCharacter: ctx.triggerCharacter,
                },
              }
            );
            const rawItems: readonly LspCompletionItem[] = isReadonlyArray(res)
              ? res
              : res && isReadonlyArray(res.items)
              ? res.items
              : [];
            return rawItems.map((it) => {
              const item = new vscode.CompletionItem(
                it.label ?? "",
                toVscodeCompletionKind(it.kind)
              );
              if (it.detail) item.detail = it.detail;
              if (it.sortText) item.sortText = it.sortText;
              if (it.filterText) item.filterText = it.filterText;
              if (it.documentation) {
                const val =
                  typeof it.documentation === "string"
                    ? it.documentation
                    : it.documentation.value ?? "";
                if (val) item.documentation = new vscode.MarkdownString(val);
              }
              const isSnippet = it.insertTextFormat === 2;
              if (it.textEdit?.range && typeof it.textEdit.newText === "string") {
                item.range = toVscodeRange(it.textEdit.range);
                item.insertText = isSnippet
                  ? new vscode.SnippetString(it.textEdit.newText)
                  : it.textEdit.newText;
              } else if (typeof it.insertText === "string") {
                item.insertText = isSnippet
                  ? new vscode.SnippetString(it.insertText)
                  : it.insertText;
              }
              if (isReadonlyArray(it.additionalTextEdits)) {
                item.additionalTextEdits = it.additionalTextEdits
                  .filter((e): e is LspTextEdit => Boolean(e?.range && typeof e.newText === "string"))
                  .map((e) => new vscode.TextEdit(toVscodeRange(e.range), e.newText));
              }
              return item;
            });
          } catch {
            return [];
          }
        },
      },
      ".",
      ":",
      ">",
      "/",
      "@"
    ),
    vscode.languages.registerSignatureHelpProvider(
      selector,
      {
        async provideSignatureHelp(doc, position) {
          try {
            const client = await ensureReady();
            if (!client) return null;
            const res = await client.request<LspSignatureHelp | null>(
              "textDocument/signatureHelp",
              {
                textDocument: { uri: doc.uri.toString() },
                position: { line: position.line, character: position.character },
              }
            );
            if (!res || !isReadonlyArray(res.signatures) || res.signatures.length === 0) {
              return null;
            }
            const help = new vscode.SignatureHelp();
            help.activeSignature = res.activeSignature ?? 0;
            help.activeParameter = res.activeParameter ?? 0;
            help.signatures = res.signatures.map((sig) => {
              const info = new vscode.SignatureInformation(sig.label ?? "");
              if (isReadonlyArray(sig.parameters)) {
                info.parameters = sig.parameters.map(
                  (p) => new vscode.ParameterInformation(p.label ?? "")
                );
              }
              return info;
            });
            return help;
          } catch {
            return null;
          }
        },
      },
      "(",
      ","
    ),
    vscode.languages.registerDocumentSemanticTokensProvider(
      selector,
      {
        async provideDocumentSemanticTokens(doc) {
          try {
            const client = await ensureReady();
            if (!client) return null;
            const res = await client.request<LspSemanticTokens | null>(
              "textDocument/semanticTokens/full",
              {
                textDocument: { uri: doc.uri.toString() },
              }
            );
            if (!res || !isReadonlyArray(res.data)) return null;
            return new vscode.SemanticTokens(new Uint32Array(res.data));
          } catch {
            return null;
          }
        },
      },
      SEMANTIC_LEGEND
    ),
    vscode.languages.registerHoverProvider(selector, {
      async provideHover(doc, position) {
        try {
          const client = await ensureReady();
          if (!client) return null;
          const res = await client.request<LspHover | null>("textDocument/hover", {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
          });
          if (!res?.contents) return null;
          const value =
            typeof res.contents === "string"
              ? res.contents
              : res.contents.value ?? "";
          if (!value) return null;
          const md = new vscode.MarkdownString(value);
          md.isTrusted = false;
          return new vscode.Hover(md, res.range ? toVscodeRange(res.range) : undefined);
        } catch {
          return null;
        }
      },
    }),
    vscode.languages.registerDefinitionProvider(selector, {
      async provideDefinition(doc, position) {
        try {
          const client = await ensureReady();
          if (!client) return null;
          const res = await client.request<LspLocation | LspLocation[] | null>(
            "textDocument/definition",
            {
              textDocument: { uri: doc.uri.toString() },
              position: { line: position.line, character: position.character },
            }
          );
          if (!res) return null;
          const items = Array.isArray(res) ? res : [res];
          return items
            .filter((loc): loc is LspLocation => Boolean(loc?.uri && loc.range))
            .map((loc) => new vscode.Location(vscode.Uri.parse(loc.uri), toVscodeRange(loc.range)));
        } catch {
          return null;
        }
      },
    }),
    vscode.languages.registerReferenceProvider(selector, {
      async provideReferences(doc, position, ctx) {
        try {
          const client = await ensureReady();
          if (!client) return [];
          const res = await client.request<LspLocation[] | null>("textDocument/references", {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
            context: { includeDeclaration: Boolean(ctx.includeDeclaration) },
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter((loc): loc is LspLocation => Boolean(loc?.uri && loc.range))
            .map((loc) => new vscode.Location(vscode.Uri.parse(loc.uri), toVscodeRange(loc.range)));
        } catch {
          return [];
        }
      },
    }),
    vscode.languages.registerRenameProvider(selector, {
      async prepareRename(doc, position) {
        const client = await ensureReady();
        if (!client) throw new Error("Ril Language Server is not running");
        const res = await client.request<LspPrepareRenameResult | null>(
          "textDocument/prepareRename",
          {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
          }
        );
        if (!res?.range) {
          throw new Error("Cannot rename this symbol");
        }
        return {
          range: toVscodeRange(res.range),
          placeholder: res.placeholder ?? "",
        };
      },
      async provideRenameEdits(doc, position, newName) {
        try {
          const client = await ensureReady();
          if (!client) return null;
          const res = await client.request<LspWorkspaceEdit | null>("textDocument/rename", {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
            newName,
          });
          return res ? toVscodeWorkspaceEdit(res) : null;
        } catch {
          return null;
        }
      },
    }),
    vscode.languages.registerDocumentSymbolProvider(selector, {
      async provideDocumentSymbols(doc) {
        try {
          const client = await ensureReady();
          if (!client) return [];
          const res = await client.request<LspDocumentSymbol[] | null>(
            "textDocument/documentSymbol",
            {
              textDocument: { uri: doc.uri.toString() },
            }
          );
          if (!Array.isArray(res)) return [];
          return res.map(toVscodeDocumentSymbol);
        } catch {
          return [];
        }
      },
    }),
    vscode.languages.registerWorkspaceSymbolProvider({
      async provideWorkspaceSymbols(query) {
        try {
          const client = await ensureReady();
          if (!client) return [];
          const res = await client.request<LspWorkspaceSymbol[] | null>("workspace/symbol", {
            query,
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter(
              (s): s is LspWorkspaceSymbol & { location: LspLocation } =>
                Boolean(s?.location?.uri && s.location.range)
            )
            .map(
              (s) =>
                new vscode.SymbolInformation(
                  s.name ?? "",
                  toVscodeSymbolKind(s.kind),
                  "",
                  new vscode.Location(
                    vscode.Uri.parse(s.location.uri),
                    toVscodeRange(s.location.range)
                  )
                )
            );
        } catch {
          return [];
        }
      },
    }),
    vscode.languages.registerInlayHintsProvider(selector, {
      async provideInlayHints(doc, range) {
        try {
          const client = await ensureReady();
          if (!client) return [];
          const res = await client.request<LspInlayHint[] | null>("textDocument/inlayHint", {
            textDocument: { uri: doc.uri.toString() },
            range: toLspRange(range),
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter(
              (h): h is Required<Pick<LspInlayHint, "position" | "label">> & LspInlayHint =>
                Boolean(h?.position && h.label)
            )
            .map((h) => {
              const hint = new vscode.InlayHint(
                new vscode.Position(h.position.line, h.position.character),
                h.label,
                h.kind === 1
                  ? vscode.InlayHintKind.Type
                  : vscode.InlayHintKind.Parameter
              );
              hint.paddingLeft = Boolean(h.paddingLeft);
              hint.paddingRight = Boolean(h.paddingRight);
              return hint;
            });
        } catch {
          return [];
        }
      },
    }),
    vscode.languages.registerCodeActionsProvider(
      selector,
      {
        async provideCodeActions(doc, range, ctx) {
          try {
            const client = await ensureReady();
            if (!client) return [];
            const res = await client.request<LspCodeAction[] | null>("textDocument/codeAction", {
              textDocument: { uri: doc.uri.toString() },
              range: toLspRange(range),
              context: {
                diagnostics: (ctx.diagnostics ?? []).map((d) => ({
                  range: toLspRange(d.range),
                  severity: toLspSeverity(d.severity),
                  code: d.code,
                  source: d.source,
                  message: d.message,
                })),
              },
            });
            if (!Array.isArray(res)) return [];
            return res.map((a) => {
              const action = new vscode.CodeAction(
                a.title ?? "Quick Fix",
                vscode.CodeActionKind.QuickFix
              );
              action.isPreferred = Boolean(a.isPreferred);
              if (a.edit) {
                action.edit = toVscodeWorkspaceEdit(a.edit);
              }
              return action;
            });
          } catch {
            return [];
          }
        },
      },
      { providedCodeActionKinds: [vscode.CodeActionKind.QuickFix] }
    ),
    vscode.languages.registerDocumentFormattingEditProvider(selector, {
      async provideDocumentFormattingEdits(doc, options) {
        try {
          const client = await ensureReady();
          if (!client) return [];
          const res = await client.request<LspTextEdit[] | null>("textDocument/formatting", {
            textDocument: { uri: doc.uri.toString() },
            options: {
              tabSize: options.tabSize,
              insertSpaces: options.insertSpaces,
            },
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter((edit): edit is LspTextEdit => Boolean(edit?.range && typeof edit.newText === "string"))
            .map((edit) => new vscode.TextEdit(toVscodeRange(edit.range), edit.newText));
        } catch {
          return [];
        }
      },
    })
  );

  updateAllVisibleDocDecorations();
  void startClient();
}

export async function deactivate(): Promise<void> {
  if (activeClient) {
    await activeClient.stop();
    activeClient = null;
  }
}
