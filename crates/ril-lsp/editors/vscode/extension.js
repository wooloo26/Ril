"use strict";

const vscode = require("vscode");
const cp = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");

const SEMANTIC_TOKEN_TYPES = [
  "namespace",
  "type",
  "typeParameter",
  "function",
  "parameter",
  "variable",
  "property",
  "enumMember",
  "macro",
];

const SEMANTIC_TOKEN_MODIFIERS = [
  "declaration",
  "readonly",
  "modification",
  "defaultLibrary",
];

const SEMANTIC_LEGEND = new vscode.SemanticTokensLegend(
  SEMANTIC_TOKEN_TYPES,
  SEMANTIC_TOKEN_MODIFIERS
);

/** @type {RilLspClient | null} */
let activeClient = null;
/** @type {vscode.OutputChannel | null} */
let output = null;
/** @type {vscode.DiagnosticCollection | null} */
let diagnostics = null;

function isExecutable(filePath) {
  try {
    fs.accessSync(filePath, fs.constants.X_OK);
    return fs.statSync(filePath).isFile();
  } catch {
    return false;
  }
}

function resolveCargoBinary() {
  const ext = process.platform === "win32" ? ".exe" : "";
  const homeCargo = path.join(os.homedir(), ".cargo", "bin", `cargo${ext}`);
  if (isExecutable(homeCargo)) {
    return homeCargo;
  }
  return "cargo";
}

function readRilSettings() {
  const cfg = vscode.workspace.getConfiguration("ril");
  return {
    dotToPipe: cfg.get("completion.dotToPipe", true),
    autoImport: cfg.get("completion.autoImport", true),
    inlayHints: cfg.get("inlayHints.enable", true),
  };
}

function resolveServerCommand(workspaceRoot) {
  const cfg = vscode.workspace.getConfiguration("ril");
  const configured = (cfg.get("serverPath") || "").trim();
  if (configured) {
    const args = cfg.get("serverArgs");
    return {
      command: configured,
      args: Array.isArray(args) ? args : ["lsp"],
      cwd: workspaceRoot || undefined,
    };
  }

  const ext = process.platform === "win32" ? ".exe" : "";
  if (workspaceRoot) {
    const candidates = [
      path.join(workspaceRoot, "target", "debug", `ril${ext}`),
      path.join(workspaceRoot, "target", "release", `ril${ext}`),
    ];
    for (const candidate of candidates) {
      if (isExecutable(candidate)) {
        return { command: candidate, args: ["lsp"], cwd: workspaceRoot };
      }
    }
    if (
      fs.existsSync(path.join(workspaceRoot, "Cargo.toml")) &&
      fs.existsSync(path.join(workspaceRoot, "crates", "ril-cli"))
    ) {
      return {
        command: resolveCargoBinary(),
        args: ["run", "--quiet", "-p", "ril-cli", "--bin", "ril", "--", "lsp"],
        cwd: workspaceRoot,
      };
    }
  }

  const homeRil = path.join(os.homedir(), ".cargo", "bin", `ril${ext}`);
  if (isExecutable(homeRil)) {
    return { command: homeRil, args: ["lsp"], cwd: workspaceRoot || undefined };
  }

  return { command: "ril", args: ["lsp"], cwd: workspaceRoot || undefined };
}

function toVscodeRange(range) {
  return new vscode.Range(
    range.start.line,
    range.start.character,
    range.end.line,
    range.end.character
  );
}

function toLspRange(range) {
  return {
    start: { line: range.start.line, character: range.start.character },
    end: { line: range.end.line, character: range.end.character },
  };
}

function toVscodeSeverity(severity) {
  switch (severity) {
    case 1:
      return vscode.DiagnosticSeverity.Error;
    case 2:
      return vscode.DiagnosticSeverity.Warning;
    case 3:
      return vscode.DiagnosticSeverity.Information;
    case 4:
      return vscode.DiagnosticSeverity.Hint;
    default:
      return vscode.DiagnosticSeverity.Error;
  }
}

function toLspSeverity(severity) {
  switch (severity) {
    case vscode.DiagnosticSeverity.Error:
      return 1;
    case vscode.DiagnosticSeverity.Warning:
      return 2;
    case vscode.DiagnosticSeverity.Information:
      return 3;
    case vscode.DiagnosticSeverity.Hint:
      return 4;
    default:
      return 1;
  }
}

function toVscodeCompletionKind(kind) {
  // LSP CompletionItemKind is 1-based, VS Code CompletionItemKind is 0-based.
  if (typeof kind === "number" && kind >= 1) {
    return kind - 1;
  }
  return vscode.CompletionItemKind.Text;
}

function toVscodeSymbolKind(kind) {
  // LSP SymbolKind is 1-based, VS Code SymbolKind is 0-based.
  if (typeof kind === "number" && kind >= 1) {
    return kind - 1;
  }
  return vscode.SymbolKind.Variable;
}

function toVscodeDocumentSymbol(sym) {
  const ds = new vscode.DocumentSymbol(
    sym.name || "",
    sym.detail || "",
    toVscodeSymbolKind(sym.kind),
    toVscodeRange(sym.range),
    toVscodeRange(sym.selectionRange || sym.range)
  );
  if (Array.isArray(sym.children)) {
    ds.children = sym.children.map(toVscodeDocumentSymbol);
  }
  return ds;
}

function toVscodeWorkspaceEdit(lspEdit) {
  const edit = new vscode.WorkspaceEdit();
  if (lspEdit && lspEdit.changes) {
    for (const [uriStr, edits] of Object.entries(lspEdit.changes)) {
      const uri = vscode.Uri.parse(uriStr);
      if (Array.isArray(edits)) {
        for (const e of edits) {
          if (e && e.range && typeof e.newText === "string") {
            edit.replace(uri, toVscodeRange(e.range), e.newText);
          }
        }
      }
    }
  }
  return edit;
}

class RilLspClient {
  constructor(workspaceRoot, out, diagCollection) {
    this.workspaceRoot = workspaceRoot;
    this.out = out;
    this.diagnostics = diagCollection;
    this.proc = null;
    this.buffer = Buffer.alloc(0);
    this.nextId = 1;
    this.pending = new Map();
    this.ready = null;
    this.initialized = false;
    this.disposed = false;
  }

  async start() {
    const spec = resolveServerCommand(this.workspaceRoot);
    this.out.appendLine(
      `[ril-lsp] starting: ${spec.command} ${spec.args.join(" ")} (cwd=${spec.cwd || "<none>"})`
    );

    const env = { ...process.env };
    const cargoBin = path.join(os.homedir(), ".cargo", "bin");
    if (fs.existsSync(cargoBin) && !(env.PATH || "").includes(cargoBin)) {
      env.PATH = `${cargoBin}${path.delimiter}${env.PATH || ""}`;
    }

    this.proc = cp.spawn(spec.command, spec.args, {
      cwd: spec.cwd,
      env,
      stdio: ["pipe", "pipe", "pipe"],
    });

    this.proc.stdout.on("data", (chunk) => this.onData(chunk));
    this.proc.stderr.on("data", (chunk) => {
      this.out.append(chunk.toString("utf8"));
    });
    this.proc.on("error", (err) => {
      this.out.appendLine(`[ril-lsp] process error: ${err.message}`);
      this.rejectAll(err);
    });
    this.proc.on("exit", (code, signal) => {
      this.out.appendLine(`[ril-lsp] exited (code=${code}, signal=${signal})`);
      this.rejectAll(new Error(`ril lsp exited (${code})`));
      this.proc = null;
      this.initialized = false;
    });

    const rootUri = this.workspaceRoot
      ? vscode.Uri.file(this.workspaceRoot).toString()
      : null;

    this.ready = this.request("initialize", {
      processId: process.pid,
      rootUri,
      initializationOptions: readRilSettings(),
      capabilities: {
        textDocument: {
          completion: {
            completionItem: { snippetSupport: true },
          },
          semanticTokens: {
            requests: { full: true },
            tokenTypes: SEMANTIC_TOKEN_TYPES,
            tokenModifiers: SEMANTIC_TOKEN_MODIFIERS,
          },
        },
      },
    }).then(() => {
      this.notify("initialized", {});
      this.initialized = true;
      for (const doc of vscode.workspace.textDocuments) {
        if (doc.languageId === "ril") {
          this.didOpen(doc);
        }
      }
    });

    await this.ready;
  }

  rejectAll(err) {
    for (const [, entry] of this.pending) {
      entry.reject(err);
    }
    this.pending.clear();
  }

  sendRaw(payload) {
    if (!this.proc || !this.proc.stdin || !this.proc.stdin.writable) {
      return false;
    }
    const body = Buffer.from(JSON.stringify(payload), "utf8");
    const header = Buffer.from(`Content-Length: ${body.length}\r\n\r\n`, "ascii");
    this.proc.stdin.write(Buffer.concat([header, body]));
    return true;
  }

  request(method, params) {
    const id = this.nextId++;
    return new Promise((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      const sent = this.sendRaw({ jsonrpc: "2.0", id, method, params });
      if (!sent) {
        this.pending.delete(id);
        reject(new Error("ril lsp process is not running"));
      }
    });
  }

  notify(method, params) {
    this.sendRaw({ jsonrpc: "2.0", method, params });
  }

  onData(chunk) {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (true) {
      const headerEnd = this.buffer.indexOf("\r\n\r\n");
      if (headerEnd === -1) {
        return;
      }
      const headerText = this.buffer.slice(0, headerEnd).toString("ascii");
      const match = /Content-Length:\s*(\d+)/i.exec(headerText);
      if (!match) {
        this.buffer = this.buffer.slice(headerEnd + 4);
        continue;
      }
      const length = parseInt(match[1], 10);
      const total = headerEnd + 4 + length;
      if (this.buffer.length < total) {
        return;
      }
      const bodyText = this.buffer.slice(headerEnd + 4, total).toString("utf8");
      this.buffer = this.buffer.slice(total);
      let message;
      try {
        message = JSON.parse(bodyText);
      } catch (err) {
        this.out.appendLine(`[ril-lsp] invalid JSON: ${err.message}`);
        continue;
      }
      this.handleMessage(message);
    }
  }

  handleMessage(message) {
    if (message.id !== undefined && this.pending.has(message.id)) {
      const entry = this.pending.get(message.id);
      this.pending.delete(message.id);
      if (message.error) {
        entry.reject(new Error(message.error.message || "LSP request failed"));
      } else {
        entry.resolve(message.result);
      }
      return;
    }

    if (message.method === "textDocument/publishDiagnostics" && message.params) {
      const uri = vscode.Uri.parse(message.params.uri);
      const items = (message.params.diagnostics || []).map((d) => {
        const diag = new vscode.Diagnostic(
          toVscodeRange(d.range),
          d.message || "",
          toVscodeSeverity(d.severity)
        );
        if (d.code !== undefined && d.code !== null) {
          diag.code = d.code;
        }
        diag.source = d.source || "ril";
        return diag;
      });
      this.diagnostics.set(uri, items);
    }
  }

  didOpen(doc) {
    this.notify("textDocument/didOpen", {
      textDocument: {
        uri: doc.uri.toString(),
        languageId: "ril",
        version: doc.version,
        text: doc.getText(),
      },
    });
  }

  didChange(doc) {
    this.notify("textDocument/didChange", {
      textDocument: {
        uri: doc.uri.toString(),
        version: doc.version,
      },
      contentChanges: [{ text: doc.getText() }],
    });
  }

  didClose(doc) {
    this.notify("textDocument/didClose", {
      textDocument: { uri: doc.uri.toString() },
    });
  }

  didChangeConfiguration() {
    this.notify("workspace/didChangeConfiguration", {
      settings: { ril: readRilSettings() },
    });
  }

  async stop() {
    this.disposed = true;
    this.initialized = false;
    if (!this.proc) {
      return;
    }
    try {
      await Promise.race([
        this.request("shutdown", null),
        new Promise((resolve) => setTimeout(resolve, 1000)),
      ]);
      this.notify("exit", null);
    } catch {
      // Ignore shutdown errors on already-exited server.
    }
    if (this.proc) {
      this.proc.kill();
      this.proc = null;
    }
  }
}

async function startClient() {
  if (activeClient) {
    await activeClient.stop();
    activeClient = null;
  }
  const folders = vscode.workspace.workspaceFolders;
  const workspaceRoot = folders && folders.length > 0 ? folders[0].uri.fsPath : null;
  const client = new RilLspClient(workspaceRoot, output, diagnostics);
  activeClient = client;
  try {
    await client.start();
  } catch (err) {
    output.appendLine(`[ril-lsp] failed to start: ${err.message}`);
    vscode.window.showWarningMessage(
      `Ril Language Server failed to start: ${err.message}`
    );
  }
}

async function ensureReady() {
  if (!activeClient || !activeClient.proc) {
    return null;
  }
  if (activeClient.ready) {
    await activeClient.ready;
  }
  return activeClient && activeClient.proc ? activeClient : null;
}

function activate(context) {
  output = vscode.window.createOutputChannel("Ril Language Server");
  diagnostics = vscode.languages.createDiagnosticCollection("ril");
  context.subscriptions.push(output, diagnostics);

  const selector = { language: "ril" };

  context.subscriptions.push(
    vscode.commands.registerCommand("ril.restartServer", async () => {
      diagnostics.clear();
      await startClient();
    }),
    vscode.workspace.onDidChangeConfiguration((e) => {
      if (e.affectsConfiguration("ril") && activeClient && activeClient.initialized) {
        activeClient.didChangeConfiguration();
      }
    }),
    vscode.workspace.onDidOpenTextDocument((doc) => {
      if (doc.languageId === "ril" && activeClient && activeClient.initialized) {
        activeClient.didOpen(doc);
      }
    }),
    vscode.workspace.onDidChangeTextDocument((event) => {
      if (event.document.languageId === "ril" && activeClient && activeClient.initialized) {
        activeClient.didChange(event.document);
      }
    }),
    vscode.workspace.onDidCloseTextDocument((doc) => {
      if (doc.languageId === "ril") {
        diagnostics.delete(doc.uri);
        if (activeClient && activeClient.initialized) {
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
            const res = await client.request("textDocument/completion", {
              textDocument: { uri: doc.uri.toString() },
              position: { line: position.line, character: position.character },
              context: {
                triggerKind: ctx.triggerKind + 1,
                triggerCharacter: ctx.triggerCharacter,
              },
            });
            const rawItems = Array.isArray(res)
              ? res
              : res && Array.isArray(res.items)
              ? res.items
              : [];
            return rawItems.map((it) => {
              const item = new vscode.CompletionItem(
                it.label || "",
                toVscodeCompletionKind(it.kind)
              );
              if (it.detail) item.detail = it.detail;
              if (it.sortText) item.sortText = it.sortText;
              if (it.filterText) item.filterText = it.filterText;
              if (it.documentation) {
                const val =
                  typeof it.documentation === "string"
                    ? it.documentation
                    : it.documentation.value || "";
                if (val) item.documentation = new vscode.MarkdownString(val);
              }
              const isSnippet = it.insertTextFormat === 2;
              if (it.textEdit && it.textEdit.range && typeof it.textEdit.newText === "string") {
                item.range = toVscodeRange(it.textEdit.range);
                item.insertText = isSnippet
                  ? new vscode.SnippetString(it.textEdit.newText)
                  : it.textEdit.newText;
              } else if (typeof it.insertText === "string") {
                item.insertText = isSnippet
                  ? new vscode.SnippetString(it.insertText)
                  : it.insertText;
              }
              if (Array.isArray(it.additionalTextEdits)) {
                item.additionalTextEdits = it.additionalTextEdits
                  .filter((e) => e && e.range && typeof e.newText === "string")
                  .map(
                    (e) =>
                      new vscode.TextEdit(toVscodeRange(e.range), e.newText)
                  );
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
            const res = await client.request("textDocument/signatureHelp", {
              textDocument: { uri: doc.uri.toString() },
              position: { line: position.line, character: position.character },
            });
            if (!res || !Array.isArray(res.signatures) || res.signatures.length === 0) {
              return null;
            }
            const help = new vscode.SignatureHelp();
            help.activeSignature = res.activeSignature || 0;
            help.activeParameter = res.activeParameter || 0;
            help.signatures = res.signatures.map((sig) => {
              const info = new vscode.SignatureInformation(sig.label || "");
              if (Array.isArray(sig.parameters)) {
                info.parameters = sig.parameters.map(
                  (p) => new vscode.ParameterInformation(p.label || "")
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
            const res = await client.request("textDocument/semanticTokens/full", {
              textDocument: { uri: doc.uri.toString() },
            });
            if (!res || !Array.isArray(res.data)) return null;
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
          const res = await client.request("textDocument/hover", {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
          });
          if (!res || !res.contents) return null;
          const value =
            typeof res.contents === "string"
              ? res.contents
              : res.contents.value || "";
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
          const res = await client.request("textDocument/definition", {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
          });
          if (!res) return null;
          const items = Array.isArray(res) ? res : [res];
          return items
            .filter((loc) => loc && loc.uri && loc.range)
            .map(
              (loc) =>
                new vscode.Location(vscode.Uri.parse(loc.uri), toVscodeRange(loc.range))
            );
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
          const res = await client.request("textDocument/references", {
            textDocument: { uri: doc.uri.toString() },
            position: { line: position.line, character: position.character },
            context: { includeDeclaration: !!ctx.includeDeclaration },
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter((loc) => loc && loc.uri && loc.range)
            .map(
              (loc) =>
                new vscode.Location(vscode.Uri.parse(loc.uri), toVscodeRange(loc.range))
            );
        } catch {
          return [];
        }
      },
    }),
    vscode.languages.registerRenameProvider(selector, {
      async prepareRename(doc, position) {
        const client = await ensureReady();
        if (!client) throw new Error("Ril Language Server is not running");
        const res = await client.request("textDocument/prepareRename", {
          textDocument: { uri: doc.uri.toString() },
          position: { line: position.line, character: position.character },
        });
        if (!res || !res.range) {
          throw new Error("Cannot rename this symbol");
        }
        return {
          range: toVscodeRange(res.range),
          placeholder: res.placeholder || "",
        };
      },
      async provideRenameEdits(doc, position, newName) {
        try {
          const client = await ensureReady();
          if (!client) return null;
          const res = await client.request("textDocument/rename", {
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
          const res = await client.request("textDocument/documentSymbol", {
            textDocument: { uri: doc.uri.toString() },
          });
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
          const res = await client.request("workspace/symbol", { query });
          if (!Array.isArray(res)) return [];
          return res
            .filter((s) => s && s.location && s.location.uri && s.location.range)
            .map(
              (s) =>
                new vscode.SymbolInformation(
                  s.name || "",
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
          const res = await client.request("textDocument/inlayHint", {
            textDocument: { uri: doc.uri.toString() },
            range: toLspRange(range),
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter((h) => h && h.position && h.label)
            .map((h) => {
              const hint = new vscode.InlayHint(
                new vscode.Position(h.position.line, h.position.character),
                h.label,
                h.kind === 1
                  ? vscode.InlayHintKind.Type
                  : vscode.InlayHintKind.Parameter
              );
              hint.paddingLeft = !!h.paddingLeft;
              hint.paddingRight = !!h.paddingRight;
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
            const res = await client.request("textDocument/codeAction", {
              textDocument: { uri: doc.uri.toString() },
              range: toLspRange(range),
              context: {
                diagnostics: (ctx.diagnostics || []).map((d) => ({
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
                a.title || "Quick Fix",
                vscode.CodeActionKind.QuickFix
              );
              action.isPreferred = !!a.isPreferred;
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
          const res = await client.request("textDocument/formatting", {
            textDocument: { uri: doc.uri.toString() },
            options: {
              tabSize: options.tabSize,
              insertSpaces: options.insertSpaces,
            },
          });
          if (!Array.isArray(res)) return [];
          return res
            .filter((edit) => edit && edit.range && typeof edit.newText === "string")
            .map(
              (edit) =>
                new vscode.TextEdit(toVscodeRange(edit.range), edit.newText)
            );
        } catch {
          return [];
        }
      },
    })
  );

  startClient();
}

async function deactivate() {
  if (activeClient) {
    await activeClient.stop();
    activeClient = null;
  }
}

module.exports = { activate, deactivate };
