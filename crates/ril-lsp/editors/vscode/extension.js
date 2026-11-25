"use strict";

const vscode = require("vscode");
const cp = require("child_process");
const fs = require("fs");
const os = require("os");
const path = require("path");

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
    });

    const rootUri = this.workspaceRoot
      ? vscode.Uri.file(this.workspaceRoot).toString()
      : null;

    this.ready = this.request("initialize", {
      processId: process.pid,
      rootUri,
      capabilities: {},
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

  async stop() {
    this.disposed = true;
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
      }
    }),
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
