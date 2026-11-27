import * as cp from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as vscode from "vscode";
import type {
  JsonRpcMessage,
  LspPublishDiagnosticsParams,
  LspRange,
  RilSettings,
} from "./lspTypes.js";

export const SEMANTIC_TOKEN_TYPES = [
  "namespace",
  "type",
  "typeParameter",
  "function",
  "parameter",
  "variable",
  "property",
  "enumMember",
  "macro",
] as const;

export const SEMANTIC_TOKEN_MODIFIERS = [
  "declaration",
  "readonly",
  "modification",
  "defaultLibrary",
] as const;

export const SEMANTIC_LEGEND = new vscode.SemanticTokensLegend(
  [...SEMANTIC_TOKEN_TYPES],
  [...SEMANTIC_TOKEN_MODIFIERS]
);

interface ServerCommand {
  readonly command: string;
  readonly args: readonly string[];
  readonly cwd?: string;
}

interface PendingRequest {
  readonly resolve: (value: unknown) => void;
  readonly reject: (err: Error) => void;
}

function isExecutable(filePath: string): boolean {
  try {
    fs.accessSync(filePath, fs.constants.X_OK);
    return fs.statSync(filePath).isFile();
  } catch {
    return false;
  }
}

function resolveCargoBinary(): string {
  const ext = process.platform === "win32" ? ".exe" : "";
  const homeCargo = path.join(os.homedir(), ".cargo", "bin", `cargo${ext}`);
  if (isExecutable(homeCargo)) {
    return homeCargo;
  }
  return "cargo";
}

export function readRilSettings(): RilSettings {
  const cfg = vscode.workspace.getConfiguration("ril");
  return {
    dotToPipe: cfg.get<boolean>("completion.dotToPipe", true),
    autoImport: cfg.get<boolean>("completion.autoImport", true),
    inlayHints: cfg.get<boolean>("inlayHints.enable", true),
  };
}

function makeServerCommand(
  command: string,
  args: readonly string[],
  workspaceRoot: string | null
): ServerCommand {
  return workspaceRoot !== null
    ? { command, args, cwd: workspaceRoot }
    : { command, args };
}

function resolveServerCommand(workspaceRoot: string | null): ServerCommand {
  const cfg = vscode.workspace.getConfiguration("ril");
  const configured = (cfg.get<string>("serverPath") ?? "").trim();
  if (configured) {
    const args = cfg.get<string[]>("serverArgs");
    return makeServerCommand(
      configured,
      Array.isArray(args) ? args : ["lsp"],
      workspaceRoot
    );
  }

  const ext = process.platform === "win32" ? ".exe" : "";
  if (workspaceRoot !== null) {
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
    return makeServerCommand(homeRil, ["lsp"], workspaceRoot);
  }

  return makeServerCommand("ril", ["lsp"], workspaceRoot);
}

export function toVscodeRange(range: LspRange): vscode.Range {
  return new vscode.Range(
    range.start.line,
    range.start.character,
    range.end.line,
    range.end.character
  );
}

export function toLspRange(range: vscode.Range): LspRange {
  return {
    start: { line: range.start.line, character: range.start.character },
    end: { line: range.end.line, character: range.end.character },
  };
}

export function toVscodeSeverity(severity?: number): vscode.DiagnosticSeverity {
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

export function toLspSeverity(severity: vscode.DiagnosticSeverity): number {
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

export class RilLspClient {
  public proc: cp.ChildProcessWithoutNullStreams | null = null;
  public ready: Promise<void> | null = null;
  public initialized = false;
  public disposed = false;

  private readonly workspaceRoot: string | null;
  private readonly out: vscode.OutputChannel;
  private readonly diagnostics: vscode.DiagnosticCollection;
  private buffer: Buffer = Buffer.alloc(0);
  private nextId = 1;
  private readonly pending = new Map<number, PendingRequest>();

  constructor(
    workspaceRoot: string | null,
    out: vscode.OutputChannel,
    diagnostics: vscode.DiagnosticCollection
  ) {
    this.workspaceRoot = workspaceRoot;
    this.out = out;
    this.diagnostics = diagnostics;
  }

  async start(): Promise<void> {
    const spec = resolveServerCommand(this.workspaceRoot);
    this.out.appendLine(
      `[ril-lsp] starting: ${spec.command} ${spec.args.join(" ")} (cwd=${spec.cwd ?? "<none>"})`
    );

    const env: NodeJS.ProcessEnv = { ...process.env };
    const cargoBin = path.join(os.homedir(), ".cargo", "bin");
    const currentPath = env["PATH"] ?? "";
    if (fs.existsSync(cargoBin) && !currentPath.includes(cargoBin)) {
      env["PATH"] = `${cargoBin}${path.delimiter}${currentPath}`;
    }

    const spawnOpts: cp.SpawnOptionsWithoutStdio =
      spec.cwd !== undefined
        ? { cwd: spec.cwd, env, stdio: ["pipe", "pipe", "pipe"] }
        : { env, stdio: ["pipe", "pipe", "pipe"] };

    const child = cp.spawn(spec.command, spec.args, spawnOpts);
    this.proc = child;

    child.stdout.on("data", (chunk: Buffer) => this.onData(chunk));
    child.stderr.on("data", (chunk: Buffer) => {
      this.out.append(chunk.toString("utf8"));
    });
    child.on("error", (err: Error) => {
      this.out.appendLine(`[ril-lsp] process error: ${err.message}`);
      this.rejectAll(err);
    });
    child.on("exit", (code: number | null, signal: NodeJS.Signals | null) => {
      this.out.appendLine(`[ril-lsp] exited (code=${String(code)}, signal=${String(signal)})`);
      this.rejectAll(new Error(`ril lsp exited (${String(code)})`));
      this.proc = null;
      this.initialized = false;
    });

    const rootUri =
      this.workspaceRoot !== null
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

  private rejectAll(err: Error): void {
    for (const entry of this.pending.values()) {
      entry.reject(err);
    }
    this.pending.clear();
  }

  private sendRaw(payload: unknown): boolean {
    if (!this.proc?.stdin.writable) {
      return false;
    }
    const body = Buffer.from(JSON.stringify(payload), "utf8");
    const header = Buffer.from(`Content-Length: ${String(body.length)}\r\n\r\n`, "ascii");
    this.proc.stdin.write(Buffer.concat([header, body]));
    return true;
  }

  request<T = unknown>(method: string, params: unknown): Promise<T> {
    const id = this.nextId++;
    return new Promise<T>((resolve, reject) => {
      this.pending.set(id, {
        resolve: resolve as (value: unknown) => void,
        reject,
      });
      const sent = this.sendRaw({ jsonrpc: "2.0", id, method, params });
      if (!sent) {
        this.pending.delete(id);
        reject(new Error("ril lsp process is not running"));
      }
    });
  }

  notify(method: string, params: unknown): void {
    this.sendRaw({ jsonrpc: "2.0", method, params });
  }

  private onData(chunk: Buffer): void {
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (true) {
      const headerEnd = this.buffer.indexOf("\r\n\r\n");
      if (headerEnd === -1) {
        return;
      }
      const headerText = this.buffer.subarray(0, headerEnd).toString("ascii");
      const match = /Content-Length:\s*(\d+)/i.exec(headerText);
      const lengthStr = match?.[1];
      if (lengthStr === undefined) {
        this.buffer = this.buffer.subarray(headerEnd + 4);
        continue;
      }
      const length = Number.parseInt(lengthStr, 10);
      const total = headerEnd + 4 + length;
      if (this.buffer.length < total) {
        return;
      }
      const bodyText = this.buffer.subarray(headerEnd + 4, total).toString("utf8");
      this.buffer = this.buffer.subarray(total);
      let message: JsonRpcMessage;
      try {
        message = JSON.parse(bodyText) as JsonRpcMessage;
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        this.out.appendLine(`[ril-lsp] invalid JSON: ${msg}`);
        continue;
      }
      this.handleMessage(message);
    }
  }

  private handleMessage(message: JsonRpcMessage): void {
    if (message.id !== undefined) {
      const entry = this.pending.get(message.id);
      if (entry !== undefined) {
        this.pending.delete(message.id);
        if (message.error !== undefined) {
          entry.reject(new Error(message.error.message ?? "LSP request failed"));
        } else {
          entry.resolve(message.result);
        }
        return;
      }
    }

    if (message.method === "textDocument/publishDiagnostics" && message.params !== undefined) {
      const params = message.params as LspPublishDiagnosticsParams;
      const uri = vscode.Uri.parse(params.uri);
      const items = (params.diagnostics ?? []).map((d) => {
        const diag = new vscode.Diagnostic(
          toVscodeRange(d.range),
          d.message ?? "",
          toVscodeSeverity(d.severity)
        );
        if (d.code !== undefined && d.code !== null) {
          diag.code = d.code;
        }
        diag.source = d.source ?? "ril";
        return diag;
      });
      this.diagnostics.set(uri, items);
    }
  }

  didOpen(doc: vscode.TextDocument): void {
    this.notify("textDocument/didOpen", {
      textDocument: {
        uri: doc.uri.toString(),
        languageId: "ril",
        version: doc.version,
        text: doc.getText(),
      },
    });
  }

  didChange(doc: vscode.TextDocument): void {
    this.notify("textDocument/didChange", {
      textDocument: {
        uri: doc.uri.toString(),
        version: doc.version,
      },
      contentChanges: [{ text: doc.getText() }],
    });
  }

  didClose(doc: vscode.TextDocument): void {
    this.notify("textDocument/didClose", {
      textDocument: { uri: doc.uri.toString() },
    });
  }

  didChangeConfiguration(): void {
    this.notify("workspace/didChangeConfiguration", {
      settings: { ril: readRilSettings() },
    });
  }

  async stop(): Promise<void> {
    this.disposed = true;
    this.initialized = false;
    if (!this.proc) {
      return;
    }
    try {
      await Promise.race([
        this.request("shutdown", null),
        new Promise<void>((resolve) => setTimeout(resolve, 1000)),
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
