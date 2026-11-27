#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
EXT_NAME="ril-local.ril-lang-0.1.0"
INSTALLED=0

if [ ! -d "$SCRIPT_DIR/node_modules" ]; then
    (cd "$SCRIPT_DIR" && pnpm install --frozen-lockfile)
fi
(cd "$SCRIPT_DIR" && pnpm run build)

for ext_root in \
    "$HOME/.vscode-server/extensions" \
    "$HOME/.vscode/extensions" \
    "$HOME/.vscode-insiders/extensions" \
    "$HOME/.vscode-server-insiders/extensions"
do
    if [ -d "$ext_root" ]; then
        target="$ext_root/$EXT_NAME"
        rm -rf "$target"
        ln -s "$SCRIPT_DIR" "$target"
        echo "Linked $target -> $SCRIPT_DIR"
        INSTALLED=1
    fi
done

if [ "$INSTALLED" -eq 0 ]; then
    mkdir -p "$HOME/.vscode/extensions"
    target="$HOME/.vscode/extensions/$EXT_NAME"
    ln -s "$SCRIPT_DIR" "$target"
    echo "Linked $target -> $SCRIPT_DIR"
fi

echo "Done! Reload VS Code (Developer: Reload Window) to activate Ril syntax highlighting and ril lsp."
