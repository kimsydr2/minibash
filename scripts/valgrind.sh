#!/usr/bin/env bash
set -euo pipefail
BIN="${1:-./src/minibash}"
SCRIPT="${2:-/dev/null}"
if ! command -v valgrind >/dev/null 2>&1; then
  echo "valgrind not found in PATH" >&2
  exit 1
fi
valgrind --leak-check=full --show-leak-kinds=all --error-exitcode=1 "$BIN" < "$SCRIPT"
