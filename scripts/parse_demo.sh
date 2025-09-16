
set -euo pipefail
FILE="${1:-tests/001-comment.sh}"
if ! command -v tree-sitter >/dev/null 2>&1; then
  echo "tree-sitter CLI not found. Try: source env.sh; export PATH=~cs3214/bin:\$PATH" >&2
  exit 1
fi
tree-sitter parse "$FILE"
