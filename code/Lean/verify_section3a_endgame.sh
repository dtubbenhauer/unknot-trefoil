#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1 || ! command -v lean >/dev/null 2>&1; then
    echo 'Lean and Lake are required. Install the pinned lean-toolchain with elan.' >&2
    exit 2
fi
exec python3 scripts/verify.py "$@"
