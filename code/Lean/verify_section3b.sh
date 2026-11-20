#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
exec bash verify_section3a_endgame.sh --section3b-only "$@"
