#!/bin/sh
set -eu
cd "$(dirname "$0")"
exec bash verify_section3a_endgame.sh "$@"
