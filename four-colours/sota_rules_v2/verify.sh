#!/bin/sh
set -eu
cd "$(dirname "$0")"
. ./dependencies.sh
: "${PYTHON:=python3}"
"$PYTHON" -B audit.py "${1:-best_bundle}"
