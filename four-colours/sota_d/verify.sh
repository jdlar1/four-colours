#!/bin/sh
set -eu
export OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 OMP_NUM_THREADS=8 PYTHONDONTWRITEBYTECODE=1
bundle=${1:-best_bundle}
workers=${2:-8}
python3 check_archive.py >/dev/null
sh build.sh
python3 lift_build.py
"${PYTHON:-python3}" audit.py "$bundle"
python3 lift.py "$bundle"
python3 replay.py "$bundle" "$workers" both
python3 manifest.py "$bundle"
