#!/bin/bash
# Generates the modified certificates of Section 5 of the paper from certificate/tp_certificate.json, checks their
# SHA-256 against tests/expected_outputs.sha256, and runs one or both checkers on each of them.
# Usage, from the repository root:  tests/run_all.sh PYTHON WHICH [NPROC]
#   PYTHON: a Python 3 with python-flint;  WHICH: generate, first, second or both;  NPROC: worker processes per check.
# The modified certificates go to tests/work/{a,b,c}/ (generated if absent), one log per check to
# tests/logs/{first,second}/.
set -u
PY=${1:-python3}; WHICH=${2:-both}; NP=${3:-8}
W=tests/work
if [ "$WHICH" = generate ] || [ ! -d "$W" ]; then
  mkdir -p "$W/a" "$W/b" "$W/c"
  "$PY" -I tests/make_modified_a.py certificate/tp_certificate.json "$W/a" > /dev/null || exit 1
  "$PY" -I tests/make_modified_b.py certificate/tp_certificate.json "$W/b" > /dev/null || exit 1
  "$PY" -I tests/make_modified_c.py certificate/tp_certificate.json "$W/c" > /dev/null || exit 1
fi
(cd "$W" && sha256sum --quiet -c ../expected_outputs.sha256) || { echo "modified certificates differ"; exit 1; }
run() {   # $1 = first or second, $2 = checker file
  mkdir -p "tests/logs/$1"
  for f in "$W"/a/*.json "$W"/b/*.json "$W"/c/*.json; do
    s=$(basename "$(dirname "$f")"); b=$(basename "$f" .json)
    "$PY" -I "checker/$2" "$f" "$NP" > "tests/logs/$1/${s}_$b.log" 2>&1
    echo "exit status: $?" >> "tests/logs/$1/${s}_$b.log"
  done
}
case "$WHICH" in
  first) run first check_certificate.py ;;
  second) run second check_independent.py ;;
  both) run first check_certificate.py; run second check_independent.py ;;
esac
exit 0
