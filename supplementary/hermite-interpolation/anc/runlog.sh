#!/usr/bin/env bash
# Run one verifier from the anc/ directory and record a log with a header and a footer.
# Usage (from anc/):   ./runlog.sh LOGFILE  command [args...]
# Example:             export PY=python3
#                      ./runlog.sh kappa/logs/J40.log "$PY" kappa/verify_kappa.py kappa/params/J40.json --prec 1000
set -u
cd "$(dirname "$0")"
log="$1"; shift
PYBIN="${PY:-python3}"
mkdir -p "$(dirname "$log")"
{
  shown="$*"
  if [ "${1:-}" = "$PYBIN" ]; then shown="python ${*:2}"; fi    # never print the interpreter's absolute path
  echo "# command : $shown"
  echo "# date    : $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# system  : $(uname -sm), $(nproc) visible cores"
  echo "# python  : $("$PYBIN" -c 'import sys,flint,mpmath; print(sys.version.split()[0], "| python-flint", flint.__version__, "| mpmath", mpmath.__version__)')"
} > "$log"
t0=$(date +%s.%N)
"$@" >> "$log" 2>&1
rc=$?
t1=$(date +%s.%N)
awk -v a="$t0" -v b="$t1" -v rc="$rc" 'BEGIN{printf "# exit code %d; wall time %.1f s\n", rc, b-a}' >> "$log"
exit $rc
