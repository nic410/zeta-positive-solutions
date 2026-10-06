#!/usr/bin/env bash
# Re-run every kappa* certificate and write the logs (run from anc/ or anywhere):
#     PY=python3 kappa/run_all.sh [WORKERS]
# Total cost about 40 CPU-minutes (J = 100: 26; self-test: 4); WORKERS processes per run (default 1, as in the shipped
# logs; the header line 'workers' and the timings are the only output that depends on it).
# Each run overwrites its log in place: run on a copy of anc/ and compare with the shipped logs by
#     python tools/logdiff.py SHIPPED_ANC COPY_OF_ANC
# set -e: the batch stops at the first run that does not certify (non-zero exit code).
set -e
cd "$(dirname "$0")/.."
W=${1:-1}
export PY=${PY:-python3}
./runlog.sh kappa/logs/cushion.log  "$PY" kappa/cushion_A.py
./runlog.sh kappa/logs/selftest.log "$PY" kappa/selftest.py
./runlog.sh kappa/logs/J20.log  "$PY" kappa/verify_kappa.py kappa/params/J20.json  --prec 600  --order 28 --workers "$W"
./runlog.sh kappa/logs/J23.log  "$PY" kappa/verify_kappa.py kappa/params/J23.json  --prec 500  --order 24 --workers "$W"
./runlog.sh kappa/logs/J24.log  "$PY" kappa/verify_kappa.py kappa/params/J24.json  --prec 500  --order 24 --workers "$W"
./runlog.sh kappa/logs/J30.log  "$PY" kappa/verify_kappa.py kappa/params/J30.json  --prec 700  --order 26 --workers "$W"
./runlog.sh kappa/logs/J35.log  "$PY" kappa/verify_kappa.py kappa/params/J35.json  --prec 850  --order 26 --workers "$W"
./runlog.sh kappa/logs/J40.log  "$PY" kappa/verify_kappa.py kappa/params/J40.json  --prec 1000 --order 28 --workers "$W"
./runlog.sh kappa/logs/J50.log  "$PY" kappa/verify_kappa.py kappa/params/J50.json  --prec 1300 --order 28 --workers "$W"
./runlog.sh kappa/logs/J60.log  "$PY" kappa/verify_kappa.py kappa/params/J60.json  --prec 1700 --order 28 --workers "$W"
./runlog.sh kappa/logs/J100.log "$PY" kappa/verify_kappa.py kappa/params/J100.json --prec 3300 --order 28 \
            --order-far 64 --order-switch 121 --workers "$W"
