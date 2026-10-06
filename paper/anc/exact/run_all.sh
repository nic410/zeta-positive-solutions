#!/usr/bin/env bash
# Re-run the exact-member certificates and write the logs:   PY=python3 exact/run_all.sh [WORKERS]
# (N), (POS) and the bound for max_k((2k)! p_k)^(1/2k) at J = 10, 60, 61, 110, 111 (writes exact/out/P{J}_ball.txt).
# Cost: about 45 CPU-minutes in total (enclosures J = 110, 111: about 20 CPU-minutes each).
# WORKERS (default 2, as in the shipped logs) is the number of worker processes of each enclosure run.
# Each run overwrites its log (and its enclosure) in place: run on a copy of this directory and compare with the shipped
# logs by   python tools/logdiff.py SHIPPED_DIR COPY_DIR   and with   sha256sum -c SHA256SUMS.
# set -e: the batch stops at the first run that does not certify (non-zero exit code).
set -e
cd "$(dirname "$0")/.."
W=${1:-2}
export PY=${PY:-python3}
for spec in 10:800 60:1800 61:2000 110:3000 111:3000; do
  J=${spec%%:*}; B=${spec##*:}
  ./runlog.sh exact/logs/NPOS_J$J.log "$PY" exact/verify_exact_member.py $J --prec $B --workers "$W" \
              --ref exact/ref/P${J}_ref.txt --out exact/out/P${J}_ball.txt
done
# The coefficient bound 0.71636 of the finite-J instances (J = 60, 61, 110, 111), checked from the enclosures
./runlog.sh exact/logs/coefficient_bound.log "$PY" exact/check_coefficient_bound.py --bound 0.71636 \
            exact/out/P60_ball.txt exact/out/P61_ball.txt exact/out/P110_ball.txt exact/out/P111_ball.txt
