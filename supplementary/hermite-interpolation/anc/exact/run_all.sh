#!/usr/bin/env bash
# Re-run the certificates for the exact members and write the logs:   PY=python3 exact/run_all.sh [WORKERS]
# Root geometry at J = 60, 110, 111; Lemma BF at J = 60 and J = 10; base data (B) at J = 60, 110, 10; ratio bounds R_1 at J = 60, 110; increment signs
# at J = 60, 110.  Inputs: the certified enclosures exact/out/P{J}_ball.txt (copies of the outputs of
# exact/verify_exact_member.py of Paper I).  Cost: about 30 CPU-minutes (R_1 at J = 110: 15).
# WORKERS (default 2, as in the shipped logs) is used by every multi-process run; base_J10 used one process.
# Each run overwrites its log in place: run on a copy of this directory and compare with the shipped logs by
#     python tools/logdiff.py SHIPPED_DIR COPY_DIR
# set -e: the batch stops at the first run that does not certify (non-zero exit code).
set -e
cd "$(dirname "$0")/.."
W=${1:-2}
export PY=${PY:-python3}
# Root geometry of the exact members at J = 60, 110, 111 (validated root isolation)
for J in 60 110 111; do
  ./runlog.sh exact/logs/roots_J$J.log "$PY" exact/verify_roots.py exact/out/P${J}_ball.txt --prec 2000
done
./runlog.sh exact/logs/BF_J60.log "$PY" exact/verify_bf.py exact/out/P60_ball.txt --x0 199.4 --x0 199.39 --control 199.35 --prec 4600
./runlog.sh exact/logs/BF_J10.log "$PY" exact/verify_bf.py exact/out/P10_ball.txt --x0 16.45 --control 16.44 --prec 1000
# Base data (B): Fhat_J >= theta Psi_1 min(1, d^2) on [xi_2, xi_X] and Fhat_J'' > 0 at the nodes
./runlog.sh exact/logs/base_J60.log  "$PY" exact/verify_base.py exact/out/P60_ball.txt  --X 199 --theta 0.787979 --prec 1800 --workers "$W"
./runlog.sh exact/logs/base_J110.log "$PY" exact/verify_base.py exact/out/P110_ball.txt --X 59  --theta 0.787979 --prec 3000 --workers "$W"
./runlog.sh exact/logs/base_J10.log  "$PY" exact/verify_base.py exact/out/P10_ball.txt  --X 16  --theta 0.786684 --prec 800  --workers 1
# Ratio bounds R_1(X) >= sup_{[2,X] \ PP} |Fhat_{J+1} - Fhat_J| / (|Delta p_1| Fhat_J)
./runlog.sh exact/logs/R1_J60.log  "$PY" exact/verify_r1.py exact/out/P60_ball.txt exact/out/P61_ball.txt \
            --target 31:1.021e9 --prec 1800 --workers "$W"
./runlog.sh exact/logs/R1_J110.log "$PY" exact/verify_r1.py exact/out/P110_ball.txt exact/out/P111_ball.txt \
            --target 31:1.037e9 --target 43:2.701e9 --target 47:3.476e9 --target 53:4.844e9 --target 59:6.474e9 \
            --prec 3000 --workers "$W"
# Sign pattern of the coefficient increments p_k^(J+1) - p_k^(J)
./runlog.sh exact/logs/increments_J60.log  "$PY" exact/verify_increments.py exact/out/P60_ball.txt exact/out/P61_ball.txt \
            --expect-negative 2,4,6,10,11
./runlog.sh exact/logs/increments_J110.log "$PY" exact/verify_increments.py exact/out/P110_ball.txt exact/out/P111_ball.txt \
            --expect-negative 2,4,6,10,11
