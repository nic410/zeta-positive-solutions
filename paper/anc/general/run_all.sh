#!/usr/bin/env bash
# Re-run every certificate in general/ and write the logs (run from the top directory or anywhere):
#     PY=python3 general/run_all.sh
# One process at a time (the window bounds use 2). Cost on one core: about 8 min (K = 128) + 5 min (F_80) + 3 min
# (Gamma_R^2 dual) + 1 min (Gamma_R^2 pair) + 3 min (Gamma_C dual and pair) + 0.2 min (pair for zeta at log q = 0.02)
# + about 10 min (the floating-point identity checks of the three pairs, which are not certificates).
# --gap-x N: the natural gap xi_N of the data (Q(sqrt 5): 4; Q(sqrt -3): 3; zeta: 2) is checked as well.
# The corollaries and the window bounds read the summaries written to general/results/ by the runs they name.
# Each run overwrites its log (and its summary) in place: run on a copy of this directory and compare with the shipped
# logs by   python tools/logdiff.py SHIPPED_DIR COPY_DIR   and with   sha256sum -c SHA256SUMS.
# set -e: the batch stops at the first run that does not certify (non-zero exit code).
set -e
cd "$(dirname "$0")/.."
export PY=${PY:-python3}
./runlog.sh general/logs/zeta_K128_s13.log     "$PY" general/verify_general.py general/params/zeta_K128_s13.json
./runlog.sh general/logs/zeta_K80_s12_F80.log  "$PY" general/verify_general.py general/params/zeta_K80_s12_F80.json
./runlog.sh general/logs/F80_windows.log       "$PY" general/verify_windows.py general/params/F80_windows.json 2
./runlog.sh general/logs/gammaR2_K80_s7.log    "$PY" general/verify_general.py general/params/gammaR2_K80_s7.json
./runlog.sh general/logs/pair_gammaR2_X240.log "$PY" general/verify_pair.py    general/params/pair_gammaR2_X240.json --gap-x 4
./runlog.sh general/logs/gammaC_K64_s9.log     "$PY" general/verify_general.py general/params/gammaC_K64_s9.json
./runlog.sh general/logs/pair_gammaC_X40.log   "$PY" general/verify_pair.py    general/params/pair_gammaC_X40.json --gap-x 3
./runlog.sh general/logs/corollary_qsqrt5.log  "$PY" general/corollary_slack.py general/params/corollary_qsqrt5.json --gap-x 4
./runlog.sh general/logs/corollary_qsqrtm3.log "$PY" general/corollary_slack.py general/params/corollary_qsqrtm3.json --gap-x 3
./runlog.sh general/logs/pair_zeta_logq002_X10.log "$PY" general/verify_pair.py general/params/pair_zeta_logq002_X10.json --gap-x 2
# Floating-point identity checks of the three pairs (not certificates), at sigma = 1.5 and 0.7
for P in gammaR2_X240 gammaC_X40 zeta_logq002_X10; do
  for SIG in 1.5 0.7; do
    ./runlog.sh general/logs/identity_${P}_sigma$SIG.log "$PY" general/check_pair_identity.py general/params/pair_$P.json $SIG
  done
done
