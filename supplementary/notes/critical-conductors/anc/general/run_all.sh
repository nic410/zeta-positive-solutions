#!/usr/bin/env bash
# Re-run every certificate in general/ and write the logs (run from the top directory or anywhere):
#     PY=python3 general/run_all.sh
# One process at a time. Cost on one core: about 8 min (K = 128) + 4 min (K = 104) + 3 min (right pole-residue pin)
# + 3 min (Gamma_R^2 dual) + 1 min (Gamma_R^2 pair) + 3 min (Gamma_C dual and pair) + 0.1 min (pair for Q(i)).
# --gap-x N: the natural gap xi_N of the data (Q(sqrt 5): 4; Q(sqrt -3): 3) is checked as well.
# The corollaries read the summaries written to general/results/ by the runs they name.
# Each run overwrites its log (and its summary) in place: run on a copy of this directory and compare with the shipped
# logs by   python tools/logdiff.py SHIPPED_DIR COPY_DIR   and with   sha256sum -c SHA256SUMS.
# set -e: the batch stops at the first run that does not certify (non-zero exit code).
set -e
cd "$(dirname "$0")/.."
export PY=${PY:-python3}
./runlog.sh general/logs/zeta_K128_s13.log     "$PY" general/verify_general.py general/params/zeta_K128_s13.json
./runlog.sh general/logs/zeta_K104_s13.log     "$PY" general/verify_general.py general/params/zeta_K104_s13.json
./runlog.sh general/logs/zeta_K80_s12_edge.log "$PY" general/verify_general.py general/params/zeta_K80_s12_edge.json
./runlog.sh general/logs/gammaR2_K80_s7.log    "$PY" general/verify_general.py general/params/gammaR2_K80_s7.json
./runlog.sh general/logs/pair_gammaR2_X240.log "$PY" general/verify_pair.py    general/params/pair_gammaR2_X240.json --gap-x 4
./runlog.sh general/logs/gammaC_K64_s9.log     "$PY" general/verify_general.py general/params/gammaC_K64_s9.json
./runlog.sh general/logs/pair_gammaC_X40.log   "$PY" general/verify_pair.py    general/params/pair_gammaC_X40.json --gap-x 3
./runlog.sh general/logs/pair_Qi_X10.log       "$PY" general/verify_pair.py    general/params/pair_Qi_X10.json
./runlog.sh general/logs/corollary_qsqrt5.log  "$PY" general/corollary_slack.py general/params/corollary_qsqrt5.json --gap-x 4
./runlog.sh general/logs/corollary_qsqrtm3.log "$PY" general/corollary_slack.py general/params/corollary_qsqrtm3.json --gap-x 3
