#!/usr/bin/env bash
# Re-run every toy-model certificate and write the logs (run from anc/ or anywhere):
#     PY=python3 toy/run_all.sh
# Total cost about 78 CPU-minutes: Theorem PT4 (two runs of about 20 min) and Theorem PP80 (two runs of about
# 5 min, plus about 8 min for the second route) dominate.  The commands are independent; the split ranges and
# piece lists may be run in parallel (e.g. by appending '&' and a final 'wait').  Each PT4 run needs about 1 GB of memory.
# Each run overwrites its log in place: run on a copy of anc/ and compare with the shipped logs by
#     python tools/logdiff.py SHIPPED_ANC COPY_OF_ANC
# set -e: the batch stops at the first run that does not certify (non-zero exit code).
set -e
cd "$(dirname "$0")/.."
export PY=${PY:-python3}
# Theorem PP80: direct route (tau basis, 6000 bits), levels K = 0..160 split into two runs
./runlog.sh toy/pp80/logs/pp80_tau_K0-134.log   "$PY" toy/pp80/verify_pp80_tau.py toy/pp80/params/pp80.json 0 134
./runlog.sh toy/pp80/logs/pp80_tau_K135-160.log "$PY" toy/pp80/verify_pp80_tau.py toy/pp80/params/pp80.json 135 160
# Theorem PP80: hypotheses of Theorem A by the Stirling-1 cofactor system (4000 bits), K = 0..160
./runlog.sh toy/pp80/logs/pp80_chain_K0-160.log "$PY" toy/pp80/verify_pp80_chain.py toy/pp80/params/pp80_chain.json
# Theorems PT2, PT3, PT4 (exact); PT2 also by the independent Cramer route; PT4 split by pieces into two runs
./runlog.sh toy/pt/logs/pt2.log        "$PY" toy/pt/verify_pt.py toy/pt/params/pt2.json
./runlog.sh toy/pt/logs/pt2_cramer.log "$PY" toy/pt/verify_pt2_cramer.py
./runlog.sh toy/pt/logs/pt3.log        "$PY" toy/pt/verify_pt.py toy/pt/params/pt3.json
./runlog.sh toy/pt/logs/pt4_region.log "$PY" toy/pt/check_pt4_region.py toy/pt/params/pt4.json
./runlog.sh toy/pt/logs/pt4_part1.log  "$PY" toy/pt/verify_pt.py toy/pt/params/pt4.json Ia1,Iap,Ia3,Ib1,Ib2
./runlog.sh toy/pt/logs/pt4_part2.log  "$PY" toy/pt/verify_pt.py toy/pt/params/pt4.json II1,II2,II3,II4,II5,II6
# (AP+) and (B) at delta = 1/20, J = 1..90 (exact)
./runlog.sh toy/ap/logs/ap_delta005_J1-80.log  "$PY" toy/ap/verify_ap.py toy/ap/params/ap_delta005.json 1 80
./runlog.sh toy/ap/logs/ap_delta005_J81-90.log "$PY" toy/ap/verify_ap.py toy/ap/params/ap_delta005.json 81 90
./runlog.sh toy/ap/logs/halfstep_delta005_J1-90.log "$PY" toy/ap/verify_halfstep.py toy/ap/params/ap_delta005.json 1 90
# Conjecture W: certified counterexamples (Arb) and Theorems W2, W3 (exact; Q'' > 0 from Theorems PT2, PT3)
./runlog.sh toy/w/logs/w_cex.log "$PY" toy/w/verify_w_cex.py toy/w/params/w_cex.json
./runlog.sh toy/w/logs/w_J2.log  "$PY" toy/w/verify_w_small.py toy/w/params/w_small.json 2
./runlog.sh toy/w/logs/w_J3.log  "$PY" toy/w/verify_w_small.py toy/w/params/w_small.json 3
# (SMset) for k = 1..60 (Arb), (UM+) at sampled J (Arb), explicit far-node remainders for PP_6, PP_10, PP_20 (Arb)
./runlog.sh toy/sm/logs/smset_k1-60.log "$PY" toy/sm/verify_smset.py toy/sm/params/smset.json
./runlog.sh toy/um/logs/um.log          "$PY" toy/um/verify_um.py toy/um/params/um.json
./runlog.sh toy/ft/logs/farbound.log    "$PY" toy/ft/verify_farbound.py toy/ft/params/farbound.json
./runlog.sh toy/w/logs/w_J2_insertion.log "$PY" toy/w/verify_w_insertion.py toy/w/params/w_small.json 2
./runlog.sh toy/w/logs/w_J3_insertion.log "$PY" toy/w/verify_w_insertion.py toy/w/params/w_small.json 3
# Prime powers dominate the PT-tight progression (finite part, exact); zero-slack PT counterexamples at J = 2 (exact)
./runlog.sh toy/pp/logs/pp_prefix.log "$PY" toy/pp/verify_pp_prefix.py toy/pp/params/pp_prefix.json
./runlog.sh toy/pt/logs/pt0_false.log "$PY" toy/pt/verify_pt0_false.py toy/pt/params/pt0_false.json
