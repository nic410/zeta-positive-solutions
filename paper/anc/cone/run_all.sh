#!/usr/bin/env bash
# Re-run the certificates of cone/ (the exact Hermite members F_J lie in the cone C, J = 10, 60, 61, 110, 111).
# Usage (from the top directory):  export PY=python3;  cone/run_all.sh [WORKERS] [WHAT]
#   WORKERS (default 3, as in the shipped logs) is the number of worker processes of each run.
#   WHAT = all (default) | selftest | primary | second | compare
#   primary: cone/cert_exact.py on exact/out (enclosures of exact/verify_exact_member.py; operators lib/bessel_form;
#            trapezoid-rule K of lib/k01_trapezoid)
#   second : cone/cert_exact_alt.py on exact/ref (independently computed enclosures; independent operator construction
#            lib/opcalc; series/asymptotic K of lib/besselk); same certificate logic
#   each for x_min = 2 (with the cost A(F_J)) and x_min = 1.  Logs: cone/logs/, JSON summaries: cone/out/.
# Each run overwrites its log and its JSON summary in place: run on a copy of this directory and compare with the shipped
# logs by   python tools/logdiff.py SHIPPED_DIR COPY_DIR   and with   sha256sum -c SHA256SUMS.
set -eu                      # stop at the first run that does not certify (non-zero exit code)
cd "$(dirname "$0")/.."
W=${1:-3}
WHAT=${2:-all}
export PY=${PY:-python3}
declare -A SHA=( [10]=4e55d361d6d2c05f15565bd3c94d56b9f5e0715acecda9fd362410181bdc48d3
                 [60]=fdfbfe57bfe9945f640291b6f1e1b7e74e4d5afb04278961d5737f26db6cda4b
                 [61]=8cc7b2b9a66f643e8e40d84fd4ffd6970401342aeab87b716ec169bc91ca3dd4
                 [110]=7c8999567bc77cd1c6fb5a9e816bb0b4f212b971f26dd0f3bda3237ff51c117a
                 [111]=25669a321f71ddef789247cd0adc0fd129c5d70f293e488bc4dab8c3f708b3f1 )
declare -A SHAREF=( [10]=101eba6041a44d9ecf7f8f2fb267899759d9b048fcf5fa420499b516db8a7971
                    [60]=cf6cff397c3fe1ba5084331132b52fc35f15a41a1fa84f11db6126f752263576
                    [61]=532d0576df70320ebee3e286cca7b75fcae559a4eb5837f8bfaa17ff7b2f9637
                    [110]=dcba593fad1b1e11ce5320bb05c990dd9d3894879be4f2767ad9a483d53ef043
                    [111]=0300ef95e96fc6f41cc341faa1b1b760f1db40a80da2f2c7cd80939d0312c8cc )
declare -A PREC=( [10]=800 [60]=1800 [61]=2000 [110]=3000 [111]=3000 )
if [ "$WHAT" = all ] || [ "$WHAT" = selftest ]; then
  ./runlog.sh cone/logs/selftest.log "$PY" cone/selftest.py
fi
for path in primary second; do
  [ "$WHAT" = all ] || [ "$WHAT" = $path ] || continue
  for xm in 2 1; do
    for J in 10 60 61 110 111; do
      case $J in 10) ORD="--order 24";; 60|61) ORD="--order 28 --order-far 48 --order-switch 80";;
                 *) ORD="--order 28 --order-far 64 --order-switch 121";; esac
      COST=""; [ $xm = 2 ] && COST="--cost $(( J < 100 ? 400 : 800 ))"
      if [ $path = primary ]; then
        ./runlog.sh cone/logs/W_J${J}_x${xm}.log "$PY" cone/cert_exact.py $J --pball exact/out/P${J}_ball.txt \
            --sha ${SHA[$J]} --prec ${PREC[$J]} $ORD --workers "$W" --xmin $xm $COST --json cone/out/W_J${J}_x${xm}.json
      else
        ./runlog.sh cone/logs/Wref_J${J}_x${xm}.log "$PY" cone/cert_exact_alt.py $J --pball exact/ref/P${J}_ref.txt \
            --sha ${SHAREF[$J]} --prec ${PREC[$J]} $ORD --workers "$W" --xmin $xm --kback series $COST \
            --json cone/out/Wref_J${J}_x${xm}.json
      fi
    done
  done
done
if [ "$WHAT" = all ] || [ "$WHAT" = compare ]; then
  ./runlog.sh cone/logs/compare_x2.log "$PY" cone/compare_runs.py 10,60,61,110,111 --xmin 2
  ./runlog.sh cone/logs/compare_x1.log "$PY" cone/compare_runs.py 10,60,61,110,111 --xmin 1
fi
echo "cone/run_all.sh $WHAT: done"
