#!/usr/bin/env bash
# The audit of the Lean formalisation of Paper I (library `PositivityRigidity`). Run from anywhere after `lake build`:
#   scripts/audit.sh            (CORES=8-15 LEAN_NUM_THREADS=8 scripts/audit.sh to pin to other cores)
# CORES (default 0-3) is a CPU list for `taskset`; the pinning is skipped if `taskset` is not available (e.g. macOS)
# or cannot pin to CORES, and CORES= (empty) disables it. LEAN_NUM_THREADS defaults to 4. AUDIT_NO_GIT=1 lists the
# files for the provenance digest without git.
# One command, one final line: `AUDIT PASSED` (or `AUDIT FAILED`).
#
# (0) `lake build --no-build PositivityRigidity` succeeds: the checked .olean files are those of the current sources.
# (a) no `sorry` / `admit` / `native_decide` token anywhere in the Lean sources (PositivityRigidity/,
#     PositivityRigidity.lean, scripts/; comments and string literals stripped; also covers files that the library
#     root does not import);
# (b) axioms: no `axiom` declaration outside PositivityRigidity/Ledger.lean (textual, comments and strings stripped,
#     and in the environment:
#     scripts/Audit.lean); the number of ledger axioms (textual and in the environment) equals the total in
#     LEDGER.md, and LEDGER.md names every ledger axiom; no declaration of the library depends on an axiom other
#     than propext, Classical.choice, Quot.sound and the ledger axioms (so no sorryAx, no Lean.ofReduceBool =
#     native_decide, no Lean.trustCompiler); every headline theorem exists and is a theorem;
# (c) `#print axioms` regression: the output of scripts/print_axioms.lean (every headline theorem and every other
#     formalised numbered statement) equals axioms.log, its `# ` header lines excepted, exactly;
# (d) statement pin: the output of scripts/Statements.lean (the types of the headline theorems and of every ledger
#     axiom, and the types and bodies of every project definition they unfold to, with structural hashes) equals
#     scripts/Statements.baseline.txt exactly. (c) pins the dependencies of the headlines by name; (d) pins what
#     the names and the axioms mean;
# (e) every SHA-256 cited in PositivityRigidity/Ledger.lean and LEDGER.md matches ../SHA256SUMS
#     (scripts/check_ledger_hashes.py, Python standard library only);
# (f) non-vacuity: scripts/NonVacuity.lean compiles, and each of its 11 theorems (the test class and the cones are
#     non-empty, `κ*` is not a junk value, admissible pairs are Radon, `Arch` and `RiemannHypothesis` are the
#     paper's, the explicit formula holds on a Paley-Wiener subclass, the hypotheses of the v1.1 results can be
#     met) depends only on propext, Classical.choice, Quot.sound.
# Provenance (printed, not enforced): a sha256 over the project's files (`git ls-files`, or, outside a git
# checkout or with AUDIT_NO_GIT=1, every file except `.lake/`).
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CORES=${CORES-0-3}
PIN=""
if [ -n "$CORES" ] && command -v taskset >/dev/null 2>&1 && taskset -c "$CORES" true >/dev/null 2>&1; then
  PIN="taskset -c $CORES"
fi
RUN="env LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} $PIN lake env lean"
fail=0

echo "== provenance (printed, not enforced) =="
if [ -z "${AUDIT_NO_GIT:-}" ] && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  files=$(git ls-files --cached --others --exclude-standard . | LC_ALL=C sort -u); src="git ls-files, tracked and untracked-unignored"
else
  files=$(find . -path ./.lake -prune -o -type f -print | sed 's|^\./||' | LC_ALL=C sort); src="all files except .lake/"
fi
nfiles=$(echo "$files" | sed '/^$/d' | wc -l)
digest=$(echo "$files" | sed '/^$/d' | while IFS= read -r f; do [ -f "$f" ] && sha256sum -- "$f"; done | sha256sum | cut -d' ' -f1)
echo "sha256 over $nfiles files ($src; sha256sum lines, sorted by path): $digest"
echo

echo "== (0) the build is up to date with the sources =="
# Everything below reads the built .olean files; a source edited after the last `lake build` would not be seen.
if nb_out=$($PIN lake build --no-build PositivityRigidity 2>&1); then
  echo "lake build --no-build PositivityRigidity: $(echo "$nb_out" | tail -1)"
else
  echo "$nb_out" | grep -v '^Note: \|^warning\|^⚠' | tail -5
  echo "FAIL: the build is not up to date (run \`lake build\` first; it must succeed)"; fail=1
fi
echo

echo "== (a) no sorry / admit / native_decide in the Lean sources =="
# Every Lean file of the project (also files that the library root does not import), with comments and string
# literals stripped, as `file:line: text` lines; (a) and (b) search this text.
stripped=$(find PositivityRigidity scripts -name '*.lean' -print0 | LC_ALL=C sort -z | xargs -0 perl -e '
  for my $f (@ARGV) { open(my $h, "<:encoding(UTF-8)", $f) or die "$f: $!"; local $/; my $s = <$h>; close $h;
    my ($o, $d, $i, $n) = ("", 0, 0, length $s);
    while ($i < $n) { my $c = substr($s, $i, 2);
      if ($c eq "/-") { $d++; $i += 2; next }
      if ($d > 0) { if ($c eq "-/") { $d--; $i += 2 } else { $o .= "\n" if substr($s, $i, 1) eq "\n"; $i++ } next }
      if ($c eq "--") { $i++ while $i < $n && substr($s, $i, 1) ne "\n"; next }
      if (substr($s, $i, 1) eq "\"") { $i++; while ($i < $n && substr($s, $i, 1) ne "\"") { $i += (substr($s, $i, 1) eq "\\") ? 2 : 1 } $i++; next }
      $o .= substr($s, $i, 1); $i++ }
    binmode(STDOUT, ":encoding(UTF-8)");
    my $ln = 0; for my $l (split /\n/, $o) { $ln++; print "$f:$ln: $l\n" if $l =~ /\S/ } }' PositivityRigidity.lean)
tok_hits=$(echo "$stripped" | perl -ne 'print if /^[^:]*:\d+: .*(?<![\w.])(sorry|admit|native_decide)(?![\w])/')
if [ -n "$tok_hits" ]; then echo "$tok_hits"; echo "FAIL: sorry/admit/native_decide in the sources"; fail=1
else echo "sorry/admit/native_decide (outside comments and strings; PositivityRigidity, scripts): none"; fi
echo

echo "== (b) axioms: only in the ledger, counted in LEDGER.md =="
axiom_re='^[^:]*:[0-9]+: \s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(private\s+|protected\s+)?axiom\s'
outside=$(echo "$stripped" | grep -E "$axiom_re" | grep -v '^PositivityRigidity/Ledger\.lean:')
if [ -n "$outside" ]; then echo "$outside"; echo "FAIL: axiom declaration outside PositivityRigidity/Ledger.lean"; fail=1
else echo "axiom declarations outside PositivityRigidity/Ledger.lean (textual): none"; fi
n_text=$(echo "$stripped" | grep -E "$axiom_re" | grep -c '^PositivityRigidity/Ledger\.lean:')
n_md=$(sed -n 's/^| \*\*Total\*\* | \*\*\([0-9]*\)\*\* |.*/\1/p' LEDGER.md | head -1)
audit_out=$($RUN scripts/Audit.lean 2>&1)
echo "$audit_out"
n_lean=$(echo "$audit_out" | sed -n 's/^ledger axioms (axiom declarations in PositivityRigidity.Ledger): \([0-9]*\)$/\1/p')
echo "ledger axioms: $n_text in Ledger.lean (textual), ${n_lean:-?} in the environment, ${n_md:-?} in LEDGER.md (Total)"
if [ -z "$n_md" ] || [ -z "$n_lean" ] || [ "$n_text" != "$n_md" ] || [ "$n_lean" != "$n_md" ]; then
  echo "FAIL: the number of ledger axioms differs from LEDGER.md"; fail=1; fi
for ax in $(echo "$audit_out" | sed -n 's/^  PosRig\.\([A-Za-z0-9_]*\)$/\1/p'); do
  grep -qF "\`$ax\`" LEDGER.md || { echo "FAIL: ledger axiom $ax is not named in LEDGER.md"; fail=1; }
done
echo "$audit_out" | grep -q '^axiom declarations outside PositivityRigidity.Ledger: none$' \
  || { echo "FAIL: axiom declarations outside PositivityRigidity.Ledger (environment)"; fail=1; }
echo "$audit_out" | grep -q '^axioms other than propext / Classical.choice / Quot.sound and the ledger axioms .*: none$' \
  || { echo "FAIL: some declaration depends on an axiom outside the ledger (sorryAx, native_decide, ...)"; fail=1; }
echo "$audit_out" | grep -q '^declarations depending on sorryAx: none$' \
  || { echo "FAIL: some declaration depends on sorryAx"; fail=1; }
if echo "$audit_out" | grep -q '^headline .*: \(MISSING\|NOT A THEOREM\)'; then
  echo "FAIL: a headline theorem is missing"; fail=1; fi
n_head=$(echo "$audit_out" | grep -c '^headline .*: theorem; ')
[ "$n_head" -eq 14 ] || { echo "FAIL: expected 14 headline theorems, found $n_head"; fail=1; }
echo

echo "== (c) regression: scripts/print_axioms.lean against axioms.log =="
pa_out=$($RUN scripts/print_axioms.lean 2>&1)
pa_exp=$(grep -v '^# ' axioms.log)
if [ "$pa_out" = "$pa_exp" ]; then
  echo "axioms.log reproduced exactly: $(echo "$pa_out" | grep -c "^'") declarations (all headline theorems among them)"
else
  echo "FAIL: #print axioms differs from axioms.log:"; diff <(echo "$pa_exp") <(echo "$pa_out") | head -40; fail=1
fi
if echo "$pa_out" | grep -q 'sorryAx'; then echo "FAIL: a printed declaration depends on sorryAx"; fail=1; fi
echo

echo "== (d) statement pin: scripts/Statements.lean against scripts/Statements.baseline.txt =="
st_out=$($RUN scripts/Statements.lean 2>&1)
if [ "$st_out" = "$(cat scripts/Statements.baseline.txt)" ]; then
  echo "statement pin: $(sed -n '1s/^== statement pin: \([0-9]*\) declarations.*/\1/p' <<< "$st_out") declarations, identical to scripts/Statements.baseline.txt"
else
  echo "FAIL: the statements differ from scripts/Statements.baseline.txt (the meaning of a headline or of an axiom changed):"
  diff <(cat scripts/Statements.baseline.txt) <(echo "$st_out") | head -60
  fail=1
fi
echo

echo "== (e) cited SHA-256 values against ../SHA256SUMS =="
if hash_out=$(python3 scripts/check_ledger_hashes.py 2>&1); then
  echo "$(echo "$hash_out" | grep -c '^OK') citations checked: $(echo "$hash_out" | tail -1)"
else
  echo "$hash_out" | grep -v '^OK' ; echo "FAIL: scripts/check_ledger_hashes.py"; fail=1
fi
echo

echo "== (f) non-vacuity checks (scripts/NonVacuity.lean) =="
nv_out=$($RUN scripts/NonVacuity.lean 2>&1); nv_rc=$?
echo "$nv_out"
std_re="'PosRig\.NonVacuity\.[A-Za-z0-9_]+' (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])"
nv_bad=$(echo "$nv_out" | sed '/^$/d' | grep -vxE "$std_re")
nv_n=$(echo "$nv_out" | grep -cxE "$std_re")
if [ $nv_rc -ne 0 ] || [ -n "$nv_bad" ]; then
  echo "FAIL: scripts/NonVacuity.lean has errors, or a theorem there uses an axiom other than propext, Classical.choice, Quot.sound"; fail=1
elif [ "$nv_n" -ne 11 ]; then echo "FAIL: expected 11 non-vacuity theorems, found $nv_n"; fail=1
else
  for t in classes_nonempty kappaStar_index_nonempty admissible_radon arch_faithful rh_faithful explicit_formula_check \
           summability_finite summability_weighted_cumulative near_rigidity_certificate_meaning xi_sq_support \
           zero_support_hypothesis_pZeta; do
    echo "$nv_out" | grep -q "^'PosRig\.NonVacuity\.$t' " || { echo "FAIL: non-vacuity theorem $t missing"; fail=1; }
  done
  echo "non-vacuity: $nv_n theorems, each with axioms among propext, Classical.choice, Quot.sound"
fi
echo
if [ $fail -eq 0 ]; then
  echo "no sorry/admit/native_decide; $n_md ledger axioms, all in Ledger.lean and LEDGER.md; axioms.log and the statement pin reproduced; hashes match; non-vacuity checks pass"
  echo "AUDIT PASSED"
else echo "AUDIT FAILED"; fi
exit $fail
