#!/usr/bin/env bash
# make_arxiv_tarball.sh -- build and verify the arXiv source tarball for the positivity-rigidity paper.
#
# Usage:
#   production/make_arxiv_tarball.sh [options]
#
# Options:
#   --paper-dir DIR   paper directory (default: parent of this script's directory)
#   --out-dir DIR     output directory (default: <paper-dir>/production/out)
#   --texbin DIR      directory containing pdflatex/bibtex
#                     (default: $TEXBIN, else ~/.TinyTeX/bin/x86_64-linux, else $PATH)
#   --with-00readme   add a minimal 00README.json (pdflatex, toplevel main.tex, TeX Live 2025).
#                     arXiv says this file is "not required (nor recommended)"; the heuristics
#                     find main.tex because it is the only file with \documentclass.
#   --include-bib     also ship refs.bib (arXiv uses main.bbl if it is present)
#   --strict          treat source-lint warnings as errors: uses of the draft-marker macros, red/magenta
#                     colouring, placeholder text (to-do, fix-me, to-be-determined, author placeholders), non-ASCII, \today, stub
#                     fallback, internal paths, placeholder text in anc/README. \NUM and absolute
#                     paths are errors in every mode.
#   --keep-temp       keep the temporary build/verify directories
#   -h, --help        show this help
#
# Environment:
#   CPUSET            optional CPU list for taskset, e.g. CPUSET=8-9 (default: unset, no taskset)
#   SOURCE_DATE_EPOCH mtime stamped on tar entries (default: newest source file mtime)
#
# What it does:
#   1. Collects main.tex and every file it \input's / \inputsection's (macros.tex, sections/*.tex),
#      recursively; stubs/ is never shipped. anc/ is copied if present (no .tex allowed there).
#   2. Generates main.bbl with pdflatex, bibtex, pdflatex, pdflatex in a scratch copy.
#   3. Lints the staged sources.
#   4. Writes a reproducible tar.gz into the output directory.
#   5. Unpacks it into a fresh directory and compiles there with pdflatex only (the .bbl is used
#      as-is, as arXiv does), rerunning until labels are stable, and fails on any error or
#      undefined reference/citation.
#   6. Prints and saves a report (sizes, page count, overfull boxes, warnings).
#
# Writes only to --out-dir and to a mktemp directory. Never modifies the paper sources.

set -euo pipefail

usage() { sed -n '2,/^$/p' "$0" | sed 's/^# \{0,1\}//'; exit "${1:-0}"; }

SCRIPT_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
PAPER_DIR=$(cd "$SCRIPT_DIR/.." && pwd)
OUT_DIR=""
TEXBIN_OPT="${TEXBIN:-}"
WITH_README=0
INCLUDE_BIB=0
STRICT=0
KEEP_TEMP=0
MAIN=main
CPUSET="${CPUSET:-}"

while [ $# -gt 0 ]; do
  case "$1" in
    --paper-dir) PAPER_DIR=$(cd "$2" && pwd); shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    --texbin) TEXBIN_OPT="$2"; shift 2 ;;
    --with-00readme) WITH_README=1; shift ;;
    --include-bib) INCLUDE_BIB=1; shift ;;
    --strict) STRICT=1; shift ;;
    --keep-temp) KEEP_TEMP=1; shift ;;
    -h|--help) usage 0 ;;
    *) echo "unknown option: $1" >&2; usage 2 ;;
  esac
done
OUT_DIR="${OUT_DIR:-$PAPER_DIR/production/out}"

# ---------------------------------------------------------------- toolchain
if [ -z "$TEXBIN_OPT" ] && [ -x "$HOME/.TinyTeX/bin/x86_64-linux/pdflatex" ]; then
  TEXBIN_OPT="$HOME/.TinyTeX/bin/x86_64-linux"
fi
if [ -n "$TEXBIN_OPT" ]; then export PATH="$TEXBIN_OPT:$PATH"; fi
for t in pdflatex bibtex tar gzip; do
  command -v "$t" >/dev/null || { echo "ERROR: $t not found (TEXBIN=$TEXBIN_OPT)" >&2; exit 1; }
done
RUN=()
if [ -n "$CPUSET" ] && command -v taskset >/dev/null; then RUN=(taskset -c "$CPUSET"); fi
export max_print_line=10000 error_line=254 half_error_line=238   # unwrapped log lines

TEXVER=$(pdflatex --version | head -1)

# ---------------------------------------------------------------- helpers
ERRORS=0; WARNINGS=0
REPORT_LINES=()
note()  { REPORT_LINES+=("$*"); echo "$*"; }
warn()  { WARNINGS=$((WARNINGS+1)); note "WARNING: $*"; }
lintw() { if [ "$STRICT" = 1 ]; then err "$*"; else warn "$*"; fi; }
err()   { ERRORS=$((ERRORS+1)); note "ERROR: $*"; }
die()   { echo "FATAL: $*" >&2; exit 1; }

strip_comments() { sed -e 's/\(^\|[^\\]\)%.*$/\1/' "$1"; }

WORK=$(mktemp -d "${TMPDIR:-/tmp}/arxiv-tarball.XXXXXX")
cleanup() { if [ "$KEEP_TEMP" = 1 ]; then echo "(kept temp dir $WORK)"; else rm -rf "$WORK"; fi; }
trap cleanup EXIT
SRC="$WORK/src"; mkdir -p "$SRC"

cd "$PAPER_DIR"
[ -f "$MAIN.tex" ] || die "$PAPER_DIR/$MAIN.tex not found"
note "paper dir : $PAPER_DIR"
note "toolchain : $TEXVER ($(command -v pdflatex))"

# ---------------------------------------------------------------- 1. collect sources
# Resolve \input{X}, \include{X}, \inputsection{X} (-> sections/X), \inputlemma{X} (-> lemmas/X) recursively.
declare -A SEEN=()
QUEUE=("$MAIN.tex")
SOURCES=()
while [ ${#QUEUE[@]} -gt 0 ]; do
  f="${QUEUE[0]}"; QUEUE=("${QUEUE[@]:1}")
  [ -n "${SEEN[$f]:-}" ] && continue
  SEEN[$f]=1
  [ -f "$f" ] || { err "referenced file missing: $f"; continue; }
  SOURCES+=("$f")
  while IFS= read -r ref; do
    [ -z "$ref" ] && continue
    case "$ref" in *'#'*) continue ;; esac          # macro parameter, e.g. inside \newcommand
    case "$ref" in *.tex) ;; *) ref="$ref.tex" ;; esac
    QUEUE+=("$ref")
  done < <(strip_comments "$f" | grep -oE '\\(input|include)\{[^}]+\}' | sed -E 's/^\\(input|include)\{(.*)\}$/\2/')
  while IFS= read -r sec; do
    [ -z "$sec" ] && continue
    case "$sec" in *'#'*) continue ;; esac
    if [ -f "sections/$sec.tex" ]; then QUEUE+=("sections/$sec.tex")
    else err "\\inputsection{$sec}: sections/$sec.tex not found"; fi
  done < <(strip_comments "$f" | grep -oE '\\inputsection\{[^}]+\}' | sed -E 's/^\\inputsection\{(.*)\}$/\1/')
  while IFS= read -r lem; do
    [ -z "$lem" ] && continue
    case "$lem" in *'#'*) continue ;; esac
    if [ -f "lemmas/$lem.tex" ]; then QUEUE+=("lemmas/$lem.tex")
    elif [ -f "stubs/$lem.tex" ]; then err "\\inputlemma{$lem}: only stubs/$lem.tex exists (stubs are not shipped)"
    else err "\\inputlemma{$lem}: lemmas/$lem.tex not found"; fi
  done < <(strip_comments "$f" | grep -oE '\\inputlemma\{[^}]+\}' | sed -E 's/^\\inputlemma\{(.*)\}$/\1/')
  while IFS= read -r fig; do
    [ -z "$fig" ] && continue
    found=""
    for ext in "" .pdf .png .jpg .jpeg; do [ -f "$fig$ext" ] && { found="$fig$ext"; break; }; done
    if [ -n "$found" ]; then SOURCES+=("$found"); else err "figure not found: $fig"; fi
  done < <(strip_comments "$f" | grep -oE '\\includegraphics(\[[^]]*\])?\{[^}]+\}' | sed -E 's/.*\{(.*)\}$/\1/')
done

BIBNAMES=$(strip_comments "$MAIN.tex" | grep -oE '\\bibliography\{[^}]+\}' | sed -E 's/.*\{(.*)\}/\1/' | tr ',' ' ')
for b in $BIBNAMES; do [ -f "$b.bib" ] || err "bibliography database $b.bib missing"; done

for f in "${SOURCES[@]}"; do
  case "$f" in /*|*..*) err "non-relative or parent path: $f" ;; esac
  case "$f" in stubs/*) err "stub file would be shipped: $f" ;; esac
  mkdir -p "$SRC/$(dirname "$f")"; cp -p "$f" "$SRC/$f"
done
note "sources   : ${SOURCES[*]}"

# ancillary files
if [ -d anc ]; then
  # anc/lean (a Lean formalisation in progress, with its multi-GB .lake build tree) is not shipped yet.
  (cd anc && find . \( -path ./lean -o -name .lake \) -prune -o -type f ! -name '*.pyc' ! -path '*/__pycache__/*' ! -name '.DS_Store' ! -name '*~' ! -name '.*.swp' -print0) |
    while IFS= read -r -d '' a; do mkdir -p "$SRC/anc/$(dirname "$a")"; cp -p "anc/$a" "$SRC/anc/$a"; done
  ANC_N=$(find "$SRC/anc" -type f | wc -l)
  note "anc/      : $ANC_N files, $(du -sh "$SRC/anc" | cut -f1)"
  if find "$SRC/anc" -type f \( -name '*.tex' -o -name '*.sty' -o -name '*.cls' -o -name '*.bbl' \) | grep -q .; then
    err "anc/ contains TeX files (arXiv: 'TeX files should not be included in the ancillary file directory')"
  fi
  JSPDF=$(find "$SRC/anc" -type f -name '*.pdf' -exec grep -la '/JavaScript\|/JS ' {} + 2>/dev/null || true)
  [ -n "$JSPDF" ] && err "anc/ PDFs with embedded JavaScript (arXiv rejects these): $JSPDF"
  [ -f "$SRC/anc/README" ] || [ -f "$SRC/anc/README.md" ] || [ -f "$SRC/anc/README.txt" ] || warn "anc/ has no README"
  if grep -rlE '/(home|tmp|Users)/' "$SRC/anc" >/dev/null 2>&1; then
    warn "anc/ files contain absolute paths: $(grep -rlE '/(home|tmp|Users)/' "$SRC/anc" | sed "s#$SRC/##" | tr '\n' ' ')"
  fi
else
  warn "no anc/ directory in $PAPER_DIR (ancillary files will be missing)"
fi

# ---------------------------------------------------------------- 2. generate main.bbl
BBL="$WORK/bbl"; mkdir -p "$BBL"
cp -a "$SRC/." "$BBL/"; rm -rf "$BBL/anc"
for b in $BIBNAMES; do cp -p "$b.bib" "$BBL/"; done
BST=$(strip_comments "$MAIN.tex" | grep -oE '\\bibliographystyle\{[^}]+\}' | sed -E 's/.*\{(.*)\}/\1/' | head -1)
if [ -n "$BST" ]; then            # a local style (e.g. production/amsplain-doi.bst) is used for main.bbl only
  for d in . production; do [ -f "$d/$BST.bst" ] && { mkdir -p "$BBL/$(dirname "$BST")"; cp -p "$d/$BST.bst" "$BBL/$BST.bst"; cp -p "$d/$BST.bst" "$BBL/"; note "bst       : $d/$BST.bst (local; not shipped, main.bbl is)"; break; }; done
fi
(
  cd "$BBL"
  "${RUN[@]}" pdflatex -interaction=nonstopmode -halt-on-error "$MAIN" >/dev/null 2>&1 || true
  if [ -n "$BIBNAMES" ]; then "${RUN[@]}" bibtex "$MAIN" >"$WORK/bibtex.out" 2>&1 || true; fi
  "${RUN[@]}" pdflatex -interaction=nonstopmode -halt-on-error "$MAIN" >/dev/null 2>&1 || true
  "${RUN[@]}" pdflatex -interaction=nonstopmode -halt-on-error "$MAIN" >/dev/null 2>&1 || true
)
if grep -q '^!' "$BBL/$MAIN.log" 2>/dev/null; then
  die "pdflatex error while generating $MAIN.bbl: $(grep -m1 -A3 '^!' "$BBL/$MAIN.log" | tr '\n' ' ' | cut -c1-300)"
fi
if [ -n "$BIBNAMES" ]; then
  [ -s "$BBL/$MAIN.bbl" ] || die "bibtex did not produce $MAIN.bbl (see $BBL/$MAIN.blg; rerun with --keep-temp)"
  cp -p "$BBL/$MAIN.bbl" "$SRC/$MAIN.bbl"
  BIBW=$(grep -c '^Warning--' "$BBL/$MAIN.blg" || true)
  [ "$BIBW" -gt 0 ] && warn "bibtex: $BIBW warnings: $(grep '^Warning--' "$BBL/$MAIN.blg" | head -5 | tr '\n' ';')"
  [ "$INCLUDE_BIB" = 1 ] && for b in $BIBNAMES; do cp -p "$b.bib" "$SRC/"; done
  note "bbl       : $MAIN.bbl ($(grep -c '\\bibitem' "$SRC/$MAIN.bbl") entries)"
fi

# ---------------------------------------------------------------- 3. lint staged sources
TEXFILES=$(cd "$SRC" && find . -name '*.tex' ! -path './anc/*' | sed 's#^\./##' | sort)
# The definitions of the draft markers themselves (macros.tex) are not hits; their *uses* are.
MARKER_DEFS='\\(new|renew|provide)command\*?\{?\\(to[d]o|status|NUM)\}?'
lint() {  # lint <pattern> <message> [lint|error] [exclude-pattern]
  local pat="$1" msg="$2" kind="${3:-lint}" excl="${4:-}" hits
  hits=$(cd "$SRC" && for f in $TEXFILES; do strip_comments "$f" | grep -nE -- "$pat" | grep -vE -- "$MARKER_DEFS" | sed "s#^#$f:#"; done || true)
  if [ -n "$excl" ] && [ -n "$hits" ]; then hits=$(printf '%s\n' "$hits" | grep -vE -- "$excl" || true); fi
  [ -z "$hits" ] && return 0
  local n; n=$(printf '%s\n' "$hits" | wc -l)
  if [ "$kind" = error ]; then err "$msg ($n): $(printf '%s\n' "$hits" | cut -c1-120 | head -5 | tr '\n' '|')"
  else lintw "$msg ($n): $(printf '%s\n' "$hits" | cut -c1-120 | head -5 | tr '\n' '|')"; fi
}
lint '/(home|tmp|Users)/|[A-Z]:\\\\' "absolute paths in TeX sources" error
lint '\\NUM([^A-Za-z]|$)' "\\NUM placeholder (uncertified numerical value) left in the text" error
lint '\\(to[d]o|status)([^A-Za-z]|$)' "internal draft-marker macros used"
lint 'T[B]D by Nic' "author placeholders (author block, date, pdfauthor)"
lint 'T[O]DO|FIXME|XXX|T[B]D' "placeholder text (to-do, fix-me, to-be-determined)" lint 'T[B]D by Nic'
lint '\\(text)?color\{([Rr]ed|[Mm]agenta)[}!]|\\f?colorbox' "red/magenta draft colouring or colour boxes"
lint '\\today' "\\today in sources (arXiv recommends a fixed date)"
lint '\\IfFileExists|stubs/' "stub fallback still present (use plain \\input)"
lint '\\texttt\{(cert|scripts|lemmas/scripts|paper)/' "repository-internal paths in text (point to anc/ files instead)"
if [ -d "$SRC/anc" ]; then   # placeholder text in the ancillary README (e.g. the licence line)
  ANCPH=$(cd "$SRC/anc" && grep -nE 'To be chosen|T[B]D|T[O]DO|FIXME' README* 2>/dev/null || true)
  [ -n "$ANCPH" ] && lintw "placeholder in anc/ README ($(printf '%s\n' "$ANCPH" | wc -l)): $(printf '%s\n' "$ANCPH" | cut -c1-120 | head -3 | tr '\n' '|')"
fi
NONASCII=$(cd "$SRC" && grep -nP '[^\x00-\x7F]' $TEXFILES $( [ -f "$MAIN.bbl" ] && echo "$MAIN.bbl") 2>/dev/null || true)
[ -n "$NONASCII" ] && lintw "non-ASCII characters: $(printf '%s\n' "$NONASCII" | cut -c1-120 | head -5 | tr '\n' '|')"

if [ "$WITH_README" = 1 ]; then
  cat > "$SRC/00README.json" <<EOF
{
  "spec_version": 1,
  "process": { "compiler": "pdflatex" },
  "sources": [ { "filename": "$MAIN.tex", "usage": "toplevel" } ],
  "texlive_version": 2025
}
EOF
fi

# ---------------------------------------------------------------- 4. tarball
mkdir -p "$OUT_DIR"
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
NAME="arxiv-src-$STAMP"
TARBALL="$OUT_DIR/$NAME.tar.gz"
if [ -z "${SOURCE_DATE_EPOCH:-}" ]; then
  # newest *source* mtime; the freshly generated main.bbl is excluded so that reruns on unchanged sources are byte-identical
  SOURCE_DATE_EPOCH=$(cd "$SRC" && find . -type f ! -name "$MAIN.bbl" -printf '%T@\n' | sort -n | tail -1 | cut -d. -f1)
fi
(cd "$SRC" && find . -type f | sed 's#^\./##' | LC_ALL=C sort) > "$WORK/filelist"
tar --sort=name --owner=0 --group=0 --numeric-owner --mtime="@$SOURCE_DATE_EPOCH" \
    -C "$SRC" -cf - -T "$WORK/filelist" | gzip -9n > "$TARBALL"

# ---------------------------------------------------------------- 5. verify as arXiv would
VER="$WORK/verify"; mkdir -p "$VER"
tar -xzf "$TARBALL" -C "$VER"
for bad in '*.aux' '*.log' '*.out' '*.toc' '*.blg' '*.pdf'; do
  if (cd "$VER" && find . -maxdepth 1 -name "$bad" | grep -q .); then err "tarball contains top-level $bad"; fi
done
[ -d "$VER/stubs" ] && err "tarball contains stubs/"
TOPLEVEL=$(cd "$VER" && grep -l '\\documentclass' ./*.tex 2>/dev/null | sed 's#^\./##' | tr '\n' ' ')
[ "$TOPLEVEL" = "$MAIN.tex " ] || warn "files with \\documentclass at top level: '$TOPLEVEL' (arXiv needs a unique toplevel)"

PASSES=0
(
  cd "$VER"
  for i in 1 2 3 4 5; do
    "${RUN[@]}" pdflatex -interaction=nonstopmode -halt-on-error "$MAIN" >"$WORK/verify-pass$i.out" 2>&1 || { echo "$i" > "$WORK/failed"; break; }
    echo "$i" > "$WORK/passes"
    grep -qE 'Rerun to get|Rerun LaTeX|may have changed' "$MAIN.log" || break
  done
)
PASSES=$(cat "$WORK/passes" 2>/dev/null || echo 0)
LOG="$VER/$MAIN.log"
[ -f "$WORK/failed" ] && err "pdflatex failed in verification (pass $(cat "$WORK/failed")): $(grep -m3 -A2 '^!' "$LOG" | tr '\n' ' ' | cut -c1-300)"
[ -f "$VER/$MAIN.pdf" ] || err "no PDF produced in verification"

if [ -f "$LOG" ]; then
  UNDEF=$(grep -cE "LaTeX Warning: (Reference|Citation) .* undefined|There were undefined references" "$LOG" || true)
  [ "$UNDEF" -gt 0 ] && err "undefined references/citations: $(grep -E 'LaTeX Warning: (Reference|Citation)' "$LOG" | head -5 | tr '\n' ';')"
  MULTI=$(grep -c "multiply defined" "$LOG" || true)
  [ "$MULTI" -gt 0 ] && warn "multiply defined labels: $MULTI"
  grep -q 'Rerun to get\|may have changed' "$LOG" && warn "labels not stable after $PASSES passes"
  MISSCH=$(grep -c 'Missing character' "$LOG" || true)
  [ "$MISSCH" -gt 0 ] && err "missing characters in fonts: $MISSCH"
  HYPW=$(grep -c 'Package hyperref Warning' "$LOG" || true)
  [ "$HYPW" -gt 0 ] && warn "hyperref warnings: $HYPW ($(grep 'Package hyperref Warning' "$LOG" | sort | uniq -c | head -3 | tr '\n' ';'))"
  OVH=$(grep -c '^Overfull \\hbox' "$LOG" || true)
  # '|| true': with pipefail, a log without overfull boxes would otherwise abort the script here.
  OVBIG=$(grep -oE '^Overfull \\hbox \(([0-9.]+)pt' "$LOG" | grep -oE '[0-9.]+' | awk '$1>10' | wc -l || true)
  OVV=$(grep -c '^Overfull \\vbox' "$LOG" || true)
  UNH=$(grep -c '^Underfull' "$LOG" || true)
  PAGES=$(grep -oE 'Output written on [^ ]+ \(([0-9]+) pages' "$LOG" | grep -oE '[0-9]+ pages' | cut -d' ' -f1 || true)
fi

# ---------------------------------------------------------------- 6. report
TB_BYTES=$(stat -c %s "$TARBALL")
UNPACKED=$(du -sb "$VER" --exclude="$MAIN.pdf" --exclude="$MAIN.log" --exclude="$MAIN.aux" --exclude="$MAIN.out" --exclude="$MAIN.toc" | cut -f1)
UNPACKED_SRC=$(cd "$SRC" && du -sb . | cut -f1)
ANC_BYTES=$( [ -d "$SRC/anc" ] && du -sb "$SRC/anc" | cut -f1 || echo 0)
SHA=$(sha256sum "$TARBALL" | cut -d' ' -f1)
NFILES=$(wc -l < "$WORK/filelist")
[ -f "$VER/$MAIN.pdf" ] && cp -p "$VER/$MAIN.pdf" "$OUT_DIR/$NAME.pdf"
[ -f "$LOG" ] && cp -p "$LOG" "$OUT_DIR/$NAME.pdflatex.log"
ln -sfn "$NAME.tar.gz" "$OUT_DIR/latest.tar.gz"

note ""
note "==== arXiv tarball report ($STAMP) ===="
note "tarball      : $TARBALL"
note "sha256       : $SHA"
note "size         : $TB_BYTES bytes compressed ($(numfmt --to=iec "$TB_BYTES")); sources $(numfmt --to=iec "$UNPACKED_SRC") unpacked, of which anc/ $(numfmt --to=iec "$ANC_BYTES")"
note "files ($NFILES):"
while IFS= read -r f; do note "   $f"; done < "$WORK/filelist"
note "verify       : pdflatex x$PASSES in a clean unpack (no bibtex; shipped $MAIN.bbl), $TEXVER"
note "pages        : ${PAGES:-?}"
note "overfull     : ${OVH:-?} hbox (${OVBIG:-?} wider than 10pt), ${OVV:-?} vbox; underfull ${UNH:-?}"
note "result       : $ERRORS error(s), $WARNINGS warning(s)"
printf '%s\n' "${REPORT_LINES[@]}" > "$OUT_DIR/$NAME.report.txt"
[ "$ERRORS" -eq 0 ] || { echo "FAILED -- see $OUT_DIR/$NAME.report.txt" >&2; exit 1; }
echo "OK -- $OUT_DIR/$NAME.report.txt"
