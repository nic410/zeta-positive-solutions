#!/usr/bin/env python3
"""Cross-check every SHA-256 cited in Ledger.lean and LEDGER.md against ../SHA256SUMS.

Usage (from paper/anc/lean):  python3 scripts/check_ledger_hashes.py [--fix]
A citation has the form  `path/to/file` (sha256 <64 hex digits>)  or, in LEDGER.md tables,
`path/to/file` followed in the same table cell by a 64-hex-digit hash.  With --fix, stale hashes
are replaced by the current ones (only in the files of this directory).
Exit code 1 if a cited file is missing from SHA256SUMS or a hash differs (and --fix was not given).
"""
import re, sys, pathlib

here = pathlib.Path(__file__).resolve().parent.parent
sums_path = here.parent / "SHA256SUMS"
sums = {}
for line in sums_path.read_text().splitlines():
    if line.strip():
        h, f = line.split(maxsplit=1)
        sums[f.strip().removeprefix("./")] = h
fix = "--fix" in sys.argv
pat = re.compile(r"`([A-Za-z0-9_./{}-]+\.(?:json|py|txt|tsv|sh))`\s*\(?\s*(?:sha256\s+)?([0-9a-f]{64})")
bad = 0
for name in ["PositivityRigidity/Ledger.lean", "LEDGER.md"]:
    path = here / name
    if not path.exists():
        continue
    text = path.read_text()
    new = text
    for m in pat.finditer(text):
        f, h = m.group(1), m.group(2)
        cur = sums.get(f)
        if cur is None:
            print(f"MISSING  {name}: {f} not in SHA256SUMS"); bad += 1
        elif cur != h:
            print(f"STALE    {name}: {f} cites {h[:12]}…, SHA256SUMS has {cur[:12]}…")
            if fix:
                new = new.replace(h, cur)
            else:
                bad += 1
        else:
            print(f"OK       {name}: {f}")
    if fix and new != text:
        path.write_text(new)
        print(f"updated {name}")
print("all cited hashes match SHA256SUMS" if bad == 0 else f"{bad} problem(s)")
sys.exit(1 if bad else 0)
