#!/usr/bin/env bash
# Pre-commit gate for the anabelian project. Run from anywhere: scripts/preflight.sh
# Fails (exit 1) on: long lines, named statement-level binders, incomplete import chains,
# or ANY warning/error in `lake build`. A pass is committable only if this exits 0.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0

# 0. Clean tree: no untracked files outside .gitignore (orphan-prevention gate, added Pass 42).
#    `git ls-files --others --exclude-standard` = untracked AND not ignored — exactly the orphan
#    set. Staged/tracked files pass; stray untracked files (the 2026-05/06 orphan pattern, e.g.
#    an unledgered axiom file) fail the gate. To clear: `git add` the file, or add it to .gitignore.
#    This mechanically backstops CLAUDE.md's clean-tree rule: a pass cannot commit while orphans exist.
orphans=$(git ls-files --others --exclude-standard)
if [ -n "$orphans" ]; then
  echo "== UNTRACKED FILES (git add, or add to .gitignore — clean-tree rule, CLAUDE.md) =="
  echo "$orphans"
  fail=1
fi

# 1. Line length ≤ 100 in CHARACTERS (house rule; matches the lake linter).
#    NOT awk: macOS awk counts bytes, and the math glyphs (𝓀, −, ↪) are multibyte.
long=$(python3 -c '
import glob, sys
for path in sorted(glob.glob("Anabelian/*.lean")) + ["Anabelian.lean"]:
    for i, line in enumerate(open(path, encoding="utf-8"), 1):
        n = len(line.rstrip("\n"))
        if n > 100:
            print(f"{path}: line {i} ({n} chars)")
')
if [ -n "$long" ]; then echo "== LONG LINES =="; echo "$long"; fail=1; fi

# 2. Named statement-level letI/haveI binders (heuristic: 4-space indent = statement block).
#    Names there are never referenceable -> guaranteed unusedVariables warnings.
named=$(grep -nE '^ {4}(letI|haveI) [A-Za-z_][A-Za-z0-9_]* :' Anabelian/*.lean || true)
if [ -n "$named" ]; then echo "== NAMED STATEMENT BINDERS (anonymize: 'letI : T := ...') =="; echo "$named"; fail=1; fi

# 3. Import-chain completeness (the Pass-37/39 failure class).
python3 scripts/chain_check.py || fail=1

# 4. Full build; ANY warning or error fails the gate.
out=$(lake build 2>&1)
bad=$(echo "$out" | grep -E '^(⚠|✖)|warning:|error:' || true)
if [ -n "$bad" ]; then echo "== BUILD WARNINGS/ERRORS =="; echo "$bad"; fail=1; fi
echo "$out" | tail -1

if [ "$fail" -eq 0 ]; then echo "preflight: CLEAN — committable"; else echo "preflight: FAILED — do not commit"; fi
exit $fail
