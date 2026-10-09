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
for path in sorted(glob.glob("Anabelian/**/*.lean", recursive=True)) + ["Anabelian.lean"]:
    for i, line in enumerate(open(path, encoding="utf-8"), 1):
        n = len(line.rstrip("\n"))
        if n > 100:
            print(f"{path}: line {i} ({n} chars)")
')
if [ -n "$long" ]; then echo "== LONG LINES =="; echo "$long"; fail=1; fi

# 2. Named statement-level letI/haveI binders (heuristic: 4-space indent = statement block).
#    Names there are never referenceable -> guaranteed unusedVariables warnings.
named=$(grep -rnE '^ {4}(letI|haveI) [A-Za-z_][A-Za-z0-9_]* :' Anabelian --include='*.lean' || true)
if [ -n "$named" ]; then echo "== NAMED STATEMENT BINDERS (anonymize: 'letI : T := ...') =="; echo "$named"; fail=1; fi

# 3. Import-chain completeness (the Pass-37/39 failure class).
python3 scripts/chain_check.py || fail=1

# 3b. Statement ledger (added Pass 99): every file in Anabelian/Statements/ must (a) be reachable
#     from the root Anabelian.lean, (b) declare at least one `def … : Prop`, (c) contain no `axiom`,
#     and (d) elaborate on its own with `lake env lean`, with no error and no `sorry` (clause 5
#     below). The statements are audited *before* proofs are attempted — the statement is the
#     thing that can be silently wrong.
for f in Anabelian/Statements/*.lean; do
  [ -e "$f" ] || continue
  mod=$(echo "${f%.lean}" | tr '/' '.')
  if ! grep -q "^import ${mod}\$" Anabelian.lean; then
    echo "== STATEMENTS: $f not imported from Anabelian.lean =="; fail=1
  fi
  if ! grep -qE '^def [A-Za-z0-9_]+ : Prop :=' "$f"; then
    echo "== STATEMENTS: $f declares no 'def … : Prop' =="; fail=1
  fi
  if grep -qE '^\s*axiom\b' "$f"; then
    echo "== STATEMENTS: $f contains an axiom =="; fail=1
  fi
done

# 4. Full build; ANY warning or error fails the gate.
out=$(lake build 2>&1)
bad=$(echo "$out" | grep -E '^(⚠|✖)|warning:|error:' || true)
if [ -n "$bad" ]; then echo "== BUILD WARNINGS/ERRORS =="; echo "$bad"; fail=1; fi
echo "$out" | tail -1

# 5. Statement ledger elaboration (clause 3b(d)): each statements file must elaborate standalone.
for f in Anabelian/Statements/*.lean; do
  [ -e "$f" ] || continue
  sout=$(lake env lean "$f" 2>&1)
  if echo "$sout" | grep -qE 'error|sorry'; then
    echo "== STATEMENTS: $f does not elaborate cleanly =="; echo "$sout" | head -20; fail=1
  else
    echo "statements: $f elaborates ($(echo "$sout" | grep -c 'depends on axioms') axiom audits)"
  fi
done

if [ "$fail" -eq 0 ]; then echo "preflight: CLEAN — committable"; else echo "preflight: FAILED — do not commit"; fi
exit $fail
