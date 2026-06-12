#!/usr/bin/env python3
"""Import-chain completeness check (anabelian project).

Every project declaration NAME used in a file's CODE must be DEFINED somewhere in that
file's transitive project-import chain — the root `Anabelian.lean` reaching a file does NOT
make its names visible. This failed silently twice (Pass 37, Pass 39) before becoming
mechanical. Comments and docstrings are stripped first (they contain prose and forward
references by design).

Run from the repo root (or via scripts/preflight.sh). Exit 1 on any incomplete chain.
"""
import os
import re
import sys

IMP = re.compile(r"^import\s+(Anabelian\.[A-Za-z0-9_.]+)", re.M)
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:theorem|def|instance|lemma|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.M,
)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def strip_comments(src: str) -> str:
    """Remove Lean block comments (nested, incl. doc comments) and line comments."""
    out: list[str] = []
    i, n, depth = 0, len(src), 0
    while i < n:
        two = src[i : i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif two == "--":
            j = src.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def read_code(path: str) -> str:
    return strip_comments(open(path, encoding="utf-8").read())


def chain_of(path: str) -> set[str]:
    seen: set[str] = set()
    stack = IMP.findall(read_code(path))
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        src = mod.replace(".", "/") + ".lean"
        if os.path.exists(src):
            stack.extend(IMP.findall(read_code(src)))
    return seen


def main() -> int:
    files = sorted(
        "Anabelian/" + f for f in os.listdir("Anabelian") if f.endswith(".lean")
    )
    code = {f: read_code(f) for f in files}
    all_project: set[str] = set()
    for f in files:
        all_project |= set(DECL.findall(code[f]))
    bad = 0
    for f in files:
        defined: set[str] = set(DECL.findall(code[f]))
        for mod in chain_of(f):
            src = mod.replace(".", "/") + ".lean"
            if src in code:
                defined |= set(DECL.findall(code[src]))
        used = set(IDENT.findall(code[f]))
        missing = sorted((used & all_project) - defined)
        if missing:
            print(f"CHAIN INCOMPLETE {f}: uses {missing} not in its import chain")
            bad = 1
    if not bad:
        print(f"chain_check: {len(files)} files OK")
    return bad


if __name__ == "__main__":
    sys.exit(main())
