# HANDOFF.md — session bootstrap (written after Pass 43, 2026-06-24)

**State:** Pass 41 **closed the local-field assembly** — `IsNonarchimedeanLocalField L` for every
finite separable `L/K` (`Anabelian/ExtensionLocalFieldInstance.lean`). Pass 43 **discharged the
canonicity obligation**: `extensionValuativeRel K L = extensionValuativeRel K' L` for every tower
`K ⊆ K' ⊆ L` of finite separable extensions (`Anabelian/ExtensionCanonical.lean`, axiom-free) — the
last L-rung prerequisite before the ascent, and the reason `extensionValuativeRel` was a `def` not an
instance. (Pass 42 between them was governance: it discarded an unledgered 2-axiom orphan and added
the `scripts/preflight.sh` clean-tree gate.) Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom`
declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 44 — the ascent** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree),
`AXIOM_LEDGER.md` (state + the Pass-42 orphan incident record), `ROADMAP.md` (status header says
Pass 42), and the **tail of `NOTES.md`** (Passes 38–42: the assembly close + the Pass-42 cleanup).
**Session start:** `git status` — the tree must be clean. `.claude/` is now `.gitignore`d, so a clean
tree shows **nothing** untracked; `scripts/preflight.sh` clause 0 now *enforces* this (it fails on
any untracked file outside `.gitignore`). If anything is untracked, resolve it before new work
(`CLAUDE.md` clean-tree rule) — this is exactly how the Pass-42 orphan was caught.

## Where the mathematics stands

**The descent is closed and harvested** (P29–37): `ker θ₀ = G₁` unconditionally for every finite
separable `L/K`; the full P27/P28 quotient theory concrete at `𝒪_L` (`G₁` = the normal Sylow
`p`-subgroup of `G₀`). Serre IV §§1–2, finite level, zero conditional hypotheses, zero axioms.

**The assembly is COMPLETE** (P38–41): `IsNonarchimedeanLocalField L` for every finite separable
`L/K`, on the rung-1 valuative structure `extensionValuativeRel` (induced by `𝒪_L`). Parents 1
(`IsValuativeTopology`) + 3 (`IsNontrivial`) from P38; parent 2 (`LocallyCompactSpace`) from P41 via
`FiniteDimensional.proper` + the rung-1 = spectral topology identification (`isValuativeTopology_unique`).

**Canonicity is DISCHARGED** (P43): `extensionValuativeRel K L = extensionValuativeRel K' L` for a
tower `K ⊆ K' ⊆ L` of finite separable extensions (`Anabelian/ExtensionCanonical.lean`,
`extensionValuativeRel_base_independent`). The relation depends only on `𝒪_L`, which is
base-independent by integral-closure transitivity (self-consistency `𝒪[K'] = extensionIntegers K K'`
+ the transitivity engine `isIntegral_base_iff` + `RingEquiv.isIntegral_iff`). **Intermediate fields
are now usable as base fields — the ascent is open.**

## YOUR FIRST TASK — Pass 44: the ascent (Herbrand `φ`/`ψ`, upper numbering)

**Goal:** begin the **ascent** — Serre IV §3. With the assembly (P41) and canonicity (P43) in hand,
intermediate fields carry the full `IsNonarchimedeanLocalField` structure and serve as base fields,
so the quotient-compatibility that Herbrand's theorem expresses is finally statable. Targets, in
dependency order: (1) the **Herbrand functions** `φ_{L/K}`/`ψ_{L/K}` (the piecewise-linear transforms
of the lower-numbering filtration); (2) the **upper numbering** `G^v(L/K) = G_{ψ(v)}` and Herbrand's
theorem (upper numbering is what is compatible with quotients `Gal(L/K) ↠ Gal(M/K)`); (3) the limit
`G^v ≤ Gal(K̄/K)`; eventually Hasse–Arf.

**Before writing, inventory Mathlib's ramification API.** The L2 file
(`Anabelian/RamificationFiltration.lean`) carries a literal `TODO: Define higher ramification` for
`φ`/`ψ` — they are very likely **absent** from Mathlib (verify with grep/`exact?`/loogle; if genuinely
absent, that absence is itself a deliverable — log it as the next sub-target, do **not** `axiom` past
it). The lower-numbering filtration `ramificationGroup K (extensionIntegers K L) i` is in hand
(P23–37); `φ`/`ψ` are integrals/sums over it. This is real multi-pass mathematics — scope a first
concrete rung (e.g. the definition of `φ` and its monotonicity), do not attempt the whole of §3 at
once. Use the local toolchain in the loop (Pass 43's lesson: the draft had been written without one,
and three of its four errors were defeq/instance issues the compiler resolves instantly via
`lake env lean` probes).

## Environment (verify, then trust)

- **Probe environment**: a detached `lean`/`pkgs` toolchain in some prior session's `/sessions/.../tmp`
  may or may not survive a VM reset — test before trusting; rebuild from the NOTES-P36 recipe +
  P38–41 closure extensions if gone (~5 calls, ~20 min). Probes are `module`-headed files run with
  bare `lean` + the multi-package `LEAN_PATH`, publics + `.ir` only, ~0.5–1 s/iteration.
- **Workflow** (the verified P36–41 rhythm): source-grep Mathlib for every name BEFORE writing;
  kernel-verify every substantive proof abstractly in the probe env; **`lake build` runs HOST-SIDE**
  (ask the user; expect only the new file + root); **commits run HOST-SIDE** (the sandbox mount
  denies `unlink`, so in-sandbox `git commit`/`rm` are impossible, and in-sandbox `git status` leaves
  a stale `.git/index.lock` the user must `rm -f`).
- **Pre-commit gate**: `scripts/preflight.sh` (run host-side) — **clause 0 clean tree** (new, P42),
  long lines (chars not bytes), named statement-level binders, import-chain completeness
  (`scripts/chain_check.py`), and a `lake build` warning gate. A pass is committable only if it exits 0.
  **Never `grep -v` warnings out of probe output** — probe warnings are signal.
- **`scripts/refactor.sh`** (tracked, P42, **not yet run**): a one-shot flat→folders restructure of the
  44-file `Anabelian/` tree. Belongs in its own dedicated pass with a host `lake build` to verify; do
  not fold it into a math commit.

## House idioms (P36–41 vintage; older ones in NOTES P25–35)

- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake linter; the probe env cannot
  catch lake-level linters — only elaboration).
- The `letI`-tower statement pattern (relation → `ValuativeRel.topologicalSpace` →
  `IsTopologicalAddGroup.rightUniformSpace` → `isUniformAddGroup_of_addCommGroup`) is the house form
  for topological statements about `L`; instances fire automatically under it (probe-verified).
- D2 (the spectral/normed bridge) lives **entirely inside proofs** via `letI` — none in any
  statement, so `#print axioms` stays standard-only. Keep it that way.
- Renames/nesting that bit recent sessions: `sub_pow_expChar_pow_of_commute`;
  `Nat.exists_eq_pow_mul_and_not_dvd`; `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`
  (nested!); `RingEquiv.subringCongr`; `Valuation.integer` (not `Valued.integer`) via `Valued.v`.

## The queue after Pass 44

Continue the **ascent**: once `φ`/`ψ` and the upper numbering are in place, Herbrand's theorem and
Hasse–Arf (Serre IV §3). Separately, the **R1-floor** (axiomatizing L3 local class field theory to
reach a *conditional* R1 reconstruction result) is a ROADMAP-permitted but **deferred** option — if
taken, it must be a deliberate, ledgered decision (A1/A2 preserved in the NOTES Pass-42 entry) with
an explicit rule-5 argument that the conditional theorem does not trivially imply R1. R1–R3 remain
distant targets that must be earned, never axiomatized — the line between inputs and targets is drawn
in `ROADMAP.md` and is the project's reason for existing.
