# HANDOFF.md — session bootstrap (written after Pass 44, 2026-06-24)

**State:** Pass 43 **discharged the canonicity obligation** (`extensionValuativeRel K L =
extensionValuativeRel K' L` for towers `K ⊆ K' ⊆ L`), the last L-rung prerequisite. **Pass 44
opened the ascent**: the **Herbrand function** `φ(u) = ∫_0^u dt/(G_0 : G_t)` (Serre IV §3) — absent
from Mathlib — is constructed on the lower-numbering filtration and proved strictly monotone,
continuous, `φ(0)=0`, `φ=id` on `(-∞,0]`, `φ≤id` on `[0,∞)` (`Anabelian/HerbrandFunction.lean`,
axiom-free). Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations project-wide — keep
it that way. **YOUR FIRST TASK is Pass 45 — the inverse `ψ = φ⁻¹` and the upper numbering** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree),
`AXIOM_LEDGER.md` (state + tail Pass-44 entry), `ROADMAP.md` (status header says Pass 44), and the
**tail of `NOTES.md`** (Passes 41–44: assembly close, canonicity, the Herbrand function).
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
tower `K ⊆ K' ⊆ L` (`Anabelian/ExtensionCanonical.lean`, `extensionValuativeRel_base_independent`) —
the relation depends only on `𝒪_L`, base-independent by integral-closure transitivity. Intermediate
fields are now usable as base fields.

**The ascent is OPEN, rung 1 built** (P44): the Herbrand function `φ`
(`Anabelian/HerbrandFunction.lean`, `herbrandPhi K A`), defined literally as Serre's `∫_0^u dt/(G_0 :
G_t)` on the lower-numbering filtration (`ramificationGroup`, P23). The integrand `g_{⌈t⌉}/g_0` is
**antitone** (filtration decreases), so Mathlib's `intervalIntegral` API gives integrability,
`herbrandPhi_strictMono`, `herbrandPhi_continuous`, `herbrandPhi_zero`, `herbrandPhi_eq_id` (`u≤0`),
`herbrandPhi_le_self` (`u≥0`) — all axiom-free. Split into an abstract engine `herbrandPhiSeq (g : ℕ
→ ℝ)` (reuse for `ψ`) + the instantiation. **StrictMono + Continuous are the precondition for `ψ`.**

## YOUR FIRST TASK — Pass 45: the inverse `ψ = φ⁻¹` and the upper numbering

**Goal:** continue the ascent (Serre IV §3). Now that `φ` is **strictly monotone + continuous** (P44),
build `ψ = φ⁻¹` and then the upper numbering.

1. **`ψ = φ⁻¹`.** `φ` is `StrictMono` + `Continuous`; it is unbounded above (slopes `≥ 1/g_0 > 0` on
   an unbounded domain) and `φ(-1) ≥ -1`, so it is a continuous strictly-monotone bijection of
   `[-1,∞)` (or `ℝ`) onto its range. Inventory Mathlib for the inverse-of-strict-mono-continuous API
   (`StrictMono.orderIso`, `Continuous.strictMono...`, `OrderIso`/`Homeomorph` of an interval; or
   build `ψ` as the explicit piecewise function and prove `φ ∘ ψ = id`). Prove `ψ` strictly monotone,
   continuous, `ψ(0)=0`, and the **inverse identities** `φ (ψ v) = v`, `ψ (φ u) = u` on the range.
2. **Upper numbering** `G^v(L/K) := G_{⌈ψ(v)⌉}` (Serre's definition via `ψ`), then **Herbrand's
   theorem** — the upper numbering is compatible with quotients `Gal(L/K) ↠ Gal(M/K)`. This is where
   P43 canonicity + the tower theory earn their keep; it is the hard, multi-pass part.

**Method (the P43–44 lesson):** use the local toolchain **in the loop** — `lake build
Anabelian.<File>` for the real build (≈3 s incremental), and `lake env lean <scratch>.lean` for fast
throwaway probes of defeqs/instances/lemma names before committing to a proof. Scope ONE concrete
rung (e.g. just `ψ` + its basic properties); do not attempt all of §3 at once.

## Environment (verify, then trust)

- **Toolchain in-loop (P43–44 rhythm — preferred):** the host `lean`/`lake` (v4.30.0) is directly
  usable. `lake build Anabelian.<File>` is the real build (≈3 s incremental once deps are cached);
  `lake env lean <scratch>.lean` runs a throwaway probe with the full `LEAN_PATH` (import `Mathlib` +
  the project module, `#print axioms`/`example`/`#synth` to settle defeqs, instances, lemma names
  before editing the project file). Use it constantly — the P43 draft failed precisely because it was
  written without a compiler. Keep probe files in the scratchpad (outside the repo, so clause 0 stays
  clean). If running in a *sandboxed* session instead, the older detached-probe-env recipe (NOTES P36)
  is the fallback, and `lake build`/`git commit` may need to run host-side (the mount can deny
  `unlink`, leaving a stale `.git/index.lock` to `rm -f`).
- **Workflow**: source-grep Mathlib for every name BEFORE writing; probe substantive proofs with
  `lake env lean`; then `lake build` the project file; expect the new file + the root `Anabelian.lean`
  edit only.
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

## The queue after Pass 45

Continue the **ascent**: with `ψ` and the upper numbering in place, Herbrand's theorem and
Hasse–Arf (Serre IV §3). Separately, the **R1-floor** (axiomatizing L3 local class field theory to
reach a *conditional* R1 reconstruction result) is a ROADMAP-permitted but **deferred** option — if
taken, it must be a deliberate, ledgered decision (A1/A2 preserved in the NOTES Pass-42 entry) with
an explicit rule-5 argument that the conditional theorem does not trivially imply R1. R1–R3 remain
distant targets that must be earned, never axiomatized — the line between inputs and targets is drawn
in `ROADMAP.md` and is the project's reason for existing.
