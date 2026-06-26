# HANDOFF.md — session bootstrap (written after Pass 49, 2026-06-26)

**State:** Pass 43 **discharged the canonicity obligation** (the last L-rung prerequisite). **Passes
44–49 built the Herbrand machinery** (Serre IV §§1, 3, all absent from Mathlib, all axiom-free): the
**Herbrand function** `φ` (`Anabelian/HerbrandFunction.lean`, P44 — strictly monotone, continuous),
its inverse **`ψ = φ⁻¹` + the upper numbering** `G^v(L/K) = G_{⌈ψ(v)⌉}` (`Anabelian/UpperNumbering.lean`,
P45), the **subgroup compatibility** `H_u = H ∩ G_u` (Serre IV §1 Prop. 2,
`Anabelian/RamificationSubgroup.lean`, P46), the **slope** `φ'(u) = 1/(G_0 : G_u)`
(`Anabelian/HerbrandSlope.lean`, P47), the **explicit piecewise-linear formula** for `φ`
(`Anabelian/HerbrandFormula.lean`, P48), and the **`ψ` slope** `ψ'(v) = (G_0 : G_{ψ(v)})`
(`Anabelian/HerbrandPsiSlope.lean`, P49). Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom`
declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 50 — begin the
quotient-ramification theory (toward Herbrand's theorem), or a final clean `φ`/`ψ`-deepening**
(below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree, **governance
consistency**), `AXIOM_LEDGER.md` (state + tail Pass-49 entry), `ROADMAP.md` (status header says
Pass 49), and the **tail of `NOTES.md`** (Passes 41–49: assembly, canonicity, the full Herbrand
`φ`/`ψ` analytic theory — monotonicity, continuity, both slopes, `φ`'s closed form — + upper
numbering + Prop. 2).
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

**The ascent is OPEN, rungs 1–6 built** (P44–49): the Herbrand function `φ`
(`Anabelian/HerbrandFunction.lean`, `herbrandPhi K A`, Serre's `∫_0^u dt/(G_0 : G_t)`; integrand
antitone ⟹ clean `intervalIntegral` analysis ⟹ `herbrandPhi_strictMono`/`_continuous`/`_zero`/`_eq_id`
/`_le_self`), its inverse `ψ` (`Anabelian/UpperNumbering.lean`, `herbrandPsi K A` via
`Function.invFun`; `herbrandPsi_strictMono`/`_continuous`/`_zero`/`_eq_id`, inverse identities
`herbrandPhi_psi`/`herbrandPsi_phi`), the **upper numbering** `upperRamificationGroup K A v =
G_{⌈ψ(v)⌉}` (`_zero` = `G_0`, `_antitone`, `_eventually_bot`), the **subgroup compatibility**
`H_u = H ∩ G_u` (`Anabelian/RamificationSubgroup.lean`, `ramificationGroup_eq_comap`/`_map_eq`, the
restriction `decompositionRestrict : Gal(L/K') →* Gal(L/K)`), the **`φ` slope** `φ'(u) = 1/(G_0:G_u)`
(`Anabelian/HerbrandSlope.lean`, `herbrandPhi_hasDerivAt_Ioo`, via FTC), the **explicit
piecewise-linear formula** `φ(u) = (|G_1|+…+|G_n|+(u−n)|G_{n+1}|)/|G_0|`
(`Anabelian/HerbrandFormula.lean`, `herbrandPhi_eq_affine_formula`/`herbrandPhi_natCast`), and the
**`ψ` slope** `ψ'(v) = (G_0:G_{ψ(v)})` (`Anabelian/HerbrandPsiSlope.lean`, `herbrandPsi_hasDerivAt`,
via the inverse function theorem). Both `φ`/`ψ` are abstract engines
`herbrandPhiSeq`/`herbrandPsiSeq (g : ℕ → ℝ)` + the ramification instantiation. All axiom-free. The
`φ`/`ψ` **analytic theory is now complete** — only the *arithmetic* wall remains.

## YOUR FIRST TASK — Pass 50: the quotient-ramification theory (toward Herbrand's theorem)

**Goal:** `φ`-transitivity `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` (Serre IV §3 Prop. 15) and Herbrand's
theorem `(G/H)^v = G^v H/H` (Prop. 14). The analytic side is done; **what remains is the
index-multiplicativity** `1/(G_0:G_u) = 1/((G/H)_0 : (G/H)_{φ_{L/K'}(u)}) · 1/(H_0 : H_u)`, i.e. the
**quotient relationship** `(G/H)_{φ(u)} = G_u H/H` (Serre's Lemma 5). `H_u = H ∩ G_u` (P46) is the
*subgroup* half; the open *quotient* half is how the filtration of `Gal(K'/K)` (the project's
`ramificationGroup K 𝒪_{K'}`) relates to `G`'s via the restriction `Gal(L/K) ↠ Gal(K'/K)`. **This is
a genuine multi-pass project** (Mathlib has no quotient-ramification API; the core is the arithmetic
of how `i_{K'/K}(σ̄)` relates to the `i_{L/K}` of the lifts of `σ̄`).

**Scope the FIRST brick of it, complete and axiom-free** — e.g. set up the quotient restriction
`Gal(L/K) ↠ Gal(K'/K)` (Mathlib's `AlgEquiv.restrictNormalHom`, for `K'/K` Galois) and its
interaction with the decomposition groups (the quotient analogue of P46's `decompositionRestrict`),
as the group-theoretic skeleton — **without** the hard ramification arithmetic. Do NOT half-build the
arithmetic (clean partial > half-discharge). **Alternatively**, a final clean `φ`/`ψ`-deepening: the
**`ψ` closed form** (piecewise-linear, breakpoints at `φ(n)`, symmetric to P48) or **concavity** of
`φ` (blocked via Mathlib's `concaveOn_of_deriv` — `φ` isn't `DifferentiableOn` — so it needs a
from-scratch piecewise/secant argument; only attempt if you want the challenge).

**Method (the P43–49 rhythm):** local toolchain **in the loop** — `lake build Anabelian.<File>`
(≈3 s incremental) for the real build, `lake env lean <scratch>.lean` for throwaway probes of
defeqs/instances/lemma names before committing. Scope tightly; one rung.

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
  flat `Anabelian/` tree. Belongs in its own dedicated pass with a host `lake build` to verify; do
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

## The queue after Pass 50

Continue the **ascent**: build out the quotient-ramification theory → `φ`-transitivity and
**Herbrand's theorem** `(G/H)^v = G^v H/H`, then Hasse–Arf and the limit `G^v ≤ Gal(K̄/K)` (Serre IV
§3); the `ψ` closed form / concavity remain as optional clean deepening. Separately, the **R1-floor**
(axiomatizing L3 local class field theory to
reach a *conditional* R1 reconstruction result) is a ROADMAP-permitted but **deferred** option — if
taken, it must be a deliberate, ledgered decision (A1/A2 preserved in the NOTES Pass-42 entry) with
an explicit rule-5 argument that the conditional theorem does not trivially imply R1. R1–R3 remain
distant targets that must be earned, never axiomatized — the line between inputs and targets is drawn
in `ROADMAP.md` and is the project's reason for existing.
