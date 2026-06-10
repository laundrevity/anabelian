/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueIso
import Anabelian.ResidueReductionInvariant
import Anabelian.ResidueReductionContinuity

/-!
# Rung L1, post-discharge: the named residue reduction and its kernel — the inertia subgroup (Pass 21)

Pass 20 discharged `residueReduction_surjective` as an *existential* (`∃ φ, Surjective φ`): the
concrete map was buried inside the proof. This pass **names** it and identifies its kernel — the
sub-target `ROADMAP.md` logged at Pass 5 as "tie `N` (the residue-reduction kernel) to the inertia
subgroup", then blocked on the absent valuation on `K̄`, now in hand.

## What is proved (all axiom-free; only the two `Surjective`/`≃*` results need `[PerfectField K]`)

* `Anabelian.galoisIntegers_stabilizer_eq_top` — **the decomposition group is everything**:
  `Gal(K̄/K)` stabilizes `𝔪[K̄]` (the unique maximal ideal of the local `𝒪[K̄]` is Galois-stable).
  Classically: a local field has one prime, so decomposition = the full group. Extracted from the
  Pass-20 proof as a named lemma (no `PerfectField`).
* `Anabelian.residueReductionHom` — **THE residue reduction**, now a named `def`:
  `Gal(K̄/K) →* Gal(𝓀̄/𝓀)`, the composite `galoisResidueAut ∘ stabilizerHom ∘ galoisToStabilizer`
  (no `PerfectField`; the *map* exists unconditionally — only surjectivity needs profiniteness).
* `Anabelian.residueReductionHom_surjective` `[PerfectField K]` — the Pass-20 discharge, now about
  the *named* map (the keystone `Ideal.Quotient.stabilizerHom_surjective_of_profinite` applied to
  the Passes 11–19 bricks).
* `Anabelian.galoisInertia` — **the inertia subgroup of `Gal(K̄/K)`, as a named `Subgroup`**:
  `(𝔪[K̄]).inertia Gal(K̄/K) = {σ | ∀ b ∈ 𝒪[K̄], σ b − b ∈ 𝔪[K̄]}` (Mathlib's `Ideal.inertia`,
  the classical pointwise condition `v(σx − x) > 0` — Serre, *Local Fields*, ch. IV §1). Typed as
  `Subgroup (Field.absoluteGaloisGroup K)` so all downstream statements live over one group
  instance.
* `Anabelian.mem_galoisInertia_iff` — the unfolded membership (definitional, kept for downstream
  use and as the bridge to Pass 4's abstract `mem_inertiaSubgroup_iff` characterization).
* `Anabelian.ker_residueReductionHom` — **the identification: `ker = inertia`.** The kernel of the
  residue reduction is exactly the inertia subgroup. This is the content Pass 5 logged as remaining
  L1 work; it rests on Mathlib's `Ideal.Quotient.ker_stabilizerHom` (kernel of `stabilizerHom` =
  inertia inside the stabilizer) + `galoisIntegers_stabilizer_eq_top` (stabilizer = everything) +
  injectivity of `galoisResidueAut`. **No `PerfectField`** — the identification is unconditional.
* `Anabelian.galoisInertia_normal` — inertia is **normal** in the full `Gal(K̄/K)` (it is a kernel;
  classically: because decomposition = ⊤). Unconditional.
* `Anabelian.unramifiedQuotientEquiv` `[PerfectField K]` — **the payoff, the classical unramified
  quotient theorem in its standard form**: `Gal(K̄/K) ⧸ I ≃* Gal(𝓀̄/𝓀)` with `I` *the named inertia
  subgroup* (not an existentially-quantified `N`). Upgrades Pass 5/20's `unramifiedQuotient_iso`
  from `∃ N, …` to the concrete statement.

## Relation to Pass 4 (`Anabelian/ResidueReduction.lean`)

Pass 4 proved the faithfulness half *abstractly* for a `ValuationSubring A` of any `L/K`:
`inertiaSubgroup = ker(reduction)` and `mem_inertiaSubgroup_iff` (inertia = pointwise residue
stabilizer). This pass realizes that picture *concretely* for `𝒪[K̄]/𝒪[K]` via `Ideal.inertia`
(membership: `σ b − b ∈ 𝔪[K̄]`, i.e. exactly "acts trivially on the residue ring `𝒪[K̄]/𝔪[K̄]`" —
the same condition `mem_inertiaSubgroup_iff` isolates). The *literal* `ValuationSubring`-form
(`ValuationSubring.inertiaSubgroup K A` with `A = 𝒪[K̄] : ValuationSubring K̄`) is **deliberately
not pursued**: it would require the spectral `Valued`/`ValuationSubring` structure on `K̄` *in
statements* (a statement-level D2 incursion — see `ROADMAP.md`, D2), whereas `Ideal.inertia` is
native to the project's `integralClosure` route. The `Ideal.inertia` form is canonical here
going forward (it is what L2's ramification filtration `G_i` will specialize: `G_0 = galoisInertia`,
`G_i = {σ | ∀ b, σ b − b ∈ 𝔪[K̄]^(i+1)}`).

## Honesty: what this is and is NOT

Genuine but **connective**: the hard content (the surjectivity) was earned in Passes 11–20; this
pass converts an existential into the named map + named kernel that downstream work (L2's
filtration, the tame/wild quotients) can actually consume, with the kernel identified against
Mathlib's `Ideal.inertia` (whose `ker_stabilizerHom` does the real work — found by Pass-21
inventory, *not* reproved). The continuity of `residueReductionHom` (it is a map of profinite
groups) is true but **not** proved here — logged as remaining L1 refinement in `ROADMAP.md`.

**Not reconstruction.** Everything is about the Galois groups of *given* fields `K`, `𝓀[K]`;
nothing is recovered from an abstract topological group. No reach toward R1–R3.

**No new owed witness.** `[PerfectField K]` on the two surjectivity-dependent results is the
tracked **owed generality** (the statement is *true* without it; the keystone proof needs it —
see `ROADMAP.md`), not a load-bearing-hypothesis claim. The kernel identification, normality, and
membership characterization are proved **without** it. No new `structure`/`class` (no rule-2
model obligation).

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged. D1 N/A (no `Algebra ℚ (AlgebraicClosure ℚ)`); D2 unchanged (3a's localized
incursion in `GaloisIntegersLocal` — this file adds none; `Ideal.inertia` needs no valuation
on `K̄`).
-/

open scoped ValuativeRel Pointwise

namespace Anabelian

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] isLocalRing_galoisIntegers

set_option synthInstance.maxHeartbeats 1000000
-- file-wide: as in Pass 20, the `MulAction (Gal(K̄/K)) (Ideal 𝒪[K̄])` / stabilizer instance
-- searches are expensive under `import Mathlib` + the Anabelian instances; they resolve, just past
-- the default. A search-cost matter, not logical (`#print axioms` below is standard-only).

/-- **The decomposition group is everything.** `Gal(K̄/K)` stabilizes `𝔪[K̄]`: each `σ` permutes
the maximal ideals of `𝒪[K̄]` (`σ • 𝔪[K̄] = (𝔪[K̄]).comap σ⁻¹` is maximal), and the local `𝒪[K̄]`
(Pass 18) has only one. Classically: a local field has a unique prime, so the decomposition group
of `𝔪[K̄]` is the full absolute Galois group. Extracted from the Pass-20 discharge as a named
lemma; no `PerfectField` needed. -/
theorem galoisIntegers_stabilizer_eq_top :
    MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_eq_comap]
  exact eq_maximalIdeal inferInstance

/-- The (iso)morphism `Gal(K̄/K) →* stabilizer 𝔪[K̄]` packaging `galoisIntegers_stabilizer_eq_top`:
every Galois element, bundled with the proof that it stabilizes `𝔪[K̄]`. Surjective
(`galoisToStabilizer_surjective`), so `stabilizerHom`'s domain restriction is no restriction. -/
def galoisToStabilizer :
    Field.absoluteGaloisGroup K →*
      ↥(MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
        (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)))) where
  toFun σ := ⟨σ, by rw [galoisIntegers_stabilizer_eq_top]; exact Subgroup.mem_top σ⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `galoisToStabilizer` is surjective (immediate from `stabilizer = ⊤`). -/
theorem galoisToStabilizer_surjective :
    Function.Surjective (galoisToStabilizer K) :=
  fun τ => ⟨τ.1, Subtype.ext rfl⟩

/-- **THE residue reduction, as a named map** (Pass 21; previously existential inside the Pass-20
discharge): `Gal(K̄/K) →* Gal(𝓀̄/𝓀)`, the composite of `galoisToStabilizer` (decomposition = ⊤),
Mathlib's `Ideal.Quotient.stabilizerHom` (act on `𝒪[K̄]/𝔪[K̄]`), and `galoisResidueAut` (Pass 19's
identification `Aut(𝓀̄/𝓀[K]) ≃* Gal(𝓀̄/𝓀)`). The *map* needs no `PerfectField` — only its
surjectivity does (`residueReductionHom_surjective`). Its kernel is the inertia subgroup
(`ker_residueReductionHom`), unconditionally. -/
noncomputable def residueReductionHom :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K] :=
  (galoisResidueAut K).toMonoidHom.comp
    ((Ideal.Quotient.stabilizerHom
        (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)))
        (maximalIdeal ↥𝒪[K])
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).comp
      (galoisToStabilizer K))

set_option maxHeartbeats 1000000 in
-- elaboration heartbeats raised for the keystone application, exactly as in the Pass-20 discharge.
/-- **The residue reduction is surjective** — the Pass-20 discharge, restated for the *named* map
(`residueReduction_surjective` in `UnramifiedQuotient.lean` is now a corollary). Carries the
`[PerfectField K]` narrowing (the keystone needs `Gal(K̄/K)` profinite = `IsGalois K K̄` ⟺ `K`
perfect); the imperfect equal-characteristic case is the tracked remainder in `ROADMAP.md`. -/
theorem residueReductionHom_surjective [PerfectField K] :
    Function.Surjective (residueReductionHom K) := by
  letI : TopologicalSpace ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := ⊥
  haveI : DiscreteTopology ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := ⟨rfl⟩
  haveI := continuousSMul_galoisIntegers K
  haveI := galoisIntegers_algebraIsInvariant K
  have hsurj := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (maximalIdeal ↥𝒪[K]) (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)))
  rw [residueReductionHom]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (galoisResidueAut K).surjective.comp (hsurj.comp (galoisToStabilizer_surjective K))

/-- **The inertia subgroup of `Gal(K̄/K)`, named.** `Ideal.inertia` of `𝔪[K̄]`:
`{σ | ∀ b ∈ 𝒪[K̄], σ b − b ∈ 𝔪[K̄]}` — the classical pointwise condition (`v(σx − x) > 0`;
Serre, *Local Fields*, ch. IV §1), i.e. "acts trivially on the residue field". Typed as a
`Subgroup (Field.absoluteGaloisGroup K)` so the kernel identification and the quotient below live
over a single group-instance path. Normal (`galoisInertia_normal`); equal to the kernel of the
residue reduction (`ker_residueReductionHom`). L2's ramification filtration will specialize this
(`G_0 = galoisInertia`; `G_i` replaces `𝔪[K̄]` by `𝔪[K̄]^(i+1)`). -/
noncomputable def galoisInertia : Subgroup (Field.absoluteGaloisGroup K) :=
  (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))).inertia
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)

/-- Membership in the inertia subgroup, unfolded: `σ ∈ I ↔ ∀ b ∈ 𝒪[K̄], σ b − b ∈ 𝔪[K̄]` — the
concrete realization of Pass 4's abstract `mem_inertiaSubgroup_iff` ("acts trivially on the
residue field") for `𝒪[K̄]/𝒪[K]`. (Stated for `σ` in the `AlgEquiv` form of the Galois group,
where the `MulSemiringAction` on `𝒪[K̄]` is registered.) -/
theorem mem_galoisInertia_iff (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    σ ∈ galoisInertia K ↔
      ∀ b : ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)),
        σ • b - b ∈ maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) :=
  AddSubgroup.mem_inertia

/-- **The identification `N = inertia`** — the sub-target logged at Pass 5 ("tie `N` to the
inertia subgroup"), closed: the kernel of the residue reduction is exactly the inertia subgroup.
Proof: `galoisResidueAut` is injective, so `ker(residueReductionHom) = ker(stabilizerHom ∘
galoisToStabilizer)`; Mathlib's `Ideal.Quotient.ker_stabilizerHom` identifies `ker(stabilizerHom)`
with inertia-inside-the-stabilizer, and `stabilizer = ⊤` (`galoisIntegers_stabilizer_eq_top`)
collapses the `subgroupOf`. **No `PerfectField`** — the identification holds for the map itself,
surjective or not. -/
theorem ker_residueReductionHom :
    (residueReductionHom K).ker = galoisInertia K := by
  ext σ
  have h := Subgroup.ext_iff.mp (Ideal.Quotient.ker_stabilizerHom
    (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) (maximalIdeal ↥𝒪[K])
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) (galoisToStabilizer K σ)
  rw [MonoidHom.mem_ker] at h
  rw [MonoidHom.mem_ker, residueReductionHom]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    EmbeddingLike.map_eq_one_iff]
  exact h.trans Subgroup.mem_subgroupOf

/-- **Inertia is normal in the full absolute Galois group** — because it is a kernel
(`ker_residueReductionHom`); classically, because the decomposition group is everything
(`galoisIntegers_stabilizer_eq_top`). Unconditional (no `PerfectField`). -/
instance galoisInertia_normal : (galoisInertia K).Normal := by
  rw [← ker_residueReductionHom]
  exact MonoidHom.normal_ker (residueReductionHom K)

/-- **The unramified quotient theorem, classical form** (upgrading Pass 5/20's existential
`unramifiedQuotient_iso`): `Gal(K̄/K) ⧸ I ≃* Gal(𝓀̄/𝓀)` with `I = galoisInertia K` the *named*
inertia subgroup — decomposition mod inertia is the residue Galois group, and here decomposition
is everything. Carries `[PerfectField K]` from the surjectivity (the tracked narrowing). -/
noncomputable def unramifiedQuotientEquiv [PerfectField K] :
    (Field.absoluteGaloisGroup K ⧸ galoisInertia K) ≃* Field.absoluteGaloisGroup 𝓀[K] :=
  (QuotientGroup.quotientMulEquivOfEq (ker_residueReductionHom K)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residueReductionHom_surjective K))

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms galoisIntegers_stabilizer_eq_top
#print axioms galoisToStabilizer
#print axioms galoisToStabilizer_surjective
#print axioms residueReductionHom
#print axioms residueReductionHom_surjective
#print axioms galoisInertia
#print axioms mem_galoisInertia_iff
#print axioms ker_residueReductionHom
#print axioms galoisInertia_normal
#print axioms unramifiedQuotientEquiv

end Anabelian
