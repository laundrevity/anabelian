/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.RamificationFiltration
import Mathlib

/-!
# The descent, rung 1: `𝒪_L` as a valuation subring of a finite extension (Pass 29)

First rung of the finite-extension local-field block. For `K` a nonarchimedean local field and
`L/K` **finite**, this file produces the object every L2 theorem has been waiting for:

> `extensionIntegers K L : ValuationSubring L` — the integral closure `𝒪_L = integralClosure
> 𝒪[K] L`, proved to be a **valuation subring** of `L`,

and discharges, at `A = 𝒪_L`, the hypotheses the abstract ramification theory (Passes 23–28) was
parametrized by:

* **`mem_or_inv_mem`** — the real content: this *is* the unique-extension-of-valuations theorem
  for complete fields, proved via the spectral norm (`x ∉ 𝒪_L ⟹ ‖x‖ > 1 ⟹ ‖x⁻¹‖ < 1 ⟹ x⁻¹
  integral`), with the **entire spectral/normed structure localized inside the proof field**
  (the Pass-18 `letI` discipline — nothing leaks to the statement, which is pure
  `integralClosure`).
* `IsLocalRing 𝒪_L` — **free** once it is a `ValuationSubring` (no Pass-18-style transport
  needed at finite level).
* `isNoetherianRing_extensionIntegers` — `𝒪_L` is **Noetherian** (`[Algebra.IsSeparable K L]`):
  Mathlib's `IsIntegralClosure.isNoetherianRing` over the DVR `𝒪[K]`.
* **`iInf_ramificationGroup_extensionIntegers`** — Pass 23's Krull separation hypothesis,
  **discharged at `𝒪_L`**: `⨅ i, G_i(L/K) = ⊥`.
* `Finite (decompositionSubgroup)` (from `AlgEquiv.fintype`) and
  **`exists_ramificationGroup_extensionIntegers_eq_bot`** — Pass 24's finiteness hypothesis and
  eventual triviality, discharged at `𝒪_L`.

With this, `ramificationGroup K (extensionIntegers K L) i` is the honest-to-Serre filtration of
a finite extension of local fields, with separating, eventually-trivial behavior **proved**, not
hypothesized.

## Honesty

* The **separability hypothesis** `[Algebra.IsSeparable K L]` on the Noetherian/finiteness
  results is honest: it is what Mathlib's integral-closure finiteness consumes (char-0 local
  fields: automatic; equal characteristic: a real restriction, same boundary as the Pass-14
  perfect-case narrowing — named, not hidden).
* **D2 status: the Pass-18 incursion pattern, reused.** The spectral/normed structure on `L`
  appears ONLY inside the `mem_or_inv_mem'` proof field of the definition (a `letI` chain);
  every statement in this file is `ValuativeRel`/`integralClosure`-native. Same logged
  containment as Pass 18; nothing new to watch.
* NOT yet built (the block's remaining rungs, named): `IsDiscreteValuationRing 𝒪_L`; finite
  residue field `𝓀_L`; the full `IsNonarchimedeanLocalField L` instance assembly; the
  **monogenicity discharge** (Serre IV §1 Prop. 5's own proof — the hypothesis of Passes 25/27/28
  becomes a theorem here, eventually); ramification-index/degree bookkeeping (`e·f = n`).
* No new `structure`/`class` beyond the `ValuationSubring` *instance* of an existing Mathlib
  structure (rule-2: `ValuationSubring` is Mathlib's, already calibrated; our definition is a
  witness for it, and Passes 22/26 already exhibit valuation subrings with genuinely different
  ramification behavior — collapse vs separation — so nothing new to pin). No owed witness.
  D1 N/A. Recovers nothing from an abstract group; R1–R3 untouched.
* `import Mathlib` wholesale, per the `GaloisIntegersLocal` precedent (the spectral chain's
  module paths are scattered); noted as in Pass 17/18.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open Polynomial

namespace Anabelian

open scoped ValuativeRel NNReal
open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The algebraic half of the spectral bridge, for a finite extension (the Pass-17 brick,
`L`-version): integrality over `𝒪[K]` is equivalent to the `K`-minimal polynomial having
coefficients in `𝒪[K]`. Norm-free, hence D2-free. -/
theorem isIntegral_iff_minpoly_coeff_mem_findim (x : L) :
    IsIntegral ↥𝒪[K] x ↔ ∀ i, (minpoly K x).coeff i ∈ (𝒪[K] : Subring K) := by
  have halg : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  constructor
  · intro hx i
    have hmap : minpoly K x = (minpoly ↥𝒪[K] x).map (algebraMap ↥𝒪[K] K) :=
      minpoly.isIntegrallyClosed_eq_field_fractions K L hx
    rw [hmap, coeff_map]
    exact (minpoly ↥𝒪[K] x).coeff i |>.2
  · intro h
    have hsub : (↑(minpoly K x).coeffs : Set K) ⊆ (𝒪[K] : Subring K) := by
      intro a ha
      rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact h i
    refine ⟨(minpoly K x).toSubring (𝒪[K] : Subring K) hsub,
      (Polynomial.monic_toSubring _ _ _).mpr (minpoly.monic halg), ?_⟩
    change aeval x _ = 0
    rw [← Polynomial.aeval_map_algebraMap K x,
        show algebraMap ↥𝒪[K] K = (𝒪[K] : Subring K).subtype from rfl,
        Polynomial.map_toSubring]
    exact minpoly.aeval K x

set_option synthInstance.maxHeartbeats 400000 in
-- `synthInstance.maxHeartbeats` raised exactly as in Pass 18: the `Valued.integer` instance
-- searches inside the spectral `letI` chain are expensive under `import Mathlib`. Search cost
-- only, not logical (`#print axioms` below is standard-only).
/-- **`𝒪_L`, as a valuation subring** (the descent's foundational object): the integral closure
`integralClosure 𝒪[K] L`, with `mem_or_inv_mem` — the unique-extension theorem for the complete
`K` — proved via the spectral norm, **localized entirely inside this proof field** (Pass-18
discipline; the statement is `integralClosure`-pure). -/
noncomputable def extensionIntegers : ValuationSubring L :=
  { (integralClosure ↥𝒪[K] L).toSubring with
    mem_or_inv_mem' := by
      intro x
      letI := IsTopologicalAddGroup.rightUniformSpace K
      haveI := isUniformAddGroup_of_addCommGroup (G := K)
      letI rk : (Valued.v (R := K)).RankOne :=
        { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
            MonoidWithZeroHom.ValueGroup₀.embedding
          strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
            MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
      letI nnf : NontriviallyNormedField K :=
        Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
      letI nfL : NormedField L := spectralNorm.normedField K L
      haveI ultL : IsUltrametricDist L :=
        IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
          (isNonarchimedean_spectralNorm (K := K) (L := L))
      letI vL : Valued L ℝ≥0 := NormedField.toValued
      have hmem : ∀ y : L, y ∈ (integralClosure ↥𝒪[K] L).toSubring ↔
          y ∈ Valued.integer L := by
        intro y
        have halg : IsIntegral K y := Algebra.IsIntegral.isIntegral y
        rw [Valuation.mem_integer_iff]
        change IsIntegral ↥𝒪[K] y ↔ _
        rw [isIntegral_iff_minpoly_coeff_mem_findim K L y]
        have hvy : (Valued.v y ≤ (1 : ℝ≥0)) ↔ spectralNorm K L y ≤ 1 := by
          rw [show Valued.v y = ‖y‖₊ from rfl, show spectralNorm K L y = ‖y‖ from rfl]
          exact_mod_cast Iff.rfl
        rw [hvy, show spectralNorm K L y = spectralValue (minpoly K y) from rfl,
            spectralValue_le_one_iff (minpoly.monic halg)]
        refine forall_congr' (fun i => ?_)
        rw [Valued.toNormedField.norm_le_one_iff]
        exact Iff.rfl
      rcases (Valued.v (R := L)).valuationSubring.mem_or_inv_mem x with h | h
      · exact Or.inl ((hmem x).mpr h)
      · exact Or.inr ((hmem x⁻¹).mpr h) }

/-- Membership in `𝒪_L` is integrality over `𝒪[K]`. -/
theorem mem_extensionIntegers_iff (x : L) :
    x ∈ extensionIntegers K L ↔ IsIntegral ↥𝒪[K] x :=
  Iff.rfl

/-- `𝒪_L` is **Noetherian** (`L/K` finite separable): Mathlib's integral-closure finiteness
over the DVR `𝒪[K]`, transported along the carrier identity. With Pass 23, this discharges the
Krull separation hypothesis at `𝒪_L`. -/
theorem isNoetherianRing_extensionIntegers [Algebra.IsSeparable K L] :
    IsNoetherianRing ↥(extensionIntegers K L) := by
  haveI h1 : IsNoetherianRing ↥(integralClosure ↥𝒪[K] L) :=
    IsIntegralClosure.isNoetherianRing ↥𝒪[K] K L ↥(integralClosure ↥𝒪[K] L)
  let e : ↥(integralClosure ↥𝒪[K] L) ≃+* ↥(extensionIntegers K L) :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
  exact isNoetherianRing_of_surjective _ _ e.toRingHom e.surjective

/-- **Pass 23's separation hypothesis, discharged at `𝒪_L`**: the ramification filtration of a
finite separable extension of local fields separates. -/
theorem iInf_ramificationGroup_extensionIntegers [Algebra.IsSeparable K L] :
    (⨅ i : ℕ, ramificationGroup K (extensionIntegers K L) i) = ⊥ := by
  haveI := isNoetherianRing_extensionIntegers K L
  exact iInf_ramificationGroup_eq_bot_of_isNoetherianRing K (extensionIntegers K L)

/-- The decomposition subgroup at `𝒪_L` is **finite** (`L/K` finite): it sits inside the finite
`L ≃ₐ[K] L`. Discharges the Pass-24/28 finiteness hypotheses at `𝒪_L`. -/
instance : Finite ↥((extensionIntegers K L).decompositionSubgroup K) := by
  haveI : Fintype (L ≃ₐ[K] L) := AlgEquiv.fintype K L
  exact Subtype.finite

/-- **Pass 24's eventual triviality, discharged at `𝒪_L`**: the filtration of a finite separable
extension of local fields is eventually trivial — some `G_i = ⊥`, proved, not hypothesized. -/
theorem exists_ramificationGroup_extensionIntegers_eq_bot [Algebra.IsSeparable K L] :
    ∃ i, ramificationGroup K (extensionIntegers K L) i = ⊥ := by
  haveI := isNoetherianRing_extensionIntegers K L
  exact exists_ramificationGroup_eq_bot K (extensionIntegers K L)
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top')

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms isIntegral_iff_minpoly_coeff_mem_findim
#print axioms extensionIntegers
#print axioms mem_extensionIntegers_iff
#print axioms isNoetherianRing_extensionIntegers
#print axioms iInf_ramificationGroup_extensionIntegers
#print axioms exists_ramificationGroup_extensionIntegers_eq_bot

end Anabelian
