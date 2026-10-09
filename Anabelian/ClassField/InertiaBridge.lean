/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
import Anabelian.ClassField.UpperBridge
import Anabelian.Quotient.Surjective

/-!
# The inertia bridge: `G_0(𝒪_L)` is ClassFieldTheory's inertia; `|G_0| = e`; `e·f = [L:K]`
(Pass 100)

The dependency's local-field layer (`ValuedFieldTheory`, inside `n-yamaguchi-0729/ClassFieldTheory`)
carries its own inertia subgroup of `Gal(L/K)` — `galoisGroupMaximalIdealInertiaOfIsIntegralClosure
K L`, the inertia of `𝓂[L]` for the Galois action on `𝒪[L]` — together with `|inertia| = e`
(Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`, instantiated) and the fundamental identity
`e · f = [L : K]`. This file identifies that inertia subgroup with the project's `G_0(𝒪_L)`
(Pass 23's `ramificationGroup K (extensionIntegers K L) 0`, pushed along `Subgroup.subtype`) under
the project's instance package on `L` (Passes 41/98), and transports the two numerical facts to
the project's group. Everything is stated with the package under statement-level `letI`/`haveI`,
as in `UpperBridge` (Pass 99); `card_galoisGroup_eq_card_ramificationGroup_zero_mul` is the
form the `n = 0` case of `L34` consumes.

* `inertia_eq_map_ramificationGroup_zero` — the identification, by `ext`: both carriers are
  `{σ | ∀ x ∈ 𝒪_L, σ x - x ∈ 𝔪_L}`; `D(𝒪_L) = ⊤` (Pass 52) supplies decomposition membership.
* `card_ramificationGroup_zero_eq_ramificationIdx` — `|G_0(𝒪_L)| = 𝓂[L].ramificationIdx 𝒪[K]`.
* `ramificationIdx_mul_finrank_residueField` — `e · [𝓀_L : 𝓀_K] = [L : K]` at the package.
* `card_galoisGroup_eq_card_ramificationGroup_zero_mul` — `|Gal(L/K)| = |G_0(𝒪_L)| · [𝓀_L : 𝓀_K]`.

## Honesty

The cardinality facts are **imported** (ledger "External dependencies"); the project's
contribution is the identification. No `structure`/`class`; no owed witness. Standard axioms only.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [Algebra K L] [FiniteDimensional K L]

section Separable

variable [Algebra.IsSeparable K L]

/-- **ClassFieldTheory's inertia subgroup is the project's `G_0(𝒪_L)`**, as subgroups of
`L ≃ₐ[K] L`, under the project's local-field package on `L`. -/
theorem inertia_eq_map_ramificationGroup_zero :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
      LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
    LocalFieldTheory.galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L =
      (ramificationGroup K (extensionIntegers K L) 0).map
        ((extensionIntegers K L).decompositionSubgroup K).subtype := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
  have hA := valuationSubring_extensionValuativeRel_eq K L
  have hD : ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K = ⊤ := by
    rw [hA]; exact decompositionSubgroup_extensionIntegers_eq_top K L
  rw [← hA]
  ext σ
  constructor
  · intro hσ
    have hσ' : ∀ x : ↥𝒪[L],
        LocalFieldTheory.galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x ∈ 𝓂[L] := hσ
    have hσD : σ ∈ ((ValuativeRel.valuation L).valuationSubring).decompositionSubgroup K := by
      rw [hD]; exact Subgroup.mem_top σ
    refine ⟨⟨σ, hσD⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_ramificationGroup_iff]
    intro a
    rw [zero_add, pow_one]
    exact hσ' a
  · rintro ⟨⟨τ, hτD⟩, hτ, rfl⟩
    rw [SetLike.mem_coe, mem_ramificationGroup_iff] at hτ
    intro x
    have := hτ x
    rwa [zero_add, pow_one] at this

open LocalFieldTheory in
/-- **The fundamental identity `e · f = [L : K]`** at the package: the ramification index of
`𝓂[L]` over `𝒪[K]` times the residue degree `[𝓀_L : 𝓀_K]` is the field degree
(ClassFieldTheory's `maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank`, with
`ramificationIdx'` converted to `ramificationIdx`). Separable `L/K` suffices. -/
theorem ramificationIdx_mul_finrank_residueField :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] * Module.finrank 𝓀[K] 𝓀[L] =
      Module.finrank K L := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
  have h := maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have : Module.Finite 𝒪[K] 𝒪[L] :=
    LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosure K L
  rwa [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp] at h

end Separable

section Galois

variable [IsGalois K L]

/-- **`|G_0(𝒪_L)| = e`**: the project's inertia group has order the ramification index of
`𝓂[L]` over `𝒪[K]` (ClassFieldTheory's `…_card_eq_ramificationIdx`, through the identification). -/
theorem card_ramificationGroup_zero_eq_ramificationIdx :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    haveI : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
      LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
    Nat.card (ramificationGroup K (extensionIntegers K L) 0) =
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
  rw [← LocalFieldTheory.galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx,
    inertia_eq_map_ramificationGroup_zero K L,
    Subgroup.card_map_of_injective Subtype.val_injective]

/-- **`|Gal(L/K)| = |G_0(𝒪_L)| · [𝓀_L : 𝓀_K]`** — the fundamental identity read on the
project's inertia group; the Galois group's order is `[L : K]` (`IsGalois.card_aut_eq_finrank`). -/
theorem card_galoisGroup_eq_card_ramificationGroup_zero_mul :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    Nat.card (L ≃ₐ[K] L) =
      Nat.card (ramificationGroup K (extensionIntegers K L) 0) * Module.finrank 𝓀[K] 𝓀[L] := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  rw [IsGalois.card_aut_eq_finrank, card_ramificationGroup_zero_eq_ramificationIdx K L,
    ramificationIdx_mul_finrank_residueField K L]

end Galois

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms inertia_eq_map_ramificationGroup_zero
#print axioms card_ramificationGroup_zero_eq_ramificationIdx
#print axioms ramificationIdx_mul_finrank_residueField
#print axioms card_galoisGroup_eq_card_ramificationGroup_zero_mul

-- The imported ClassFieldTheory theorems consumed here (ledger: "External dependencies").
open LocalFieldTheory in
#print axioms galoisGroupMaximalIdealInertiaOfIsIntegralClosure_card_eq_ramificationIdx
open LocalFieldTheory in
#print axioms maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
#print axioms LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure

end Anabelian
