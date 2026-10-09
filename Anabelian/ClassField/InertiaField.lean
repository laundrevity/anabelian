/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison
import Anabelian.ClassField.InertiaBridge
import Anabelian.ClassField.UnitFiltration
import Anabelian.Extension.InertiaResidueCover
import Anabelian.Quotient.ComapIntegers
import Anabelian.Quotient.AddVal

/-!
# The inertia field is unramified, and units are norms from it (Pass 100)

Let `L/K` be finite Galois over a nonarchimedean local field, `I = G_0(𝒪_L) ≤ Gal(L/K)` its
inertia group (`inertiaImage K L`), and `M` a field sitting between `K` and `L` whose image in
`L` is the fixed field `L^I`. This file proves, in the project's vocabulary and with
ClassFieldTheory's instance package on `M` under statement-level `letI`:

* **`finrank_residueField_eq`** — `[𝓀_M : 𝓀_K] = [𝓀_L : 𝓀_K]`: the residue map
  `𝓀_M → 𝓀_L` is a bijection. Injective as a field map; surjective because every residue class
  of `𝓀_L` contains an *inertia-fixed* integer (Pass 73's `map_residue_inertiaFixedIntegers_eq_top`
  — the project's own "`f(L/L^I) = 1`"), which lies in `L^I = M`. Compared through cardinalities
  `|𝓀| = q^f` (`Module.natCard_eq_pow_finrank`), so no compatibility of `𝓀_K`-structures is
  needed.
* **`ramificationIdx_eq_one_of_fieldRange_eq_fixedField`** — **`M/K` is unramified**:
  `e(M/K) · f(M/K) = [M : K]` (bridge), `[L : M] = |I| = e(L/K)` (Galois correspondence +
  bridge), `[L : K] = e(L/K) · f(L/K)` (bridge), and `f(M/K) = f(L/K)` force `e(M/K) = 1`.
  This is Serre I §7 Cor. 2 / IV §1 for the maximal unramified subextension, obtained here
  without the surjectivity `G_0(L/K) ↠ G_0(M/K)`.
* **`unitFiltration_zero_le_fieldNormSubgroup`** — **units are norms from an unramified
  extension**: `U⁰_K ≤ N_{M/K} Mˣ` when `e(M/K) = 1` (ClassFieldTheory's
  `normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure`: the norm group of an
  unramified extension is `{x | [M:K] ∣ v(x)}`).

`M` is abstract (`[Algebra M L] [IsScalarTower K M L]` with `fieldRange = fixedField I`) rather
than `↥(fixedField I)` itself, so that the `n = 0` case of `L34` can apply it to the *lift* of
`L^I` into `K^sep`, which is the member of ClassFieldTheory's family the coherence clause speaks
about.

## Honesty

The norm-group computation for unramified extensions, `|inertia| = e` and `e·f = n` are
**imported** (ledger "External dependencies"). The project's contributions are the residue-field
bijection (via Pass 73) and the degree bookkeeping. No `structure`/`class`; no owed witness.
Standard axioms only.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

section Inertia

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The inertia group of `L/K` inside `Gal(L/K)`**: Pass 23's `G_0(𝒪_L)` (a subgroup of the
decomposition group `D(𝒪_L)`, which is all of `Gal(L/K)` by Pass 52) pushed along the inclusion.
This is the right-hand side of `L34` at `n = 0`, once `G^0 = G_0` (Pass 45's
`upperRamificationGroup_zero`). -/
noncomputable def inertiaImage : Subgroup (L ≃ₐ[K] L) :=
  (ramificationGroup K (extensionIntegers K L) 0).map
    ((extensionIntegers K L).decompositionSubgroup K).subtype

theorem card_inertiaImage :
    Nat.card (inertiaImage K L) = Nat.card (ramificationGroup K (extensionIntegers K L) 0) :=
  Subgroup.card_map_of_injective Subtype.val_injective

end Inertia

section FixedField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
variable (M : Type) [Field M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
variable [FiniteDimensional K M]

/-- The inclusion `𝒪_M →+* 𝒪_L` (`𝒪_L ∩ M = 𝒪_M`, Pass 57's `extensionIntegers_comap_eq`). -/
noncomputable def integersInclusion :
    ↥(extensionIntegers K M) →+* ↥(extensionIntegers K L) :=
  (comapRingHom M (extensionIntegers K L)).comp (comapIntegersEquiv K M (L := L)).toRingHom

@[simp] theorem coe_integersInclusion (x : ↥(extensionIntegers K M)) :
    (integersInclusion K L M x : L) = algebraMap M L x := rfl

/-- The inclusion of integer rings is a local homomorphism (a unit of `𝒪_L` lying in `M` is a
unit of `𝒪_M`, Pass 59's `isUnit_comapRingHom_iff`). -/
instance isLocalHom_integersInclusion : IsLocalHom (integersInclusion K L M) := by
  refine ⟨fun a ha => ?_⟩
  have h := (isUnit_comapRingHom_iff M (extensionIntegers K L) _).mp ha
  simpa using h.map (comapIntegersEquiv K M (L := L)).symm.toRingHom

variable [IsGalois K L]

/-- **The residue map `𝓀_M → 𝓀_L` is surjective** when `M` fills the fixed field of inertia:
every residue class of `𝓀_L` contains an inertia-fixed integer (Pass 73), and inertia-fixed
elements of `L` come from `M`. -/
theorem residueField_map_integersInclusion_surjective
    (hcover : ∀ x : L, (∀ σ ∈ inertiaImage K L, σ x = x) → ∃ m : M, algebraMap M L m = x) :
    Function.Surjective (ResidueField.map (integersInclusion K L M)) := by
  intro y
  have htop := map_residue_inertiaFixedIntegers_eq_top K L
  have hy : y ∈ (inertiaFixedIntegers K L).map (residue ↥(extensionIntegers K L)) := by
    rw [htop]; exact Subring.mem_top y
  obtain ⟨a, ha, rfl⟩ := Subring.mem_map.mp hy
  have hfix : ∀ σ ∈ inertiaImage K L, σ (a : L) = a := by
    rintro σ ⟨τ, hτ, rfl⟩
    exact congrArg Subtype.val (ha ⟨τ, hτ⟩)
  obtain ⟨m, hm⟩ := hcover a hfix
  have hmI : m ∈ extensionIntegers K M := by
    rw [← extensionIntegers_comap_eq K M (L := L), ValuationSubring.mem_comap, hm]
    exact a.2
  refine ⟨residue _ ⟨m, hmI⟩, ?_⟩
  rw [ResidueField.map_residue]
  congr 1
  exact Subtype.ext hm

/-- The residue fields of `𝒪_M` and `𝒪_L` have the same (finite) cardinality. -/
theorem card_residueField_eq
    (hcover : ∀ x : L, (∀ σ ∈ inertiaImage K L, σ x = x) → ∃ m : M, algebraMap M L m = x) :
    Nat.card (ResidueField ↥(extensionIntegers K M)) =
      Nat.card (ResidueField ↥(extensionIntegers K L)) :=
  Nat.card_congr (Equiv.ofBijective _
    ⟨(ResidueField.map (integersInclusion K L M)).injective,
      residueField_map_integersInclusion_surjective K L M hcover⟩)

/-- **`[𝓀_M : 𝓀_K] = [𝓀_L : 𝓀_K]`** — the residue degrees agree, under the instance packages
on `M` and `L`; from the cardinality equality via `|𝓀| = q^f` and injectivity of `q^(·)`. -/
theorem finrank_residueField_eq [Algebra.IsSeparable K M]
    (hcover : ∀ x : L, (∀ σ ∈ inertiaImage K L, σ x = x) → ∃ m : M, algebraMap M L m = x) :
    letI := extensionValuativeRel K M
    letI := ValuativeRel.topologicalSpace M
    haveI := isNonarchimedeanLocalField_extension K M
    haveI := hasExtension_extensionValuativeRel K M
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    Module.finrank 𝓀[K] 𝓀[M] = Module.finrank 𝓀[K] 𝓀[L] := by
  let := extensionValuativeRel K M
  let := ValuativeRel.topologicalSpace M
  have := isNonarchimedeanLocalField_extension K M
  have := hasExtension_extensionValuativeRel K M
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have : IsLocalRing ↥(extensionIntegers K M).toSubring :=
    inferInstanceAs (IsLocalRing ↥(extensionIntegers K M))
  have : IsLocalRing ↥(extensionIntegers K L).toSubring :=
    inferInstanceAs (IsLocalRing ↥(extensionIntegers K L))
  have hM : Nat.card 𝓀[M] = Nat.card (ResidueField ↥(extensionIntegers K M)) :=
    Nat.card_congr (ResidueField.mapEquiv
      (RingEquiv.subringCongr (integer_extensionValuativeRel_eq K M))).toEquiv
  have hL : Nat.card 𝓀[L] = Nat.card (ResidueField ↥(extensionIntegers K L)) :=
    Nat.card_congr (ResidueField.mapEquiv
      (RingEquiv.subringCongr (integer_extensionValuativeRel_eq K L))).toEquiv
  have hcard := card_residueField_eq K L M hcover
  have : Module.Finite 𝓀[K] 𝓀[M] := Module.Finite.of_finite
  have : Module.Finite 𝓀[K] 𝓀[L] := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[M])
  have h2 := Module.natCard_eq_pow_finrank (K := 𝓀[K]) (V := 𝓀[L])
  refine Nat.pow_right_injective (a := Nat.card 𝓀[K]) Finite.one_lt_card ?_
  change Nat.card 𝓀[K] ^ Module.finrank 𝓀[K] 𝓀[M] = Nat.card 𝓀[K] ^ Module.finrank 𝓀[K] 𝓀[L]
  rw [← h1, ← h2, hM, hL, hcard]

/-- **`[L : M] = |G_0(𝒪_L)|`** when the image of `M` in `L` is the fixed field of inertia
(the Galois correspondence `[L : L^H] = |H|`, `IntermediateField.finrank_fixedField_eq_card`). -/
theorem finrank_eq_card_ramificationGroup_zero
    (hrange : (IsScalarTower.toAlgHom K M L).fieldRange =
      IntermediateField.fixedField (inertiaImage K L)) :
    Module.finrank M L = Nat.card (ramificationGroup K (extensionIntegers K L) 0) := by
  set F := IntermediateField.fixedField (inertiaImage K L) with hF
  have h1 : Module.finrank K M = Module.finrank K F := by
    rw [LinearEquiv.finrank_eq
        (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K M L)).toLinearEquiv,
      ← AlgHom.fieldRange_toSubalgebra, hrange]
    rfl
  have h2 : Module.finrank K M * Module.finrank M L =
      Module.finrank K M * Nat.card F.fixingSubgroup := by
    rw [Module.finrank_mul_finrank, h1, ← IntermediateField.finrank_fixedField_eq_card,
      hF, IntermediateField.fixingSubgroup_fixedField, Module.finrank_mul_finrank]
  have hpos : 0 < Module.finrank K M := Module.finrank_pos
  rw [Nat.eq_of_mul_eq_mul_left hpos h2, hF, IntermediateField.fixingSubgroup_fixedField,
    card_inertiaImage]

/-- **The fixed field of inertia is unramified over `K`**: if the image of `M` in `L` is
`L^{G_0}`, then `e(M/K) = 1` — in ClassFieldTheory's vocabulary, the ramification index of
`𝓂[M]` over `𝒪[K]` is one, under the project's instance package on `M`. From
`e(M/K)·f(M/K) = [M:K]`, `[M:K]·[L:M] = [L:K] = e(L/K)·f(L/K)`, `[L:M] = e(L/K)`, and
`f(M/K) = f(L/K)`. -/
theorem ramificationIdx_eq_one_of_fieldRange_eq_fixedField [Algebra.IsSeparable K M]
    (hrange : (IsScalarTower.toAlgHom K M L).fieldRange =
      IntermediateField.fixedField (inertiaImage K L)) :
    letI := extensionValuativeRel K M
    letI := ValuativeRel.topologicalSpace M
    haveI := isNonarchimedeanLocalField_extension K M
    haveI := hasExtension_extensionValuativeRel K M
    (𝓂[M] : Ideal 𝒪[M]).ramificationIdx 𝒪[K] = 1 := by
  let := extensionValuativeRel K M
  let := ValuativeRel.topologicalSpace M
  have := isNonarchimedeanLocalField_extension K M
  have := hasExtension_extensionValuativeRel K M
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hcover : ∀ x : L, (∀ σ ∈ inertiaImage K L, σ x = x) → ∃ m : M, algebraMap M L m = x := by
    intro x hx
    have hxF : x ∈ (IsScalarTower.toAlgHom K M L).fieldRange := by
      rw [hrange]; exact (IntermediateField.mem_fixedField_iff _ _).mpr hx
    obtain ⟨m, hm⟩ := AlgHom.mem_fieldRange.mp hxF
    exact ⟨m, hm⟩
  have hres := finrank_residueField_eq K L M hcover
  have hM := ramificationIdx_mul_finrank_residueField K M
  have hL := card_galoisGroup_eq_card_ramificationGroup_zero_mul K L
  have hdeg := finrank_eq_card_ramificationGroup_zero K L M hrange
  have htower := Module.finrank_mul_finrank K M L
  rw [IsGalois.card_aut_eq_finrank] at hL
  have hpos : 0 < Nat.card (ramificationGroup K (extensionIntegers K L) 0) *
      Module.finrank 𝓀[K] 𝓀[L] := by
    rw [← hL]; exact Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [one_mul]
  calc (𝓂[M] : Ideal 𝒪[M]).ramificationIdx 𝒪[K] *
        (Nat.card (ramificationGroup K (extensionIntegers K L) 0) * Module.finrank 𝓀[K] 𝓀[L])
      = ((𝓂[M] : Ideal 𝒪[M]).ramificationIdx 𝒪[K] * Module.finrank 𝓀[K] 𝓀[M]) *
          Module.finrank M L := by rw [hres, hdeg]; ring
    _ = Module.finrank K L := by rw [hM, htower]
    _ = _ := hL

open LocalFieldTheory.IsNonarchimedeanLocalField in
/-- **Units are norms from an unramified extension** (project form): if `e(M/K) = 1` for the
finite Galois `M/K`, then `U⁰_K = 𝒪_Kˣ ≤ N_{M/K} Mˣ` — ClassFieldTheory's unramified norm-group
computation `N_{M/K} Mˣ = {x | [M:K] ∣ v(x)}`, and units have `v = 0`. -/
theorem unitFiltration_zero_le_fieldNormSubgroup [IsGalois K M]
    (hunr :
      letI := extensionValuativeRel K M
      letI := ValuativeRel.topologicalSpace M
      haveI := isNonarchimedeanLocalField_extension K M
      haveI := hasExtension_extensionValuativeRel K M
      (𝓂[M] : Ideal 𝒪[M]).ramificationIdx 𝒪[K] = 1) :
    unitFiltration K 0 ≤ ClassFieldTheory.fieldNormSubgroup K M := by
  let := extensionValuativeRel K M
  let := ValuativeRel.topologicalSpace M
  have := isNonarchimedeanLocalField_extension K M
  have := hasExtension_extensionValuativeRel K M
  have : IsIntegralClosure 𝒪[M] 𝒪[K] M :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K M
  have : Module.Finite 𝒪[K] 𝒪[M] :=
    LocalFieldTheory.integerRing_moduleFinite_of_isIntegralClosure K M
  have : IsUnramifiedValuedExtension K M := ⟨hunr⟩
  intro u hu
  change u ∈ LocalFieldTheory.localNormSubgroup K M
  rw [LocalClassFieldTheory.normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure K M,
    LocalClassFieldTheory.mem_unramifiedNormSubgroup_iff]
  have hu0 : valuationMap K (Additive.ofMul u) = 0 := by
    rw [← integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero]
    rw [unitFiltration_zero] at hu
    exact hu
  rw [hu0]
  exact dvd_zero _

end FixedField

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms card_inertiaImage
#print axioms residueField_map_integersInclusion_surjective
#print axioms finrank_residueField_eq
#print axioms finrank_eq_card_ramificationGroup_zero
#print axioms ramificationIdx_eq_one_of_fieldRange_eq_fixedField
#print axioms unitFiltration_zero_le_fieldNormSubgroup

-- The imported ClassFieldTheory theorems consumed here (ledger: "External dependencies").
#print axioms LocalClassFieldTheory.normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure

end Anabelian
