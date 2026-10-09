/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The unit filtration of a nonarchimedean local field (Pass 99)

For `K` a nonarchimedean local field with integers `𝒪[K]`, maximal ideal `𝓂[K]` and residue
field `𝓀[K]`, the **higher unit groups** are

* `U⁰ = 𝒪[K]ˣ` (the units), and
* `Uᵐ = 1 + 𝓂[K]^m` for `m ≥ 1` (the `m`-th principal units),

all realised as subgroups of `Kˣ` (`unitFiltration K m`). This is the multiplicative side of
the Pass-24/27 characters: the additive character `θ_i : G_i/G_{i+1} ↪ 𝓀⁺` (`i ≥ 1`) and the
tame character `θ_0 : G_0/G_1 ↪ 𝓀ˣ` have as their arithmetic counterparts the layers
`Uᵐ/Uᵐ⁺¹ ↪ 𝓀⁺` (`m ≥ 1`) and `U⁰/U¹ ≃ 𝓀ˣ` — exactly the groups the ramification
correspondence `θ(Uⁿ) = Gⁿ` of local class field theory (Serre, *Local Fields*, XV §2;
statement ledger entry `L34`) matches with the upper-numbering groups.

## Design

`Uᵐ` is defined in two steps. At the ring level, `integerUnitFiltration K m : Subgroup 𝒪[K]ˣ`
is the kernel of `𝒪[K]ˣ →* (𝒪[K] ⧸ 𝓂[K]^m)ˣ` — so `m = 0` gives all units (the quotient
ring is trivial) and `m ≥ 1` gives `w ≡ 1 mod 𝓂^m` with no case split. Then
`unitFiltration K m : Subgroup Kˣ` is its image under the injective hom `𝒪[K]ˣ →* Kˣ`
(`integerUnitsHom`), and `integerUnitsEquiv K m : integerUnitFiltration K m ≃* unitFiltration K m`
(`Subgroup.equivMapOfInjective`) transports every computation between the two pictures.

## Main results

* `mem_unitFiltration_iff` — `u ∈ Uᵐ ↔ ∃ w : 𝒪[K]ˣ, w − 1 ∈ 𝓂^m ∧ (w : K) = u`.
* `unitFiltration_antitone` — `Uⁿ ≤ Uᵐ` for `m ≤ n`.
* `unitFiltration_zero_eq_unitGroup` — `U⁰` is Mathlib's `(valuation K).valuationSubring.unitGroup`:
  `u ∈ U⁰ ↔ v(u) = 1`.
* `unitsQuotEquivResidueUnits : U⁰ ⧸ U¹ ≃* 𝓀[K]ˣ` — reduction of units
  (`IsLocalRing.surjective_units_map_of_local_ringHom` for surjectivity; the kernel is `U¹`
  by `Ideal.Quotient.eq`).
* For `m ≥ 1` and a uniformizer `π` (`𝓂[K] = span {π}`): the **depth-`m` coefficient**
  `unitCoeff π hπ w` with `w − 1 = π^m · unitCoeff w` (unique, as `π^m` is a nonzerodivisor),
  the homomorphism `unitLayerHom π hπ hm : Uᵐ →* Multiplicative 𝓀[K]` (`w ↦ unitCoeff w mod 𝓂`;
  multiplicativity is `(1 + π^m a)(1 + π^m b) = 1 + π^m (a + b + π^m ab)` with `π^m ab ∈ 𝓂`),
  its kernel `ker = Uᵐ⁺¹` (`ker_unitLayerHom`), its surjectivity, and the induced
  **injective** (indeed bijective) `unitLayerQuotHom : Uᵐ ⧸ Uᵐ⁺¹ →* Multiplicative 𝓀[K]`, with
  the additive form `unitLayerQuotAddHom : Additive (Uᵐ ⧸ Uᵐ⁺¹) →+ 𝓀[K]`.

The coefficient map depends on the uniformizer: changing `π` to `π·c` rescales it by
`residue c ^ m` (not recorded here; the Pass-25/27 characters have the same dependence).

## Scope and honesty

Pure DVR/local-ring algebra over Mathlib's `IsNonarchimedeanLocalField` API; nothing about
Galois groups, reciprocity, or the correspondence itself. This is design row P97 of the
Pass-95 unit-quotient program, kept (the only row kept) because L3.4 needs `Uᵐ` as the
*source* side of `θ(Uⁿ) = Gⁿ`; the remaining rows P98–P102 are retired this pass (ROADMAP).
No `structure`/`class`; the load-bearing hypothesis `1 ≤ m` of the layer homomorphism is the
same `m ≥ 1` of Pass 27 (`residue_one_add_pow_mul`); its failure at `m = 0` is not claimed as
a theorem here — at `m = 0` the map `U⁰ → 𝓀ˣ` is the *multiplicative* reduction
`unitsQuotEquivResidueUnits`, and no additive coefficient is defined. D1 N/A; D2 N/A.
Recovers nothing from an abstract group; R1–R3 untouched. Standard axioms only; ledger
`0 FOUNDATIONAL / 0 DEBT` unchanged.
-/

noncomputable section

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K]

/-! ### The ring-level filtration `𝒪[K]ˣ ⊇ 1 + 𝓂^m` -/

/-- The inclusion of the integral units into `Kˣ`. -/
def integerUnitsHom : (↥𝒪[K])ˣ →* Kˣ := Units.map (Subring.subtype 𝒪[K]).toMonoidHom

theorem integerUnitsHom_injective : Function.Injective (integerUnitsHom K) :=
  Units.map_injective (Subring.subtype_injective _)

theorem coe_integerUnitsHom (w : (↥𝒪[K])ˣ) : ((integerUnitsHom K w : Kˣ) : K) = (w : ↥𝒪[K]) :=
  rfl

/-- The ring-level higher unit group: units of `𝒪[K]` congruent to `1` modulo `𝓂[K]^m`, as the
kernel of `𝒪[K]ˣ →* (𝒪[K] ⧸ 𝓂[K]^m)ˣ`. At `m = 0` this is all of `𝒪[K]ˣ`. -/
def integerUnitFiltration (m : ℕ) : Subgroup (↥𝒪[K])ˣ :=
  (Units.map (Ideal.Quotient.mk (𝓂[K] ^ m)).toMonoidHom).ker

theorem mem_integerUnitFiltration_iff {m : ℕ} {w : (↥𝒪[K])ˣ} :
    w ∈ integerUnitFiltration K m ↔ (w : ↥𝒪[K]) - 1 ∈ 𝓂[K] ^ m := by
  rw [integerUnitFiltration, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  change Ideal.Quotient.mk (𝓂[K] ^ m) (w : ↥𝒪[K]) = 1 ↔ _
  rw [← map_one (Ideal.Quotient.mk (𝓂[K] ^ m)), Ideal.Quotient.mk_eq_mk_iff_sub_mem]

theorem integerUnitFiltration_zero : integerUnitFiltration K 0 = ⊤ := by
  rw [eq_top_iff]
  intro w _
  rw [mem_integerUnitFiltration_iff, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

theorem integerUnitFiltration_antitone : Antitone (integerUnitFiltration K) := by
  intro m n hmn w hw
  rw [mem_integerUnitFiltration_iff] at hw ⊢
  exact Ideal.pow_le_pow_right hmn hw

/-! ### The filtration `Uᵐ ≤ Kˣ` -/

/-- **The higher unit group `Uᵐ ≤ Kˣ`**: `U⁰ = 𝒪[K]ˣ`, and `Uᵐ = 1 + 𝓂[K]^m` for `m ≥ 1`
(Serre, *Local Fields*, IV §2 / XV §2), as the image of `integerUnitFiltration K m` in `Kˣ`. -/
def unitFiltration (m : ℕ) : Subgroup Kˣ := (integerUnitFiltration K m).map (integerUnitsHom K)

theorem mem_unitFiltration_iff {m : ℕ} {u : Kˣ} :
    u ∈ unitFiltration K m ↔
      ∃ w : (↥𝒪[K])ˣ, (w : ↥𝒪[K]) - 1 ∈ 𝓂[K] ^ m ∧ ((w : ↥𝒪[K]) : K) = u := by
  rw [unitFiltration, Subgroup.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, (mem_integerUnitFiltration_iff K).mp hw, rfl⟩
  · rintro ⟨w, hw, hwu⟩
    exact ⟨w, (mem_integerUnitFiltration_iff K).mpr hw, Units.ext hwu⟩

theorem unitFiltration_antitone : Antitone (unitFiltration K) := fun _ _ hmn =>
  Subgroup.map_mono (integerUnitFiltration_antitone K hmn)

theorem unitFiltration_zero : unitFiltration K 0 = (integerUnitsHom K).range := by
  rw [unitFiltration, integerUnitFiltration_zero, ← MonoidHom.range_eq_map]

/-- `u ∈ U⁰ ↔ v(u) = 1`: `U⁰` is Mathlib's unit group of the canonical valuation subring. -/
theorem mem_unitFiltration_zero_iff {u : Kˣ} :
    u ∈ unitFiltration K 0 ↔ valuation K (u : K) = 1 := by
  rw [unitFiltration_zero, MonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    rw [coe_integerUnitsHom]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).mp w.isUnit
  · intro hu
    have hmem : (u : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hu.le
    have hunit : IsUnit (⟨(u : K), hmem⟩ : ↥𝒪[K]) :=
      (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation K))).mpr hu
    exact ⟨hunit.unit, Units.ext (by simp [coe_integerUnitsHom])⟩

theorem unitFiltration_zero_eq_unitGroup :
    unitFiltration K 0 = (valuation K).valuationSubring.unitGroup := by
  ext u
  rw [mem_unitFiltration_zero_iff, Valuation.mem_unitGroup_iff]

/-- The transport `integerUnitFiltration K m ≃* unitFiltration K m` along the injective
inclusion `𝒪[K]ˣ →* Kˣ`. -/
noncomputable def integerUnitsEquiv (m : ℕ) : integerUnitFiltration K m ≃* unitFiltration K m :=
  Subgroup.equivMapOfInjective _ _ (integerUnitsHom_injective K)

theorem coe_integerUnitsEquiv_apply {m : ℕ} (w : integerUnitFiltration K m) :
    ((integerUnitsEquiv K m w : unitFiltration K m) : Kˣ) = integerUnitsHom K w :=
  rfl

/-- Kernels transport along `integerUnitsEquiv`: a hom out of the ring-level `Uᵐ` whose kernel
is the ring-level `Uⁿ` induces a hom out of `Uᵐ ≤ Kˣ` with kernel `Uⁿ ≤ Kˣ`. -/
theorem ker_comp_integerUnitsEquiv_symm {M : Type*} [Monoid M] {m n : ℕ}
    (f : integerUnitFiltration K m →* M)
    (hf : f.ker = (integerUnitFiltration K n).subgroupOf (integerUnitFiltration K m)) :
    (f.comp (integerUnitsEquiv K m).symm.toMonoidHom).ker =
      (unitFiltration K n).subgroupOf (unitFiltration K m) := by
  ext u
  obtain ⟨w, rfl⟩ := (integerUnitsEquiv K m).surjective u
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, ← MonoidHom.mem_ker, hf, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, coe_integerUnitsEquiv_apply]
  exact (Subgroup.mem_map_iff_mem (integerUnitsHom_injective K)).symm

/-! ### `U⁰ ⧸ U¹ ≃* 𝓀ˣ` -/

/-- Reduction of units `𝒪[K]ˣ →* 𝓀[K]ˣ`. -/
def residueUnits : (↥𝒪[K])ˣ →* (𝓀[K])ˣ := Units.map (residue ↥𝒪[K]).toMonoidHom

theorem residueUnits_surjective : Function.Surjective (residueUnits K) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (inferInstanceAs (IsLocalHom (residue ↥𝒪[K])))

theorem integerUnitFiltration_one : integerUnitFiltration K 1 = (residueUnits K).ker := by
  ext w
  rw [mem_integerUnitFiltration_iff, pow_one, residueUnits, MonoidHom.mem_ker, Units.ext_iff,
    Units.coe_map, Units.val_one]
  change _ ↔ Ideal.Quotient.mk 𝓂[K] (w : ↥𝒪[K]) = 1
  rw [← map_one (Ideal.Quotient.mk 𝓂[K]), Ideal.Quotient.mk_eq_mk_iff_sub_mem]

/-- `𝒪[K]ˣ ⧸ (1 + 𝓂) ≃* 𝓀[K]ˣ` (ring-level form). -/
noncomputable def integerUnitsQuotEquivResidueUnits :
    (↥𝒪[K])ˣ ⧸ integerUnitFiltration K 1 ≃* (𝓀[K])ˣ :=
  QuotientGroup.liftEquiv _ (residueUnits_surjective K) (integerUnitFiltration_one K)

/-- Reduction of units on `U⁰ ≤ Kˣ`. -/
noncomputable def unitResidue : unitFiltration K 0 →* (𝓀[K])ˣ :=
  ((residueUnits K).comp (integerUnitFiltration K 0).subtype).comp
    (integerUnitsEquiv K 0).symm.toMonoidHom

theorem unitResidue_surjective : Function.Surjective (unitResidue K) := by
  intro r
  obtain ⟨w, hw⟩ := residueUnits_surjective K r
  refine ⟨integerUnitsEquiv K 0 ⟨w, by rw [integerUnitFiltration_zero]; exact Subgroup.mem_top w⟩,
    ?_⟩
  simp [unitResidue, hw]

theorem ker_unitResidue :
    (unitResidue K).ker = (unitFiltration K 1).subgroupOf (unitFiltration K 0) := by
  refine ker_comp_integerUnitsEquiv_symm K _ ?_
  ext w
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← MonoidHom.mem_ker,
    ← integerUnitFiltration_one, Subgroup.mem_subgroupOf]

/-- **`U⁰ ⧸ U¹ ≃* 𝓀[K]ˣ`**: the units modulo the principal units are the residue-field units. -/
noncomputable def unitsQuotEquivResidueUnits :
    unitFiltration K 0 ⧸ (unitFiltration K 1).subgroupOf (unitFiltration K 0) ≃* (𝓀[K])ˣ :=
  QuotientGroup.liftEquiv _ (unitResidue_surjective K) (ker_unitResidue K).symm

/-! ### The depth-`m` coefficient and `Uᵐ ⧸ Uᵐ⁺¹ ↪ 𝓀⁺` (`m ≥ 1`) -/

variable {K} [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (π : ↥𝒪[K]) (hπ : 𝓂[K] = Ideal.span {π})
include hπ

theorem uniformizer_ne_zero : π ≠ 0 := fun h =>
  IsDiscreteValuationRing.not_a_field ↥𝒪[K] (hπ.trans (Ideal.span_singleton_eq_bot.mpr h))

theorem exists_sub_one_eq_pow_mul {m : ℕ} {w : (↥𝒪[K])ˣ} (hw : w ∈ integerUnitFiltration K m) :
    ∃ a : ↥𝒪[K], (w : ↥𝒪[K]) - 1 = π ^ m * a := by
  rw [mem_integerUnitFiltration_iff, hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
  obtain ⟨a, ha⟩ := hw
  exact ⟨a, ha⟩

/-- **The depth-`m` coefficient** of `w ∈ Uᵐ`: the unique `a` with `w − 1 = π^m · a`. -/
noncomputable def unitCoeff {m : ℕ} (w : integerUnitFiltration K m) : ↥𝒪[K] :=
  (exists_sub_one_eq_pow_mul π hπ w.2).choose

theorem unitCoeff_spec {m : ℕ} (w : integerUnitFiltration K m) :
    ((w : (↥𝒪[K])ˣ) : ↥𝒪[K]) - 1 = π ^ m * unitCoeff π hπ w :=
  (exists_sub_one_eq_pow_mul π hπ w.2).choose_spec

theorem unitCoeff_unique {m : ℕ} {w : integerUnitFiltration K m} {a : ↥𝒪[K]}
    (ha : ((w : (↥𝒪[K])ˣ) : ↥𝒪[K]) - 1 = π ^ m * a) : unitCoeff π hπ w = a :=
  mul_left_cancel₀ (pow_ne_zero _ (uniformizer_ne_zero π hπ))
    ((unitCoeff_spec π hπ w).symm.trans ha)

theorem unitCoeff_one {m : ℕ} : unitCoeff π hπ (1 : integerUnitFiltration K m) = 0 :=
  unitCoeff_unique π hπ (by simp)

theorem unitCoeff_mul {m : ℕ} (w₁ w₂ : integerUnitFiltration K m) :
    unitCoeff π hπ (w₁ * w₂) =
      unitCoeff π hπ w₁ + unitCoeff π hπ w₂ + π ^ m * (unitCoeff π hπ w₁ * unitCoeff π hπ w₂) := by
  refine unitCoeff_unique π hπ ?_
  have h₁ := unitCoeff_spec π hπ w₁
  have h₂ := unitCoeff_spec π hπ w₂
  rw [Subgroup.coe_mul, Units.val_mul]
  linear_combination ((w₂ : (↥𝒪[K])ˣ) : ↥𝒪[K]) * h₁ + (1 + π ^ m * unitCoeff π hπ w₁) * h₂

theorem residue_pow_mul_eq_zero {m : ℕ} (hm : 1 ≤ m) (a : ↥𝒪[K]) :
    residue ↥𝒪[K] (π ^ m * a) = 0 := by
  rw [residue_eq_zero_iff]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have hπm : π ∈ 𝓂[K] := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  have h : π ^ (j + 1) * a = π * (π ^ j * a) := by ring
  rw [h]
  exact Ideal.mul_mem_right _ _ hπm

/-- The depth-`m` **layer homomorphism** on the ring-level `Uᵐ` (`m ≥ 1`): `w ↦ a_w mod 𝓂`
where `w = 1 + π^m a_w`. Multiplicativity: `a_{w₁w₂} = a₁ + a₂ + π^m a₁a₂ ≡ a₁ + a₂`. -/
noncomputable def integerUnitLayerHom {m : ℕ} (hm : 1 ≤ m) :
    integerUnitFiltration K m →* Multiplicative 𝓀[K] where
  toFun w := Multiplicative.ofAdd (residue ↥𝒪[K] (unitCoeff π hπ w))
  map_one' := by rw [unitCoeff_one, map_zero, ofAdd_zero]
  map_mul' w₁ w₂ := by
    simp only [unitCoeff_mul, map_add, residue_pow_mul_eq_zero π hπ hm, add_zero, ofAdd_add]

theorem integerUnitLayerHom_apply {m : ℕ} (hm : 1 ≤ m) (w : integerUnitFiltration K m) :
    integerUnitLayerHom π hπ hm w = Multiplicative.ofAdd (residue ↥𝒪[K] (unitCoeff π hπ w)) :=
  rfl

theorem ker_integerUnitLayerHom {m : ℕ} (hm : 1 ≤ m) :
    (integerUnitLayerHom π hπ hm).ker =
      (integerUnitFiltration K (m + 1)).subgroupOf (integerUnitFiltration K m) := by
  ext w
  rw [MonoidHom.mem_ker, integerUnitLayerHom_apply, ofAdd_eq_one, residue_eq_zero_iff,
    Subgroup.mem_subgroupOf, mem_integerUnitFiltration_iff, hπ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, Ideal.mem_span_singleton, unitCoeff_spec π hπ w]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by rw [hb]; ring⟩
  · rintro ⟨c, hc⟩
    refine ⟨c, mul_left_cancel₀ (pow_ne_zero m (uniformizer_ne_zero π hπ)) ?_⟩
    rw [hc, pow_succ, mul_assoc]

theorem integerUnitLayerHom_surjective {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (integerUnitLayerHom π hπ hm) := by
  intro r
  obtain ⟨a, rfl⟩ := residue_surjective r.toAdd
  have hunit : IsUnit (1 + π ^ m * a) := by
    apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
    rw [← mem_maximalIdeal, sub_add_cancel_left, Ideal.neg_mem_iff, ← residue_eq_zero_iff]
    exact residue_pow_mul_eq_zero π hπ hm a
  have hmem : hunit.unit ∈ integerUnitFiltration K m := by
    rw [mem_integerUnitFiltration_iff, IsUnit.unit_spec, hπ, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨a, by ring⟩
  refine ⟨⟨hunit.unit, hmem⟩, ?_⟩
  rw [integerUnitLayerHom_apply,
    unitCoeff_unique π hπ (w := ⟨hunit.unit, hmem⟩) (a := a) (by rw [IsUnit.unit_spec]; ring)]
  rfl

/-- **The layer homomorphism `Uᵐ →* 𝓀⁺`** (`m ≥ 1`) on `Uᵐ ≤ Kˣ`, written multiplicatively. -/
noncomputable def unitLayerHom {m : ℕ} (hm : 1 ≤ m) : unitFiltration K m →* Multiplicative 𝓀[K] :=
  (integerUnitLayerHom π hπ hm).comp (integerUnitsEquiv K m).symm.toMonoidHom

/-- **`ker (Uᵐ → 𝓀⁺) = Uᵐ⁺¹`.** -/
theorem ker_unitLayerHom {m : ℕ} (hm : 1 ≤ m) :
    (unitLayerHom π hπ hm).ker = (unitFiltration K (m + 1)).subgroupOf (unitFiltration K m) :=
  ker_comp_integerUnitsEquiv_symm K _ (ker_integerUnitLayerHom π hπ hm)

theorem unitLayerHom_surjective {m : ℕ} (hm : 1 ≤ m) : Function.Surjective (unitLayerHom π hπ hm) :=
  (integerUnitLayerHom_surjective π hπ hm).comp (integerUnitsEquiv K m).symm.surjective

/-- **The layer isomorphism `Uᵐ ⧸ Uᵐ⁺¹ ≃* 𝓀⁺`** (`m ≥ 1`), multiplicative form. -/
noncomputable def unitLayerQuotEquiv {m : ℕ} (hm : 1 ≤ m) :
    unitFiltration K m ⧸ (unitFiltration K (m + 1)).subgroupOf (unitFiltration K m) ≃*
      Multiplicative 𝓀[K] :=
  QuotientGroup.liftEquiv _ (unitLayerHom_surjective π hπ hm) (ker_unitLayerHom π hπ hm).symm

/-- The induced **injective** homomorphism `Uᵐ ⧸ Uᵐ⁺¹ →* 𝓀⁺` (`m ≥ 1`). -/
noncomputable def unitLayerQuotHom {m : ℕ} (hm : 1 ≤ m) :
    unitFiltration K m ⧸ (unitFiltration K (m + 1)).subgroupOf (unitFiltration K m) →*
      Multiplicative 𝓀[K] :=
  (unitLayerQuotEquiv π hπ hm).toMonoidHom

theorem unitLayerQuotHom_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (unitLayerQuotHom π hπ hm) :=
  (unitLayerQuotEquiv π hπ hm).injective

/-- The additive form: **`Uᵐ ⧸ Uᵐ⁺¹ ↪ 𝓀[K]`** as an additive-group embedding (`m ≥ 1`). -/
noncomputable def unitLayerQuotAddHom {m : ℕ} (hm : 1 ≤ m) :
    Additive (unitFiltration K m ⧸ (unitFiltration K (m + 1)).subgroupOf (unitFiltration K m)) →+
      𝓀[K] where
  toFun x := (unitLayerQuotHom π hπ hm x.toMul).toAdd
  map_zero' := by simp
  map_add' x y := by simp

theorem unitLayerQuotAddHom_injective {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (unitLayerQuotAddHom π hπ hm) := by
  intro x y hxy
  exact Additive.toMul.injective
    (unitLayerQuotHom_injective π hπ hm (Multiplicative.toAdd.injective hxy))

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms mem_unitFiltration_iff
#print axioms unitFiltration_antitone
#print axioms unitFiltration_zero_eq_unitGroup
#print axioms unitsQuotEquivResidueUnits
#print axioms ker_unitLayerHom
#print axioms unitLayerQuotEquiv
#print axioms unitLayerQuotHom_injective
#print axioms unitLayerQuotAddHom_injective

end Anabelian
