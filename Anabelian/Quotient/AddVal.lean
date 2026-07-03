/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.Basic
import Anabelian.Ramification.LowerIndexGenerator
import Anabelian.Extension.Uniformizer
import Anabelian.Extension.Monogenic
import Mathlib

/-!
# Toward Serre IV §1 Prop. 3: the `addVal` bookkeeping (Pass 59)

The two divisibilities of Prop. 3 compare `ι(σ̄y − y)` with the lift-set product; the **sum
formula** `e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)` then follows by reading both sides
through `addVal`. This pass supplies that reading:

* **the `e'`-dilation** (`addVal_comapRingHom`): for the tower inclusion `ι : B → A` of DVR
  valuation subrings, `addVal_A (ι c) = addVal_B c · e'` with `e' = addVal_A (ι π_B)` — the
  ramification index in `addVal` form. Behind it, **the unit-transfer**
  (`isUnit_comapRingHom_iff`): `ι c` is a unit iff `c` is — the forward direction because a
  field inverse of a `K'`-element that is integral is again a `K'`-element of `A`, i.e. lies
  in `B` (the multiplicative counterpart of Pass 50's `𝔪`-reflection).
* **the fiber sum** (`addVal_liftProd`): at `𝒪_L` with a generator `x`,
  `addVal (∏_{h} (x − (s₀·dr h)·x)) = Σ_h i_{L/K}(s₀·dr h)` — `addVal` of a product is the
  sum (`addVal_prod`, generic), each factor is a lower index by Passes 53–54 (up to the sign
  `x − s·x = −(s·x − x)`, killed by `addVal_neg`). The right side of Prop. 3's sum formula,
  in `H`-parametrized form matching Pass 58's product.

With Pass 57's `i_{K'/K}(σ̄) = addVal_B (σ̄y − y)` and Pass 58's `a ∣ b`, the only missing
ingredient of the sum formula is now direction (ii) (`b ∣ a`).

## What is proved (all axiom-free)

* `addVal_neg`, `addVal_prod` — generic DVR bookkeeping (neg-invariance; product ↦ sum).
* `isUnit_comapRingHom_iff` — units transfer both ways along `ι : B → A`.
* **`addVal_comapRingHom`** — the `e'`-dilation.
* **`addVal_liftProd`** — the fiber sum at `𝒪_L`.

## Honesty

Valuation bookkeeping for a tower of given fields — **no reach toward R1–R3**; nothing
recovered from an abstract group. No divisibility and no part of the sum formula's assembly
is claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2 stays inside the Pass-29
proofs.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing IsDiscreteValuationRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- `addVal` is invariant under negation (`a` and `−a` divide each other). -/
theorem addVal_neg (a : R) : addVal R (-a) = addVal R a :=
  le_antisymm (addVal_le_iff_dvd.mpr (neg_dvd.mpr dvd_rfl))
    (addVal_le_iff_dvd.mpr (dvd_neg.mpr dvd_rfl))

/-- `addVal` of a finite product is the sum of the `addVal`s. -/
theorem addVal_prod {α : Type*} (s : Finset α) (f : α → R) :
    addVal R (∏ i ∈ s, f i) = ∑ i ∈ s, addVal R (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, addVal_mul, ih]

end Generic

section Dilation

variable (K' : Type*) [Field K']
variable {L : Type*} [Field L] [Algebra K' L]
variable (A : ValuationSubring L)

/-- **Units transfer both ways** along the tower inclusion `ι : A ∩ K' → A`: the inverse of
`ι c` in `A` is the image of `(c : K')⁻¹`, which is integral because it lies in `A` — so it
lives in `A ∩ K'`. (The multiplicative counterpart of Pass 50's
`mem_maximalIdeal_of_comapRingHom`.) -/
theorem isUnit_comapRingHom_iff (c : ↥(A.comap (algebraMap K' L))) :
    IsUnit (comapRingHom K' A c) ↔ IsUnit c := by
  constructor
  · intro hu
    have hc0 : (c : K') ≠ 0 := by
      rintro h0
      have hz : comapRingHom K' A c = 0 := by
        apply Subtype.ext
        change algebraMap K' L (c : K') = 0
        rw [h0, map_zero]
      rw [hz] at hu
      exact not_isUnit_zero hu
    obtain ⟨w, hw⟩ := hu
    have hmem : ((c : K')⁻¹) ∈ A.comap (algebraMap K' L) := by
      rw [mem_comap]
      have h1 : ((w : ↥A) : L) * (((w⁻¹ : _ˣ) : ↥A) : L) = 1 := by
        exact_mod_cast congrArg Subtype.val (w.mul_inv)
      rw [hw] at h1
      have h2 : (((w⁻¹ : _ˣ) : ↥A) : L) = algebraMap K' L ((c : K')⁻¹) := by
        rw [map_inv₀]
        exact eq_inv_of_mul_eq_one_right (by rw [mul_comm] at h1 ⊢; exact h1)
      rw [← h2]
      exact ((w⁻¹ : _ˣ) : ↥A).2
    rw [isUnit_iff_exists_inv]
    refine ⟨⟨(c : K')⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    exact mul_inv_cancel₀ hc0
  · exact fun hu => hu.map (comapRingHom K' A)

variable [IsDiscreteValuationRing ↥A]
  [IsDiscreteValuationRing ↥(A.comap (algebraMap K' L))]

/-- **The `e'`-dilation**: through the tower inclusion `ι : B = A ∩ K' → A` of DVRs,
`addVal_A (ι c) = addVal_B c · e'` where `e' = addVal_A (ι π)` for a uniformizer `π` of `B` —
the ramification index of the extension, in `addVal` form. (Write `c = u·π^n`; units go to
units, so the valuation upstairs is `n·e'`.) -/
theorem addVal_comapRingHom {π : ↥(A.comap (algebraMap K' L))} (hπ : Irreducible π)
    (c : ↥(A.comap (algebraMap K' L))) :
    addVal ↥A (comapRingHom K' A c)
      = addVal ↥(A.comap (algebraMap K' L)) c * addVal ↥A (comapRingHom K' A π) := by
  have hπunit : ¬ IsUnit (comapRingHom K' A π) := by
    rw [isUnit_comapRingHom_iff]
    exact hπ.not_isUnit
  have he0 : addVal ↥A (comapRingHom K' A π) ≠ 0 := by
    rw [Ne, addVal_eq_zero_iff]
    exact hπunit
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, addVal_zero, addVal_zero, ENat.top_mul he0]
  · obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hc hπ
    have hu0 : addVal ↥A (comapRingHom K' A ↑u) = 0 := by
      rw [addVal_eq_zero_iff]
      exact u.isUnit.map (comapRingHom K' A)
    rw [hu, map_mul, map_pow, addVal_mul, addVal_pow, hu0, zero_add,
        addVal_def' u hπ n, nsmul_eq_mul]

end Dilation

section FiberSum

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Fintype ((extensionIntegers K L).decompositionSubgroup K')]

/-- **The fiber sum**: for a generator `x` of `𝒪_L/𝒪_K`, the `addVal` of the lift-set
product is the sum of the lower indices over the coset —
`addVal (∏_h (x − (s₀·dr h)·x)) = Σ_h i_{L/K}(s₀·dr h)`. The right side of Prop. 3's sum
formula, in the `H`-parametrized form matching Pass 58's product. Per factor this is Passes
53–54's concrete `i_G` (with `addVal_neg` absorbing the sign `x − s·x = −(s·x − x)`). -/
theorem addVal_liftProd {x : ↥(extensionIntegers K L)}
    (hgen : Subring.closure
      (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}) = ⊤)
    (s₀ : (extensionIntegers K L).decompositionSubgroup K) :
    addVal ↥(extensionIntegers K L)
        (∏ h : (extensionIntegers K L).decompositionSubgroup K',
          (x - (s₀ * decompositionRestrict K K' (extensionIntegers K L) h) • x))
      = ∑ h : (extensionIntegers K L).decompositionSubgroup K',
          lowerIndex K (extensionIntegers K L)
            (s₀ * decompositionRestrict K K' (extensionIntegers K L) h) := by
  rw [addVal_prod]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [lowerIndex_eq_addVal K (extensionIntegers K L) hgen
      (fun a ha => smul_extensionAlgebraMap_range_eq K L _ a ha)]
  rw [show (x - (s₀ * decompositionRestrict K K' (extensionIntegers K L) h) • x)
      = -((s₀ * decompositionRestrict K K' (extensionIntegers K L) h) • x - x) by ring,
      addVal_neg]

end FiberSum

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms addVal_neg
#print axioms addVal_prod
#print axioms isUnit_comapRingHom_iff
#print axioms addVal_comapRingHom
#print axioms addVal_liftProd

end Anabelian
