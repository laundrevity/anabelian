/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.StableAction

/-!
# L3.1: the abstract DVR unit filtration (Pass 97)

For a DVR `R`, `unitFiltration R m` is the kernel of reduction of units modulo
`𝔪^m`. It is all units at depth zero, antitone, separated, and preserved by every
ring automorphism. `unitFiltration_stable` has the map-equality form consumed by
Pass 96's `restrictAut` and `quotientAut`.

A finite residue field makes `Rˣ / U^m` finite, and hence makes `Rˣ / S` finite
whenever `U^m ≤ S`. At depth one, `unitsResidueEquiv` identifies the quotient with
residue-field units; `unitsResidueEquiv_mk` specifies its effect on representatives.

For an irreducible `π` and positive depth `m`, `unitCoeff` sends `1 + π^m*a` to
the additive residue of `a`, packaged multiplicatively. The exact coefficient in
`R` is `unitCoeffLift`, whose uniqueness follows by cancellation of `π^m`.
`unitCoeff_exact` gives surjectivity and kernel `U^(m+1)`. Under `s π = π*c`,
`unitCoeff_action` retains the residue action and the factor `residue(c)^m`.
No exactness of the cyclic pair on these natural graded pieces is asserted.

## Scope and axioms

The context is an abstract DVR: no local field or completeness assumption.
Finite residue is carried only in the two finiteness results. All hypotheses
are carried without necessity or sharpness claims; no new `structure`/`class`,
no owed witness, D1/D2 N/A. No Hilbert 90, reciprocity, or R1–R3 work.
Every declaration is audited below: standard axioms only; ledger stays 0/0.
-/

open IsLocalRing

namespace Anabelian

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The depth-`m` unit subgroup, defined as the kernel of reduction modulo `𝔪^m`. -/
def unitFiltration (m : ℕ) : Subgroup Rˣ :=
  (Units.map (Ideal.Quotient.mk (maximalIdeal R ^ m)).toMonoidHom).ker

/-- A unit has depth at least `m` precisely when its difference from one lies in `𝔪^m`. -/
theorem mem_unitFiltration (m : ℕ) (u : Rˣ) :
    u ∈ unitFiltration R m ↔ (u : R) - 1 ∈ maximalIdeal R ^ m := by
  change Units.map _ u = 1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk _ (u : R) = Ideal.Quotient.mk _ 1 ↔ _
  exact Ideal.Quotient.eq

/-- Depth zero is the full unit group (including reduction to the zero quotient ring). -/
theorem unitFiltration_zero : unitFiltration R 0 = ⊤ := by
  ext u
  simp [mem_unitFiltration]

/-- Increasing the depth decreases the unit subgroup. -/
theorem unitFiltration_antitone : Antitone (unitFiltration R) := by
  intro m n hmn u hu
  rw [mem_unitFiltration] at hu ⊢
  exact Ideal.pow_le_pow_right hmn hu

/-- Krull intersection separates the unit filtration: only one lies at every depth. -/
theorem unitFiltration_separated : (⨅ m, unitFiltration R m) = ⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  have h : (u : R) - 1 ∈ ⨅ m : ℕ, maximalIdeal R ^ m := by
    exact Ideal.mem_iInf.mpr fun m =>
      (mem_unitFiltration R m u).mp ((Subgroup.mem_iInf.mp hu) m)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top,
    Submodule.mem_bot, sub_eq_zero] at h
  exact Subgroup.mem_bot.mpr (Units.ext h)

/-- Every ring automorphism preserves each depth, in the map-equality form of Pass 96. -/
theorem unitFiltration_stable (s : R ≃+* R) (m : ℕ) :
    (unitFiltration R m).map (Units.mapEquiv s.toMulEquiv).toMonoidHom =
      unitFiltration R m := by
  have hmap (t : R ≃+* R) : (maximalIdeal R ^ m).map t = maximalIdeal R ^ m := by
    rw [Ideal.map_pow, map_ringEquiv_maximalIdeal]
  have hmem (t : R ≃+* R) (u : Rˣ) (hu : u ∈ unitFiltration R m) :
      Units.mapEquiv t.toMulEquiv u ∈ unitFiltration R m := by
    rw [mem_unitFiltration] at hu ⊢
    change t (u : R) - 1 ∈ _
    rw [← map_one t, ← map_sub, ← hmap t]
    exact Ideal.mem_map_of_mem t hu
  apply le_antisymm
  · rintro u ⟨v, hv, rfl⟩
    exact hmem s v hv
  · intro u hu
    refine Subgroup.mem_map.mpr ⟨Units.mapEquiv s.symm.toMulEquiv u, hmem s.symm u hu, ?_⟩
    exact Units.ext (s.apply_symm_apply (u : R))

/-- Finite residue field gives finite unit quotients at every depth. -/
theorem finite_unitQuotient [Finite (ResidueField R)] (m : ℕ) :
    Finite (Rˣ ⧸ unitFiltration R m) := by
  haveI hres : Finite (R ⧸ maximalIdeal R) := inferInstanceAs (Finite (ResidueField R))
  haveI hquot : Finite (R ⧸ maximalIdeal R ^ m) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) m
  exact Finite.of_injective (QuotientGroup.quotientKerEquivRange
    (Units.map (Ideal.Quotient.mk (maximalIdeal R ^ m)).toMonoidHom))
    (Equiv.injective _)

/-- A subgroup containing some filtration term has finite index when the residue is finite. -/
theorem finite_units_quotient_of_le [Finite (ResidueField R)]
    (S : Subgroup Rˣ) (m : ℕ) (hS : unitFiltration R m ≤ S) :
    Finite (Rˣ ⧸ S) := by
  haveI hquot : Finite (Rˣ ⧸ unitFiltration R m) := finite_unitQuotient R m
  exact Finite.of_surjective (QuotientGroup.map _ S (MonoidHom.id _) hS)
    (QuotientGroup.map_surjective_of_surjective _ _ _ (QuotientGroup.mk_surjective) hS)

/-- Reduction identifies `Rˣ / U¹` with the multiplicative group of the residue field. -/
noncomputable def unitsResidueEquiv :
    (Rˣ ⧸ unitFiltration R 1) ≃* (ResidueField R)ˣ := by
  have hsurj : Function.Surjective (Units.map (residue R).toMonoidHom) :=
    surjective_units_map_of_local_ringHom (residue R) residue_surjective inferInstance
  have hk : unitFiltration R 1 = (Units.map (residue R).toMonoidHom).ker := by
    ext u
    rw [mem_unitFiltration, MonoidHom.mem_ker, Units.ext_iff]
    change (u : R) - 1 ∈ maximalIdeal R ^ 1 ↔ residue R (u : R) = 1
    rw [Submodule.pow_one, ← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
  exact (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

/-- The residue equivalence is induced by reduction of unit representatives. -/
theorem unitsResidueEquiv_mk (u : Rˣ) :
    unitsResidueEquiv R (QuotientGroup.mk' (unitFiltration R 1) u) =
      Units.map (residue R).toMonoidHom u := by
  simp only [unitsResidueEquiv, MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- A depth-`m` unit can be written as `1 + π^m*a` for any uniformizer `π`. -/
theorem unitFiltration_exists_coeff (π : R) (hπ : Irreducible π)
    (m : ℕ) (u : unitFiltration R m) :
    ∃ a : R, (u.val : R) = 1 + π ^ m * a := by
  have hu := (mem_unitFiltration R m u.val).mp u.property
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨a, ha⟩ := hu
  exact ⟨a, by rw [← ha]; ring⟩

/-- The exact coefficient `(u - 1) / π^m` in the ring, chosen from its existence proof. -/
noncomputable def unitCoeffLift (π : R) (hπ : Irreducible π)
    (m : ℕ) (u : unitFiltration R m) : R :=
  (unitFiltration_exists_coeff R π hπ m u).choose

/-- The chosen coefficient reconstructs the original unit. -/
theorem unitCoeffLift_spec (π : R) (hπ : Irreducible π)
    (m : ℕ) (u : unitFiltration R m) :
    (u.val : R) = 1 + π ^ m * unitCoeffLift R π hπ m u :=
  (unitFiltration_exists_coeff R π hπ m u).choose_spec

/-- Cancellation of the nonzero `π^m` makes the exact coefficient unique. -/
theorem unitCoeffLift_eq (π : R) (hπ : Irreducible π) (m : ℕ)
    (u : unitFiltration R m) (a : R) (ha : (u.val : R) = 1 + π ^ m * a) :
    unitCoeffLift R π hπ m u = a := by
  exact mul_left_cancel₀ (pow_ne_zero m hπ.ne_zero)
    (add_left_cancel ((unitCoeffLift_spec R π hπ m u).symm.trans ha))

/-- The additive residue coefficient at positive depth, written multiplicatively.
The cross term in a product vanishes modulo the maximal ideal. -/
noncomputable def unitCoeff (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    unitFiltration R m →* Multiplicative (ResidueField R) where
  toFun u := Multiplicative.ofAdd (residue R (unitCoeffLift R π hπ m u))
  map_one' := by
    rw [unitCoeffLift_eq R π hπ m 1 0 (by simp)]
    rfl
  map_mul' u v := by
    let a := unitCoeffLift R π hπ m u
    let b := unitCoeffLift R π hπ m v
    have huv : ((u * v).val : R) = 1 + π ^ m * (a + b + π ^ m * (a * b)) := by
      change (u.val : R) * (v.val : R) = _
      rw [unitCoeffLift_spec R π hπ m u, unitCoeffLift_spec R π hπ m v]
      change (1 + π ^ m * a) * (1 + π ^ m * b) = _
      ring
    have hπres : residue R π = 0 := by
      rw [residue_eq_zero_iff, hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    rw [unitCoeffLift_eq R π hπ m (u * v) _ huv]
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd (residue R a + residue R b)
    simp [map_add, map_mul, map_pow, hπres, ne_of_gt hm]

/-- The coefficient hom sends `1 + π^m*a` to the residue of `a`. -/
theorem unitCoeff_spec (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m)
    (u : unitFiltration R m) (a : R)
    (ha : (u.val : R) = 1 + π ^ m * a) :
    unitCoeff R π hπ m hm u = Multiplicative.ofAdd (residue R a) := by
  change Multiplicative.ofAdd (residue R (unitCoeffLift R π hπ m u)) = _
  rw [unitCoeffLift_eq R π hπ m u a ha]

/-- The coefficient hom is surjective and has kernel the next filtration term. -/
theorem unitCoeff_exact (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (unitCoeff R π hπ m hm) ∧
    (unitCoeff R π hπ m hm).ker =
      (unitFiltration R (m + 1)).subgroupOf (unitFiltration R m) := by
  constructor
  · intro x
    obtain ⟨a, ha⟩ := residue_surjective (Multiplicative.toAdd x)
    have hπmem : π ∈ maximalIdeal R := by
      rw [hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    have hpowmem : π ^ m ∈ maximalIdeal R ^ m := Ideal.pow_mem_pow hπmem m
    have hzero : residue R (π ^ m * a) = 0 := by
      rw [residue_eq_zero_iff]
      exact (maximalIdeal R).mul_mem_right a (Ideal.pow_le_self (ne_of_gt hm) hpowmem)
    have hunit : IsUnit (1 + π ^ m * a) := by
      apply (residue_ne_zero_iff_isUnit _).mp
      rw [map_add, map_one, hzero, add_zero]
      exact one_ne_zero
    have hu : hunit.unit ∈ unitFiltration R m := by
      rw [mem_unitFiltration, hunit.unit_spec, add_sub_cancel_left]
      exact (maximalIdeal R ^ m).mul_mem_right a hpowmem
    refine ⟨⟨hunit.unit, hu⟩, ?_⟩
    rw [unitCoeff_spec R π hπ m hm _ a hunit.unit_spec, ha]
    rfl
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_unitFiltration]
    change Multiplicative.ofAdd (residue R (unitCoeffLift R π hπ m u)) = 1 ↔ _
    rw [ofAdd_eq_one, residue_eq_zero_iff, hπ.maximalIdeal_eq,
      Ideal.mem_span_singleton, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      unitCoeffLift_spec R π hπ m u, add_sub_cancel_left, pow_succ]
    exact (mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)).symm

/-- Under `s π = π*c`, coefficients transform by the residue action and `residue(c)^m`.
The representative formula makes the uniformizer twist explicit. -/
theorem unitCoeff_action (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m)
    (s : R ≃+* R) (c : Rˣ) (hc : s π = π * c)
    (u : unitFiltration R m) (a : R)
    (ha : (u.val : R) = 1 + π ^ m * a) :
    unitCoeff R π hπ m hm
        (restrictAut (Units.mapEquiv s.toMulEquiv) (unitFiltration R m)
          (unitFiltration_stable R s m) u) =
      Multiplicative.ofAdd (residue R (s a) * residue R (c : R) ^ m) := by
  have heq :
      ((restrictAut (Units.mapEquiv s.toMulEquiv) (unitFiltration R m)
        (unitFiltration_stable R s m) u).val : R) =
      1 + π ^ m * (s a * (c : R) ^ m) := by
    change s (u.val : R) = _
    rw [ha, map_add, map_one, map_mul, map_pow, hc, mul_pow]
    ring
  rw [unitCoeff_spec R π hπ m hm _ _ heq, map_mul, map_pow]

-- Reproducible audit of all eighteen declarations; standard axioms only.
#print axioms unitFiltration
#print axioms mem_unitFiltration
#print axioms unitFiltration_zero
#print axioms unitFiltration_antitone
#print axioms unitFiltration_separated
#print axioms unitFiltration_stable
#print axioms finite_unitQuotient
#print axioms finite_units_quotient_of_le
#print axioms unitsResidueEquiv
#print axioms unitsResidueEquiv_mk
#print axioms unitFiltration_exists_coeff
#print axioms unitCoeffLift
#print axioms unitCoeffLift_spec
#print axioms unitCoeffLift_eq
#print axioms unitCoeff
#print axioms unitCoeff_spec
#print axioms unitCoeff_exact
#print axioms unitCoeff_action

end Anabelian
