/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.TrivialAction
import Mathlib

/-!
# L3.1: the valuation exact sequence of a DVR fraction field (Pass 93)

The `q(Lˣ)` track opens. For ANY discrete valuation ring `R` with fraction field `K`
(the target instantiation: `R = 𝒪_L`, `K = L` — but nothing here is specific to the
tower), the three pieces of the short exact sequence

> **`1 → Rˣ → Kˣ →v Multiplicative ℤ → 1`**

* **`dvrUnitsValuation : Kˣ →* Multiplicative ℤ`** — Mathlib's adic valuation at the
  maximal ideal (`dvrHeightOneSpectrum`), restricted to units through
  `WithZero.unitsWithZeroEquiv`, with the computation interface
  `dvrUnitsValuation_eq_iff`;
* **`dvrUnitsValuation_surjective`** — powers of a uniformizer hit everything;
* **`dvrUnitsValuation_ker`** — the kernel is exactly the image of `Rˣ`: the
  fraction-and-factor argument, using `intValuation_irreducible` (extracted and
  shortened via ideal multiplicity in Pass 94).

This is the `(ι, π, exactness)` data of the sequence. Pass 94's
`UnitsValuationEquivariance` makes it pair-equivariant and applies multiplicativity
to obtain the conditional identity `q(Kˣ) = q(Rˣ) · n`.

## Honesty

Valuation-theoretic plumbing for a given DVR — **no reach toward R1–R3**, no class field
theory claimed. No new `structure`/`class` (one `def` bundling Mathlib's spectrum point);
no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open IsDedekindDomain IsLocalRing

namespace Anabelian


variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The maximal ideal of a DVR as a height-one prime — the access point to Mathlib's
adic-valuation machinery. -/
noncomputable def dvrHeightOneSpectrum : HeightOneSpectrum R where
  asIdeal := maximalIdeal R
  isPrime := Ideal.IsMaximal.isPrime inferInstance
  ne_bot := IsDiscreteValuationRing.not_a_field'

/-- Every irreducible of a DVR has integral valuation `exp (−1)`. -/
theorem intValuation_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    (dvrHeightOneSpectrum R).intValuation ϖ = WithZero.exp (-1 : ℤ) := by
  rw [(dvrHeightOneSpectrum R).intValuation_eq_exp_neg_multiplicity hϖ.ne_zero]
  change WithZero.exp (-(multiplicity (maximalIdeal R) (Ideal.span {ϖ}) : ℤ)) = _
  rw [hϖ.maximalIdeal_eq, multiplicity_self]
  rfl

/-- **THE UNIT VALUATION** `v : Kˣ →* Multiplicative ℤ` of a DVR's fraction field —
Mathlib's `ℤᵐ⁰`-adic valuation restricted to units and read through
`WithZero.unitsWithZeroEquiv`. The `π` of the valuation SES
`1 → Rˣ → Kˣ → ℤ → 1`. -/
noncomputable def dvrUnitsValuation : Kˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map ((dvrHeightOneSpectrum R).valuation K).toMonoidHom)

/-- The computation interface: `v x = m` iff the `ℤᵐ⁰`-valuation of the carrier is
`↑m` — every downstream computation drops to the `WithZero` level through this. -/
theorem dvrUnitsValuation_eq_iff {x : Kˣ} {m : Multiplicative ℤ} :
    dvrUnitsValuation R K x = m
      ↔ (dvrHeightOneSpectrum R).valuation K x.1 = (m : WithZero (Multiplicative ℤ)) := by
  have h1 : ((dvrUnitsValuation R K x : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      = (dvrHeightOneSpectrum R).valuation K x.1 :=
    WithZero.coe_unitsWithZeroEquiv_eq_units_val _
  constructor
  · intro h
    rw [← h1, h]
  · intro h
    have h2 : ((dvrUnitsValuation R K x : Multiplicative ℤ)
        : WithZero (Multiplicative ℤ)) = (m : WithZero (Multiplicative ℤ)) := by
      rw [h1, h]
    exact_mod_cast h2

/-- **Surjectivity**: powers of a uniformizer hit every value. -/
theorem dvrUnitsValuation_surjective :
    Function.Surjective (dvrUnitsValuation R K) := by
  obtain ⟨π, hπ⟩ := (dvrHeightOneSpectrum R).valuation_exists_uniformizer K
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  intro m
  refine ⟨(Units.mk0 π hπ0) ^ (- Multiplicative.toAdd m), ?_⟩
  rw [dvrUnitsValuation_eq_iff]
  have h2 : ((Units.mk0 π hπ0 ^ (- Multiplicative.toAdd m) : Kˣ) : K)
      = π ^ (- Multiplicative.toAdd m) := by
    push_cast
    rfl
  rw [h2, map_zpow₀, hπ, ← WithZero.exp_zsmul]
  have h3 : (- Multiplicative.toAdd m) • (-1 : ℤ) = Multiplicative.toAdd m := by
    simp
  rw [h3]
  rfl

/-- **The kernel is exactly `Rˣ`** (as a subgroup of `Kˣ` via `Units.map`): a
valuation-one element `a/b` has `|a| = |b|`, DVR-factorization forces equal
`ϖ`-exponents, and the unit parts assemble. The irreducible valuation is supplied by
`intValuation_irreducible`. -/
theorem dvrUnitsValuation_ker :
    (dvrUnitsValuation R K).ker = (Units.map (algebraMap R K : R →* K)).range := by
  ext x
  rw [MonoidHom.mem_ker, dvrUnitsValuation_eq_iff]
  constructor
  · intro hx
    -- write x = a / b and factor both
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := R) (x : K)
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have ha0 : a ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_div] at hab
      exact x.ne_zero hab.symm
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    -- valuations: |a| = |ϖ|^m, |b| = |ϖ|^n, equal ⟹ m = n
    have hvu : (dvrHeightOneSpectrum R).intValuation (u : R) = 1 := by
      rw [(dvrHeightOneSpectrum R).intValuation_eq_one_iff_mem_primeCompl]
      intro hmem
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hmem)) u.isUnit
    have hvw : (dvrHeightOneSpectrum R).intValuation (w : R) = 1 := by
      rw [(dvrHeightOneSpectrum R).intValuation_eq_one_iff_mem_primeCompl]
      intro hmem
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hmem)) w.isUnit
    have hγ := intValuation_irreducible R hϖ
    -- m = n from equal valuations
    have hva : (dvrHeightOneSpectrum R).intValuation a = WithZero.exp (-(m : ℤ)) := by
      rw [hu, map_mul, map_pow, hvu, one_mul, hγ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hvb : (dvrHeightOneSpectrum R).intValuation b = WithZero.exp (-(n : ℤ)) := by
      rw [hw, map_mul, map_pow, hvw, one_mul, hγ, ← WithZero.exp_nsmul]
      congr 1
      simp
    have hxv : (dvrHeightOneSpectrum R).intValuation a
        = (dvrHeightOneSpectrum R).intValuation b := by
      rw [← hab, map_div₀, (dvrHeightOneSpectrum R).valuation_of_algebraMap,
          (dvrHeightOneSpectrum R).valuation_of_algebraMap, WithZero.coe_one] at hx
      have hb0' : (dvrHeightOneSpectrum R).intValuation b ≠ 0 :=
        (dvrHeightOneSpectrum R).intValuation_ne_zero b hb0
      exact (div_eq_one_iff_eq hb0').mp hx
    have hmn : m = n := by
      rw [hva, hvb] at hxv
      have h12 := WithZero.exp_injective hxv
      omega
    -- assemble the unit
    refine ⟨u * w⁻¹, ?_⟩
    apply Units.ext
    have hπK : algebraMap R K ϖ ≠ 0 := fun h0 =>
      hϖ.ne_zero (IsFractionRing.injective R K (by rw [h0, map_zero]))
    have hwK : algebraMap R K (w : R) ≠ 0 := fun h0 =>
      w.ne_zero (IsFractionRing.injective R K (by rw [h0, map_zero]))
    have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul]
      have h13 : ((w : R) * ((w⁻¹ : Rˣ) : R)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [h13, map_one]
    have hL : ((Units.map (algebraMap R K : R →* K) (u * w⁻¹) : Kˣ) : K)
        = algebraMap R K (u : R) * (algebraMap R K (w : R))⁻¹ := by
      rw [map_mul]
      have h14 : ((Units.map (algebraMap R K : R →* K) u : Kˣ) : K)
          = algebraMap R K (u : R) := rfl
      have h15 : ((Units.map (algebraMap R K : R →* K) w⁻¹ : Kˣ) : K)
          = algebraMap R K ((w⁻¹ : Rˣ) : R) := rfl
      rw [Units.val_mul, h14, h15, hwinv]
    rw [hL, ← hab, hu, hw, hmn]
    rw [map_mul, map_mul, map_pow]
    field_simp
  · rintro ⟨u, rfl⟩
    have h1 : ((Units.map (algebraMap R K : R →* K) u : Kˣ) : K)
        = algebraMap R K (u : R) := rfl
    rw [h1, (dvrHeightOneSpectrum R).valuation_of_algebraMap, WithZero.coe_one,
        (dvrHeightOneSpectrum R).intValuation_eq_one_iff_mem_primeCompl]
    intro hmem
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hmem)) u.isUnit


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms dvrHeightOneSpectrum
#print axioms intValuation_irreducible
#print axioms dvrUnitsValuation
#print axioms dvrUnitsValuation_eq_iff
#print axioms dvrUnitsValuation_surjective
#print axioms dvrUnitsValuation_ker

end Anabelian
