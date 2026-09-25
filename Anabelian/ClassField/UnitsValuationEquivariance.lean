/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.UnitsValuation

/-!
# L3.1: valuation equivariance and `q(Kˣ) = q(Rˣ) · n` (Pass 94)

For a DVR `R` with fraction field `K`, compatible ring automorphisms `s` and `t`
induce unit actions making `1 → Rˣ → Kˣ → Multiplicative ℤ → 1` equivariant, with
trivial action on the value group. Integral valuation invariance follows by DVR
factorization; the fraction-field statement follows by writing each element as `a/b`.

Generic cyclic naturality supplies the four norm/difference intertwinings. Pass 90's
multiplicativity and Pass 92's `q(ℤ) = n` then give `cyclicHerbrandQuotient_units`.

## Scope and hypotheses

The headline carries `n ≠ 0`, periodicity of the action on `Kˣ`, and explicit `Finite`
instances for `Ĥ¹` on `Rˣ` and `Kˣ`. Value-group `Ĥ¹` finiteness is proved from its
cardinality being one. These are carried hypotheses; no necessity or sharpness claim
is made. The result does not establish `q(Rˣ) = 1`, discharge the two supplied
finiteness instances, or identify a concrete Galois norm. No new `structure`/`class`,
no owed witness, no class field theory or reconstruction theorem claimed.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`.
-/

open IsLocalRing

namespace Anabelian

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- A ring automorphism of a DVR preserves its integral valuation. -/
theorem intValuation_ringEquiv (s : R ≃+* R) (r : R) :
    (dvrHeightOneSpectrum R).intValuation (s r)
      = (dvrHeightOneSpectrum R).intValuation r := by
  by_cases hr : r = 0
  · simp [hr]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  have hunit : ∀ a : R, IsUnit a → (dvrHeightOneSpectrum R).intValuation a = 1 := by
    intro a ha
    rw [(dvrHeightOneSpectrum R).intValuation_eq_one_iff_mem_primeCompl]
    intro hmem
    exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hmem)) ha
  have hsϖ : Irreducible (s ϖ) := (MulEquiv.irreducible_iff s).mpr hϖ
  rw [map_mul, map_pow, map_mul, map_mul, map_pow, map_pow,
    hunit _ (u.isUnit.map s), hunit _ u.isUnit,
    intValuation_irreducible R hsϖ, intValuation_irreducible R hϖ]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The units inclusion into the fraction field is injective. -/
theorem dvrUnitsInclusion_injective :
    Function.Injective (Units.map (algebraMap R K : R →* K)) :=
  Units.map_injective (IsFractionRing.injective R K)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- Compatible ring automorphisms induce compatible actions on units. -/
theorem dvrUnitsInclusion_equivariant (s : R ≃+* R) (t : K ≃+* K)
    (hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r)) (u : Rˣ) :
    Units.map (algebraMap R K : R →* K) (Units.mapEquiv s.toMulEquiv u)
      = Units.mapEquiv t.toMulEquiv (Units.map (algebraMap R K : R →* K) u) := by
  apply Units.ext
  exact (hst u).symm

/-- The fraction-field valuation is invariant under compatible ring automorphisms. -/
theorem dvrUnitsValuation_equivariant (s : R ≃+* R) (t : K ≃+* K)
    (hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r)) (x : Kˣ) :
    dvrUnitsValuation R K (Units.mapEquiv t.toMulEquiv x) = dvrUnitsValuation R K x := by
  rw [dvrUnitsValuation_eq_iff]
  have hx := (dvrUnitsValuation_eq_iff R K (x := x)).mp rfl
  rw [← hx]
  change (dvrHeightOneSpectrum R).valuation K (t (x : K))
    = (dvrHeightOneSpectrum R).valuation K (x : K)
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := R) (x : K)
  rw [← hab, map_div₀, hst, hst, map_div₀, map_div₀]
  simp only [(dvrHeightOneSpectrum R).valuation_of_algebraMap, intValuation_ringEquiv]

/-- A cyclic difference has trivial value. No periodicity is needed. -/
theorem dvrUnitsValuation_cyclicDiff (s : R ≃+* R) (t : K ≃+* K)
    (hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r)) (x : Kˣ) :
    dvrUnitsValuation R K (cyclicDiff (Units.mapEquiv t.toMulEquiv) x) = 1 := by
  have h := map_cyclicDiff (dvrUnitsValuation R K) (Units.mapEquiv t.toMulEquiv) 1
    (dvrUnitsValuation_equivariant R K s t hst) x
  simpa only [cyclicDiff_one_apply] using h

/-- The value of a cyclic norm is the `n`-th power of the value, without periodicity. -/
theorem dvrUnitsValuation_cyclicNorm (s : R ≃+* R) (t : K ≃+* K)
    (hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r)) (n : ℕ) (x : Kˣ) :
    dvrUnitsValuation R K (cyclicNorm (Units.mapEquiv t.toMulEquiv) n x)
      = (dvrUnitsValuation R K x) ^ n := by
  have h := map_cyclicNorm (dvrUnitsValuation R K) (Units.mapEquiv t.toMulEquiv) 1
    (dvrUnitsValuation_equivariant R K s t hst) n x
  simpa only [cyclicNorm_one_apply] using h

/-- **`q(Kˣ) = q(Rˣ) · n`**, conditional on the stated cyclic action and `Ĥ¹` finiteness
data. The unit-group quotient `q(Rˣ) = 1` remains a separate mathematical dependency. -/
theorem cyclicHerbrandQuotient_units (s : R ≃+* R) (t : K ≃+* K)
    (hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r))
    (n : ℕ) (hn : n ≠ 0) (hσ : Units.mapEquiv t.toMulEquiv ^ n = 1)
    [Finite (herbrandH (cyclicNorm (Units.mapEquiv s.toMulEquiv) n)
      (cyclicDiff (Units.mapEquiv s.toMulEquiv)))]
    [Finite (herbrandH (cyclicNorm (Units.mapEquiv t.toMulEquiv) n)
      (cyclicDiff (Units.mapEquiv t.toMulEquiv)))] :
    cyclicHerbrandQuotient (Units.mapEquiv t.toMulEquiv) n
      = cyclicHerbrandQuotient (Units.mapEquiv s.toMulEquiv) n * (n : ℚ) := by
  let σR := Units.mapEquiv s.toMulEquiv
  let σK := Units.mapEquiv t.toMulEquiv
  let ι := Units.map (algebraMap R K : R →* K)
  let v := dvrUnitsValuation R K
  have hι : ∀ u, ι (σR u) = σK (ι u) := dvrUnitsInclusion_equivariant R K s t hst
  have hv : ∀ x, v (σK x) = (1 : MulAut (Multiplicative ℤ)) (v x) :=
    dvrUnitsValuation_equivariant R K s t hst
  letI := finite_herbrandH_norm_diff_int n hn
  have hq := herbrandQuotient_mul ι v
    (cyclicDiff σR) (cyclicNorm σR n) (cyclicDiff σK) (cyclicNorm σK n)
    (cyclicDiff 1) (cyclicNorm 1 n)
    (dvrUnitsInclusion_injective R K) (dvrUnitsValuation_surjective R K)
    (dvrUnitsValuation_ker R K).symm
    (map_cyclicDiff ι σR σK hι) (map_cyclicNorm ι σR σK hι n)
    (map_cyclicDiff v σK 1 hv) (map_cyclicNorm v σK 1 hv n)
    (cyclicDiff_cyclicNorm σK n hσ) (cyclicNorm_cyclicDiff σK n hσ)
  change cyclicHerbrandQuotient σK n
    = cyclicHerbrandQuotient σR n * cyclicHerbrandQuotient 1 n at hq
  rw [cyclicHerbrandQuotient_int n hn] at hq
  exact hq


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms intValuation_ringEquiv
#print axioms dvrUnitsInclusion_injective
#print axioms dvrUnitsInclusion_equivariant
#print axioms dvrUnitsValuation_equivariant
#print axioms dvrUnitsValuation_cyclicDiff
#print axioms dvrUnitsValuation_cyclicNorm
#print axioms cyclicHerbrandQuotient_units

end Anabelian
