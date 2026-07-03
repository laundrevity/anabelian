/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.AddVal
import Anabelian.Ramification.LowerIndexGenerator
import Mathlib

/-!
# Toward `e' = |H₀|`: the ramification index in ideal form (Pass 68)

The last input to Lemma 5's numerical heart is **`e' = |H₀|`** — the classical
"`e = |inertia|`" for the Galois extension `L/K'`. The Pass-68 inventory found that Mathlib
**has** this theorem in ideal-theoretic form: `Ideal.card_inertia_eq_ramificationIdxIn`
(Dedekind domains, separable residue — satisfied here, residue fields being finite). So the
task becomes an *identification program*: connect the project's objects to Mathlib's. This
pass is its first brick — **`e'` itself, in ideal form**:

* `comapAlgebra` — `𝒪_L` as a `B = 𝒪_L ∩ K'`-algebra via the tower inclusion
  (`RingHom.toAlgebra`; no canonical instance exists, so no diamond) — the scaffold
  Mathlib's Algebra-based `RamificationInertia` API requires;
* **`map_maximalIdeal_comapRingHom`** — `𝔪_B·𝒪_L = 𝔪_L^n` with `(n : ℕ∞) = addVal(ι π_B)`
  (Pass 59's `e'`);
* **`ramificationIdx_comapRingHom`** — hence `Ideal.ramificationIdx 𝔪_B 𝔪_L = n`: the
  `addVal`-form `e'` IS Mathlib's ramification index.

Remaining bricks of the identification (next passes): the Dedekind/finite/torsion-free
instance package for `(B, 𝒪_L)`, the matching of the project's inertia
(`ramificationGroup K' (𝒪_L) 0`, a subgroup of `D_{K'}(𝒪_L)`) with Mathlib's
`Ideal.inertia G P`, and the application of `card_inertia_eq_ramificationIdxIn`.

## Honesty

DVR/ideal bookkeeping for a given tower — **no reach toward R1–R3**. `e' = |H₀|` itself is
NOT claimed (this is its left half: `e'` = the ideal-theoretic `e`). The `comapAlgebra`
instance is an instance of the existing `Algebra` class, not a new `structure`/`class` — no
rule-2 obligation; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing IsDiscreteValuationRing
open scoped Pointwise

namespace Anabelian


variable (K' : Type*) [Field K']
variable {L : Type*} [Field L] [Algebra K' L]
variable (A : ValuationSubring L)

/-- **The tower inclusion as an algebra**: `𝒪_L` is a `B = 𝒪_L ∩ K'`-algebra via
`comapRingHom` — the scaffold on which Mathlib's `Ideal.ramificationIdx`/`RamificationInertia`
API (Algebra-based) will run. No canonical `Algebra ↥B ↥A` instance exists in Mathlib (the
two rings are subtypes over different fields), so `RingHom.toAlgebra` introduces no
diamond. -/
noncomputable instance comapAlgebra :
    Algebra ↥(A.comap (algebraMap K' L)) ↥A :=
  (comapRingHom K' A).toAlgebra

/-- The algebra map of `comapAlgebra` is `comapRingHom`, definitionally. -/
theorem algebraMap_comapAlgebra :
    algebraMap ↥(A.comap (algebraMap K' L)) ↥A = comapRingHom K' A := rfl

variable [IsDiscreteValuationRing ↥A]
  [IsDiscreteValuationRing ↥(A.comap (algebraMap K' L))]

/-- **`e'` in ideal form**: the extension of the maximal ideal along the tower inclusion is
the `n`-th power of the maximal ideal upstairs, where `(n : ℕ∞) = addVal (ι π_B)` is Pass
59's `addVal`-form ramification index — `𝔪_B·𝒪_L = 𝔪_L^{e'}`. (`𝔪_B = (π_B)`, and
`ι π_B = u·ϖ^n` up to a unit.) -/
theorem map_maximalIdeal_comapRingHom
    {π : ↥(A.comap (algebraMap K' L))} (hπ : Irreducible π) {n : ℕ}
    (hn : addVal ↥A (comapRingHom K' A π) = (n : ℕ∞)) :
    Ideal.map (comapRingHom K' A)
        (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap K' L)))
      = IsLocalRing.maximalIdeal ↥A ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A
  have hπ0 : comapRingHom K' A π ≠ 0 := by
    intro h0
    have h1 : π = 0 := by
      apply Subtype.ext
      have h2 := congrArg Subtype.val h0
      change algebraMap K' L (π : K') = 0 at h2
      exact (map_eq_zero (algebraMap K' L)).mp h2
    exact hπ.ne_zero h1
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hϖ
  have hm : m = n := by
    have h3 : addVal ↥A (comapRingHom K' A π) = (m : ℕ∞) := by
      rw [hu]
      exact addVal_def' u hϖ m
    rw [h3] at hn
    exact_mod_cast hn
  subst hm
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, hu]
  have hassoc : Associated (ϖ ^ m) ((u : ↥A) * ϖ ^ m) := ⟨u, by ring⟩
  rw [(Ideal.span_singleton_eq_span_singleton).mpr hassoc.symm]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- **The Mathlib-facing handle**: `Ideal.ramificationIdx 𝔪_B 𝔪_A = n` (with the
`comapAlgebra` structure) — Pass 59's `addVal`-form `e'` IS Mathlib's ideal-theoretic
ramification index. The hook for `Ideal.card_inertia_eq_ramificationIdxIn` (`|inertia| = e`),
the target of the coming identification bricks. -/
theorem ramificationIdx_comapRingHom
    {π : ↥(A.comap (algebraMap K' L))} (hπ : Irreducible π) {n : ℕ}
    (hn : addVal ↥A (comapRingHom K' A π) = (n : ℕ∞)) :
    Ideal.ramificationIdx
        (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap K' L)))
        (IsLocalRing.maximalIdeal ↥A)
      = n := by
  have hmap : Ideal.map (algebraMap ↥(A.comap (algebraMap K' L)) ↥A)
      (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap K' L)))
      = IsLocalRing.maximalIdeal ↥A ^ n := by
    rw [algebraMap_comapAlgebra]
    exact map_maximalIdeal_comapRingHom K' A hπ hn
  refine Ideal.ramificationIdx_spec (le_of_eq hmap) ?_
  rw [hmap]
  intro hle
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥A
  have h4 : ϖ ^ n ∈ IsLocalRing.maximalIdeal ↥A ^ n := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have h5 := hle h4
  rw [mem_maximalIdeal_pow_iff_le_addVal, hϖ.addVal_pow] at h5
  have h6 : (n + 1 : ℕ) ≤ n := by exact_mod_cast h5
  omega


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms comapAlgebra
#print axioms algebraMap_comapAlgebra
#print axioms map_maximalIdeal_comapRingHom
#print axioms ramificationIdx_comapRingHom

end Anabelian
