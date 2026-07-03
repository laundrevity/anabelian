/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.InertiaSetup
import Anabelian.Quotient.RamificationIdx
import Mathlib

/-!
# `e' = |H₀|` — the ramification index is the inertia cardinality (Pass 71)

The identification program of Passes 68–70 closes:

> **`(Nat.card (ramificationGroup K' (𝒪_L) 0) : ℕ∞) = addVal_{𝒪_L}(ι π_B)`**
> (`natCast_card_ramificationGroup_zero_eq_addVal`)

— the classical **`e = |inertia|`** for the Galois extension `L/K'`, in the project's
vocabulary: Pass 59's `addVal`-form `e'` equals the cardinality of `H₀`. Four rewrites:
Pass 70's definitional inertia matching, Mathlib's `card_inertia_eq_ramificationIdxIn`
(every hypothesis supplied by Passes 68–70), the single-prime reduction
`ramificationIdxIn_eq_ramificationIdx`, and Pass 68's `ramificationIdx = e'`.

With this, **every input to Lemma 5's numerical heart is proved**: the chain
P63 (sum formula) + P65 (fiber profile) + P66 (double count) + P67 (`φ`-bridge) + P71
(`e' = |H₀|`) assembles into `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j(σ̄) − 1)` — the next pass.

## Honesty

The closing application of the identification — **no reach toward R1–R3**. The numerical
Lemma 5 itself is NOT claimed (next pass). No new `structure`/`class`; no owed witness;
D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing IsDiscreteValuationRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **`e' = |H₀|`, explicit form** (the classical `e = |inertia|` for `L/K'`): if
`addVal(ι π_B) = n`, then `|ramificationGroup K' (𝒪_L) 0| = n`. The chain: the project's
`G₀` IS `Ideal.inertia 𝔪_L D` (Pass 70, definitional); Mathlib's
`card_inertia_eq_ramificationIdxIn` (`|inertia| = e`; its hypothesis package is Passes
68–70); the single-prime reduction `ramificationIdxIn_eq_ramificationIdx`; and Pass 68's
`ramificationIdx 𝔪_B 𝔪_L = n`. -/
theorem natCard_ramificationGroup_zero_eq
    {π : ↥((extensionIntegers K L).comap (algebraMap K' L))}
    (hπ : Irreducible π) {n : ℕ}
    (hn : addVal ↥(extensionIntegers K L)
        (comapRingHom K' (extensionIntegers K L) π) = (n : ℕ∞)) :
    Nat.card (ramificationGroup K' (extensionIntegers K L) 0) = n := by
  have hbot : IsLocalRing.maximalIdeal
      ↥((extensionIntegers K L).comap (algebraMap K' L)) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field'
  rw [ramificationGroup_zero_eq_inertia]
  rw [Ideal.card_inertia_eq_ramificationIdxIn
    (G := ((extensionIntegers K L).decompositionSubgroup K'))
    (IsLocalRing.maximalIdeal
      ↥((extensionIntegers K L).comap (algebraMap K' L)))
    hbot
    (IsLocalRing.maximalIdeal ↥(extensionIntegers K L))]
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx
    (IsLocalRing.maximalIdeal
      ↥((extensionIntegers K L).comap (algebraMap K' L)))
    (IsLocalRing.maximalIdeal ↥(extensionIntegers K L))
    ((extensionIntegers K L).decompositionSubgroup K')]
  exact ramificationIdx_comapRingHom K' (extensionIntegers K L) hπ hn

/-- **`e' = |H₀|`, `ℕ∞` form**: for any irreducible `π` of `B = 𝒪_L ∩ K'`,
`(|H₀| : ℕ∞) = addVal_{𝒪_L}(ι π)` — Pass 59's `addVal`-form ramification index IS the
cardinality of the inertia group of `L/K'`. The last input to Lemma 5's numerical heart. -/
theorem natCast_card_ramificationGroup_zero_eq_addVal
    {π : ↥((extensionIntegers K L).comap (algebraMap K' L))}
    (hπ : Irreducible π) :
    ((Nat.card (ramificationGroup K' (extensionIntegers K L) 0) : ℕ)
        : ℕ∞)
      = addVal ↥(extensionIntegers K L)
          (comapRingHom K' (extensionIntegers K L) π) := by
  have hπ0 : comapRingHom K' (extensionIntegers K L) π ≠ 0 := by
    intro h0
    have h1 : π = 0 := by
      apply Subtype.ext
      have h2 := congrArg Subtype.val h0
      change algebraMap K' L (π : K') = 0 at h2
      exact (map_eq_zero (algebraMap K' L)).mp h2
    exact hπ.ne_zero h1
  have htop : addVal ↥(extensionIntegers K L)
      (comapRingHom K' (extensionIntegers K L) π) ≠ ⊤ := by
    rw [Ne, addVal_eq_top_iff]
    exact hπ0
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hn]
  exact congrArg (fun m : ℕ => (m : ℕ∞))
    (natCard_ramificationGroup_zero_eq K K' hπ hn.symm)


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms natCard_ramificationGroup_zero_eq
#print axioms natCast_card_ramificationGroup_zero_eq_addVal

end Anabelian
