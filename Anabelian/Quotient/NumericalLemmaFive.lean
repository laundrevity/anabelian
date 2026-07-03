/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.SumFormula
import Anabelian.Quotient.IndexProfile
import Anabelian.Ramification.LowerIndexCount
import Anabelian.Herbrand.SumBridge
import Anabelian.Quotient.InertiaCard
import Mathlib

/-!
# THE NUMERICAL LEMMA 5: `i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1` (Pass 72)

The assembly the last nine passes built toward. For a tower `K ⊆ K' ⊆ L` over a
nonarchimedean local field (`K'/K` normal, `L/K'` Galois) and any `σ̄ ≠ 1` in the
subextension's decomposition group:

> **`i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1`** (`exists_lowerIndex_eq_herbrandPhi`)

where `j(σ̄) = max_{s ↦ σ̄} i_{L/K}(s)` (realized by a fiber maximizer `s₁`, exposed with
its full index profile). This is the numerical identity from which Serre derives Lemma 5
(`(G/H)_{φ_{L/K'}(u)} = G_u H/H`), Prop. 15 (`φ`-transitivity), and Prop. 14 (Herbrand's
theorem). The chain, every link a named pass:

`i_{K'/K}(σ̄)·e' = Σ_{s ↦ σ̄} i_{L/K}(s)` (P63, Prop. 3) `= Σ_h min(i_H(h), j)` (P65)
`= Σ_{k<j} |H_k|` (P66; `j` finite for `σ̄ ≠ 1` by P51's `⊤`-criterion under the DVR
separations) `= |H₀|·(φ_{L/K'}(j−1) + 1)` (P67), and `e' = |H₀|` (P71) cancels. The
degenerate `j = 0` case rides on `φ(−1) = −1` (P44's `herbrandPhi_eq_id`).

## Honesty

A numerical identity for the Galois theory of a **given** tower — **no reach toward
R1–R3**; nothing recovered from an abstract group. The set-level Lemma 5 (the subgroup
identity via P51's membership forms), Prop. 15, and Prop. 14 are NOT claimed — next passes.
No new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

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
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **THE NUMERICAL LEMMA 5** (Serre, *Local Fields*, IV §3, the identity behind Lemma 5):
for `σ̄ = decompositionQuotient s₀ ≠ 1` there are a fiber maximizer `s₁` (same fiber, with
the full index profile `i(s₁·h) = min(i_H(h), j)`), `m = j(σ̄) ∈ ℕ` (Serre's maximal lift
index — finite since `σ̄ ≠ 1`), and `a = i_{K'/K}(σ̄) ∈ ℕ`, with

`i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1`

(read in `ℝ`; at `j = 0` both sides vanish via `φ(−1) = −1`). Pure assembly: P63 (sum
formula at `s₁`) + P65 (fiber profile) + P66 (double count, `j` finite) + P71 (`e' = |H₀|`)
+ P67 (casts + the `φ`-bridge), with P51's `lowerIndex_eq_top_iff` supplying finiteness
under the DVR separations. -/
theorem exists_lowerIndex_eq_herbrandPhi
    (s₀ : (extensionIntegers K L).decompositionSubgroup K)
    (hσ : decompositionQuotient K K' (extensionIntegers K L) s₀ ≠ 1) :
    ∃ (s₁ : (extensionIntegers K L).decompositionSubgroup K) (m a : ℕ),
      decompositionQuotient K K' (extensionIntegers K L) s₁
        = decompositionQuotient K K' (extensionIntegers K L) s₀
      ∧ (m : ℕ∞) = lowerIndex K (extensionIntegers K L) s₁
      ∧ (∀ h : (extensionIntegers K L).decompositionSubgroup K',
          lowerIndex K (extensionIntegers K L)
              (s₁ * decompositionRestrict K K'
                (extensionIntegers K L) h)
            = min (lowerIndex K' (extensionIntegers K L) h) (m : ℕ∞))
      ∧ (a : ℕ∞) = lowerIndex K
          ((extensionIntegers K L).comap (algebraMap K' L))
          (decompositionQuotient K K' (extensionIntegers K L) s₀)
      ∧ (a : ℝ) = herbrandPhi K' (extensionIntegers K L) ((m : ℝ) - 1)
          + 1 := by
  haveI := Fintype.ofFinite ((extensionIntegers K L).decompositionSubgroup K')
  -- the fiber maximizer and its profile (P65)
  obtain ⟨s₁, hfib, hprof⟩ :=
    exists_fiber_lowerIndex_eq_min K K' (extensionIntegers K L) s₀
  -- j is finite (σ̄ ≠ 1 ⟹ s₁ ≠ 1 + separation at 𝒪_L)
  haveI := isNoetherianRing_extensionIntegers K L
  have hs₁1 : s₁ ≠ 1 := by
    intro h
    rw [h, map_one] at hfib
    exact hσ hfib.symm
  have hsepL : (⨅ n : ℕ, IsLocalRing.maximalIdeal ↥(extensionIntegers K L) ^ n)
      = ⊥ := Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
  have hjtop : lowerIndex K (extensionIntegers K L) s₁ ≠ ⊤ := by
    intro h
    exact hs₁1 ((lowerIndex_eq_top_iff K _ hsepL).mp h)
  obtain ⟨m, hm₀⟩ := WithTop.ne_top_iff_exists.mp hjtop
  have hm : (m : ℕ∞) = lowerIndex K (extensionIntegers K L) s₁ := by
    exact_mod_cast hm₀
  -- i(σ̄) is finite (σ̄ ≠ 1 + separation at B)
  have hsepB : (⨅ n : ℕ, IsLocalRing.maximalIdeal
      ↥((extensionIntegers K L).comap (algebraMap K' L)) ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
  have hatop : lowerIndex K
      ((extensionIntegers K L).comap (algebraMap K' L))
      (decompositionQuotient K K' (extensionIntegers K L) s₀)
      ≠ ⊤ := by
    intro h
    exact hσ ((lowerIndex_eq_top_iff K _ hsepB).mp h)
  obtain ⟨a, ha₀⟩ := WithTop.ne_top_iff_exists.mp hatop
  have ha : (a : ℕ∞) = lowerIndex K
      ((extensionIntegers K L).comap (algebraMap K' L))
      (decompositionQuotient K K' (extensionIntegers K L) s₀) := by
    exact_mod_cast ha₀
  -- the profile with m
  have hprofm : ∀ h : (extensionIntegers K L).decompositionSubgroup K',
      lowerIndex K (extensionIntegers K L)
          (s₁ * decompositionRestrict K K' (extensionIntegers K L) h)
        = min (lowerIndex K' (extensionIntegers K L) h) (m : ℕ∞) := by
    intro h
    rw [hprof h, ← hm]
  refine ⟨s₁, m, a, hfib, hm, hprofm, ha, ?_⟩
  -- the ℕ∞ chain: P63 at s₁, P65 profile, P66 double count, P71 e' = |H₀|, P67 casts
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    ↥((extensionIntegers K L).comap (algebraMap K' L))
  have h63 := lowerIndex_decompositionQuotient_mul_eq_sum K K'
    (s₀ := s₁) hπ
  rw [hfib] at h63
  have h65 : ∑ h : (extensionIntegers K L).decompositionSubgroup K',
      lowerIndex K (extensionIntegers K L)
        (s₁ * decompositionRestrict K K' (extensionIntegers K L) h)
      = ∑ h : (extensionIntegers K L).decompositionSubgroup K',
          min (lowerIndex K' (extensionIntegers K L) h) (m : ℕ∞) :=
    Finset.sum_congr rfl fun h _ => hprofm h
  rw [h65, sum_min_lowerIndex_eq K' (extensionIntegers K L) m,
      ← natCast_card_ramificationGroup_zero_eq_addVal K K' hπ,
      ← ha, sum_natCard_enat_eq] at h63
  -- down to ℕ
  have hnat : a * Nat.card (ramificationGroup K' (extensionIntegers K L) 0)
      = ∑ k ∈ Finset.range m,
          Nat.card (ramificationGroup K' (extensionIntegers K L) k) := by
    exact_mod_cast h63
  -- up to ℝ, case on m
  have hcard0 : (0 : ℝ) < ramificationOrders K' (extensionIntegers K L) 0 :=
    ramificationOrders_pos K' (extensionIntegers K L) 0
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: both sides vanish; φ(−1) = −1
    subst hm0
    have ha0 : a = 0 := by
      have h1 : a * Nat.card
          (ramificationGroup K' (extensionIntegers K L) 0) = 0 := by
        simpa using hnat
      rcases Nat.mul_eq_zero.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 Nat.card_pos.ne'
    subst ha0
    rw [herbrandPhi_eq_id K' (extensionIntegers K L) (by norm_num)]
    norm_num
  · -- m = n + 1: the φ-bridge (P67)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    have hR := congrArg (Nat.cast : ℕ → ℝ) hnat
    rw [natCast_sum_natCard_eq K' (extensionIntegers K L) n] at hR
    have hstep : ((a * Nat.card
        (ramificationGroup K' (extensionIntegers K L) 0) : ℕ) : ℝ)
        = (a : ℝ)
          * ramificationOrders K' (extensionIntegers K L) 0 := by
      push_cast
      rfl
    rw [hstep] at hR
    have hfin : (a : ℝ) = herbrandPhi K' (extensionIntegers K L)
        (n : ℝ) + 1 := by
      have hne : ramificationOrders K' (extensionIntegers K L) 0 ≠ 0 :=
        ne_of_gt hcard0
      have h4 : (a : ℝ) * ramificationOrders K' (extensionIntegers K L) 0
          = (herbrandPhi K' (extensionIntegers K L) (n : ℝ) + 1)
            * ramificationOrders K' (extensionIntegers K L) 0 := by
        rw [hR]
        ring
      exact mul_right_cancel₀ hne h4
    have harg : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [harg, hfin]


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms exists_lowerIndex_eq_herbrandPhi

end Anabelian
