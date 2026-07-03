/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Ramification.LowerIndex
import Anabelian.Quotient.Basic
import Anabelian.Quotient.LiftSet
import Mathlib

/-!
# Toward Serre IV §3 Lemma 5: the fiber index profile (Pass 65)

Lemma 5 (`(G/H)_{φ_{L/K'}(u)} = G_u H/H`) rests on a counting identity: for `σ̄ ≠ 1` and a
lift `s₁` of maximal lower index `j(σ̄)`, the indices over the whole fiber are

> **`i_{L/K}(s₁·h) = min(i_H(h), j(σ̄))` for every `h ∈ H`**,

so Pass 63's sum formula reads `e'·i_{K'/K}(σ̄) = Σ_{h} min(i_H(h), j)` — and the right side
is exactly what the Herbrand `φ` counts (Pass 48's piecewise formula), which will yield
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)`. This pass proves the profile (abstract, `Normal`-free,
coset form), the existence of a maximizer (finiteness), the fiber-language packaging, and
the `Σ min` form of the fiber sum.

Everything is Pass 51 calculus — the `ℕ∞`-valued `lowerIndex`, its `min`-inequality, its
`inv`-invariance, and `i_H = i_G` (which is `rfl`). No new ramification input.

## Honesty

Order bookkeeping for the indices of a given tower — **no reach toward R1–R3**. Lemma 5
itself, the `Σ min`-vs-`φ` counting, and the renumbering statement are NOT claimed — next
bricks. No new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian


section Abstract

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable (A : ValuationSubring L)

/-- **The fiber index profile** (Serre IV §3, inside the proof of Lemma 5): if `s₁`
maximizes `i_{L/K}` over its coset `s₁·H`, then for every `h ∈ H`,
`i(s₁·h) = min(i_H(h), i(s₁))`. Both directions are Pass 51's calculus: `≥` is the subgroup
inequality (`min_lowerIndex_le_lowerIndex_mul` + `i_H = i_G`); for `≤` in the
`i_H(h) < i(s₁)` case, the cancellation `dr h = s₁⁻¹·(s₁·dr h)` and `i(s₁⁻¹) = i(s₁)` force
`i(s₁·h) ≤ i_H(h)` on pain of `i_H(h) < i_H(h)`. -/
theorem lowerIndex_mul_decompositionRestrict_eq_min
    {s₁ : A.decompositionSubgroup K}
    (hmax : ∀ h' : A.decompositionSubgroup K',
      lowerIndex K A (s₁ * decompositionRestrict K K' A h')
        ≤ lowerIndex K A s₁)
    (h : A.decompositionSubgroup K') :
    lowerIndex K A (s₁ * decompositionRestrict K K' A h)
      = min (lowerIndex K' A h) (lowerIndex K A s₁) := by
  have hlow : min (lowerIndex K A s₁) (lowerIndex K' A h)
      ≤ lowerIndex K A (s₁ * decompositionRestrict K K' A h) := by
    have h1 := min_lowerIndex_le_lowerIndex_mul K A s₁
      (decompositionRestrict K K' A h)
    rwa [lowerIndex_decompositionRestrict] at h1
  rcases le_or_gt (lowerIndex K A s₁) (lowerIndex K' A h) with hle | hlt
  · -- j ≤ i_H(h): the min is j, and s₁·h also attains the max
    rw [min_eq_right hle]
    refine le_antisymm (hmax h) ?_
    calc lowerIndex K A s₁
        = min (lowerIndex K A s₁) (lowerIndex K' A h) :=
          (min_eq_left hle).symm
      _ ≤ _ := hlow
  · -- i_H(h) < j: the min is i_H(h); ≥ from the subgroup inequality, ≤ by the
    -- s₁⁻¹-cancellation trick
    rw [min_eq_left (le_of_lt hlt)]
    refine le_antisymm ?_ ?_
    · by_contra hgt
      push Not at hgt
      have h2 : min (lowerIndex K A s₁⁻¹)
          (lowerIndex K A (s₁ * decompositionRestrict K K' A h))
          ≤ lowerIndex K A (decompositionRestrict K K' A h) := by
        have h3 := min_lowerIndex_le_lowerIndex_mul K A s₁⁻¹
          (s₁ * decompositionRestrict K K' A h)
        rwa [inv_mul_cancel_left] at h3
      rw [lowerIndex_inv, lowerIndex_decompositionRestrict] at h2
      have h4 : lowerIndex K' A h < lowerIndex K' A h :=
        lt_of_lt_of_le (lt_min hlt hgt) h2
      exact absurd h4 (lt_irrefl _)
    · calc lowerIndex K' A h
          = min (lowerIndex K A s₁) (lowerIndex K' A h) :=
            (min_eq_right (le_of_lt hlt)).symm
        _ ≤ _ := hlow

/-- A coset maximizer exists (finiteness), and with it the profile: there is `h₀` such that
`s₁ := s₀·dr h₀` satisfies `i(s₁·dr h) = min(i_H(h), i(s₁))` for every `h`. -/
theorem exists_coset_lowerIndex_eq_min [Finite (A.decompositionSubgroup K')]
    (s₀ : A.decompositionSubgroup K) :
    ∃ h₀ : A.decompositionSubgroup K',
      ∀ h : A.decompositionSubgroup K',
        lowerIndex K A
            ((s₀ * decompositionRestrict K K' A h₀)
              * decompositionRestrict K K' A h)
          = min (lowerIndex K' A h)
              (lowerIndex K A
                (s₀ * decompositionRestrict K K' A h₀)) := by
  haveI := Fintype.ofFinite (A.decompositionSubgroup K')
  obtain ⟨h₀, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun h' : A.decompositionSubgroup K' =>
      lowerIndex K A (s₀ * decompositionRestrict K K' A h'))
    ⟨1, Finset.mem_univ 1⟩
  refine ⟨h₀, ?_⟩
  refine lowerIndex_mul_decompositionRestrict_eq_min K K' A ?_
  intro h'
  have h5 : (s₀ * decompositionRestrict K K' A h₀)
      * decompositionRestrict K K' A h'
      = s₀ * decompositionRestrict K K' A (h₀ * h') := by
    rw [map_mul, mul_assoc]
  rw [h5]
  exact hmax (h₀ * h') (Finset.mem_univ _)

end Abstract

section Fiber

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [Normal K K']
variable (A : ValuationSubring L)

/-- Fiber-language form: over the fiber of `σ̄ = decompositionQuotient s₀` there is a
maximizer `s₁` (in the same fiber — Pass 56's coset stability) whose profile is
`i(s₁·dr h) = min(i_H(h), i(s₁))`. Serre's `j(σ̄)` is `i(s₁)`. -/
theorem exists_fiber_lowerIndex_eq_min [Finite (A.decompositionSubgroup K')]
    (s₀ : A.decompositionSubgroup K) :
    ∃ s₁ : A.decompositionSubgroup K,
      decompositionQuotient K K' A s₁
          = decompositionQuotient K K' A s₀
      ∧ ∀ h : A.decompositionSubgroup K',
          lowerIndex K A (s₁ * decompositionRestrict K K' A h)
            = min (lowerIndex K' A h) (lowerIndex K A s₁) := by
  obtain ⟨h₀, hprof⟩ := exists_coset_lowerIndex_eq_min K K' A s₀
  exact ⟨s₀ * decompositionRestrict K K' A h₀,
    decompositionQuotient_mul_decompositionRestrict K K' A s₀ h₀, hprof⟩

/-- **The fiber sum in Serre's `Σ min` form**: for a fiber maximizer `s₁`,
`Σ_{s ↦ σ̄} i_{L/K}(s) = Σ_{h ∈ H} min(i_H(h), j)` with `j = i(s₁)` — the shape that Pass
48's piecewise `φ`-formula will count, converting Pass 63's sum formula into
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)` (Lemma 5's numerical heart, next bricks). -/
theorem sum_lowerIndex_fiber_eq_sum_min [Fintype (A.decompositionSubgroup K')]
    (s₀ : A.decompositionSubgroup K) :
    ∃ s₁ : A.decompositionSubgroup K,
      decompositionQuotient K K' A s₁
          = decompositionQuotient K K' A s₀
      ∧ ∑ h : A.decompositionSubgroup K',
            lowerIndex K A (s₁ * decompositionRestrict K K' A h)
          = ∑ h : A.decompositionSubgroup K',
              min (lowerIndex K' A h) (lowerIndex K A s₁) := by
  obtain ⟨s₁, hfib, hprof⟩ := exists_fiber_lowerIndex_eq_min K K' A s₀
  exact ⟨s₁, hfib, Finset.sum_congr rfl fun h _ => hprof h⟩

end Fiber


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms lowerIndex_mul_decompositionRestrict_eq_min
#print axioms exists_coset_lowerIndex_eq_min
#print axioms exists_fiber_lowerIndex_eq_min
#print axioms sum_lowerIndex_fiber_eq_sum_min

end Anabelian
