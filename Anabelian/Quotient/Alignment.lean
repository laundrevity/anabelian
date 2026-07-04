/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.LemmaFive
import Mathlib

/-!
# The alignment lemma: the quotient filtration jumps only at `φ`-images (Pass 75)

The hard step of Prop. 15's analytic gluing, flagged for design at Pass 74 — now proved.
For the tower `K ⊆ K' ⊆ L` and every `n : ℕ`:

> **the `B`-filtration is constant on integer indices `w ∈ (φ_{L/K'}(n), ⌈φ_{L/K'}(n+1)⌉]`**
> (`ramificationGroup_comap_eq_of_lt`),

with the real-`u` corollary `(G/H)_{⌊φ_{L/K'}(u)⌋+1} = (G/H)_{⌈φ_{L/K'}(n+1)⌉}` for
`u ∈ [n, n+1)` (`ramificationGroup_comap_floor_add_one_eq`) — exactly the statement that
the composite `φ_{K'/K} ∘ φ_{L/K'}` has CONSTANT right-slope on each `[n, n+1)`, which by
Pass 74's multiplicativity equals `φ_{L/K}`'s right-slope `|G_{n+1}|/|G_0|` there.

The proof is a jewel of the P72 design: the numerical Lemma 5 delivers `i_{K'/K}(σ̄) ∈ ℕ`
with `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j(σ̄) − 1)` — an INTEGER. A member `σ̄` of `(G/H)_w` with
`w > φ(n)` therefore has `φ(n) < w ≤ φ(j−1)`, so `j − 1 ≥ n + 1` by `φ`'s strict
monotonicity (Pass 44), so `i_{K'/K}(σ̄) ≥ φ(n+1) + 1 > ⌈φ(n+1)⌉` — the membership persists
to the right end of the window. No measure theory, no interval integrals: the "no interior
jump" fact is pure arithmetic of the jump values.

What remains for Prop. 15 (`φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}`): the right-derivative
computation for `φ` from Pass 48's affine formula, the chain rule for right derivatives
along the monotone `φ_{L/K'}`, and the glue (`eq_of_has_deriv_right_eq`-style, or
ℕ-induction + affine interpolation) — next passes.

## Honesty

A constancy window for a given tower's quotient filtration — **no reach toward R1–R3**.
Prop. 15 itself is NOT claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2
untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Normal K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **THE ALIGNMENT LEMMA** (the flagged hard step of Prop. 15's gluing): the `B`-filtration
is CONSTANT on integer indices in the window `(φ_{L/K'}(n), ⌈φ_{L/K'}(n+1)⌉]` — the quotient
filtration jumps only at `φ`-images of integers. The crux is Pass 72's INTEGRALITY: for
`σ̄ ≠ 1`, `i_{K'/K}(σ̄) = a ∈ ℕ` with `a − 1 = φ_{L/K'}(j−1)`; so `σ̄ ∈ (G/H)_w` with
`w > φ(n)` forces `φ(n) < w ≤ a − 1 = φ(j−1)`, hence `j − 1 ≥ n+1` by strict monotonicity,
hence `a ≥ φ(n+1) + 1 > ⌈φ(n+1)⌉` — membership persists to the window's right end. -/
theorem ramificationGroup_comap_eq_of_lt {n w : ℕ}
    (hw : herbrandPhi K' (extensionIntegers K L) (n : ℝ) < w)
    (hw' : w ≤ ⌈herbrandPhi K' (extensionIntegers K L)
        ((n + 1 : ℕ) : ℝ)⌉₊) :
    ramificationGroup K
        ((extensionIntegers K L).comap (algebraMap K' L)) w
      = ramificationGroup K
          ((extensionIntegers K L).comap (algebraMap K' L))
          ⌈herbrandPhi K' (extensionIntegers K L) ((n + 1 : ℕ) : ℝ)⌉₊ := by
  refine le_antisymm ?_
    (ramificationGroup_antitone K
      ((extensionIntegers K L).comap (algebraMap K' L)) hw')
  intro τ hτ
  by_cases hτ1 : τ = 1
  · subst hτ1
    exact Subgroup.one_mem _
  -- τ ≠ 1: P52 lift + P72 numerical data
  obtain ⟨s₀, rfl⟩ := decompositionQuotient_extensionIntegers_surjective K K'
    (L := L) τ
  obtain ⟨s₁, m, a, hfib, hm, hprof, ha, hφ⟩ :=
    exists_lowerIndex_eq_herbrandPhi K K' s₀ hτ1
  -- membership at w: w < a
  rw [mem_ramificationGroup_iff_lt_lowerIndex, ← ha] at hτ
  have hwa : w < a := by exact_mod_cast hτ
  -- m = 0 is impossible (a = 0 would contradict w < a)
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    have ha0 : (a : ℝ) = 0 := by
      rw [hφ, herbrandPhi_eq_id K' (extensionIntegers K L)
        (by norm_num)]
      norm_num
    have : a = 0 := by exact_mod_cast ha0
    omega
  -- m = k + 1: w ≤ a − 1 = φ(k), so φ(n) < φ(k), so k ≥ n + 1, so a > ⌈φ(n+1)⌉
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
  have hφk : herbrandPhi K' (extensionIntegers K L) (k : ℝ)
      = (a : ℝ) - 1 := by
    rw [hφ]
    push_cast
    ring_nf
  have hwk : (w : ℝ) ≤ herbrandPhi K' (extensionIntegers K L) (k : ℝ) := by
    rw [hφk]
    have : (w : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast hwa
    linarith
  have hnk : n < k := by
    by_contra hkn
    push Not at hkn
    have h1 : herbrandPhi K' (extensionIntegers K L) (k : ℝ)
        ≤ herbrandPhi K' (extensionIntegers K L) (n : ℝ) := by
      apply herbrandPhi_monotone K' (extensionIntegers K L)
      exact_mod_cast hkn
    linarith [lt_of_lt_of_le hw hwk]
  have hφn1k : herbrandPhi K' (extensionIntegers K L) ((n + 1 : ℕ) : ℝ)
      ≤ herbrandPhi K' (extensionIntegers K L) (k : ℝ) := by
    apply herbrandPhi_monotone K' (extensionIntegers K L)
    exact_mod_cast hnk
  have hceil : ⌈herbrandPhi K' (extensionIntegers K L)
      ((n + 1 : ℕ) : ℝ)⌉₊ < a := by
    have hnn : (0 : ℝ) ≤ herbrandPhi K' (extensionIntegers K L)
        ((n + 1 : ℕ) : ℝ) := by
      rw [← herbrandPhi_zero K' (extensionIntegers K L)]
      apply herbrandPhi_monotone K' (extensionIntegers K L)
      exact_mod_cast Nat.zero_le (n + 1)
    have h2 : (⌈herbrandPhi K' (extensionIntegers K L)
        ((n + 1 : ℕ) : ℝ)⌉₊ : ℝ)
        < herbrandPhi K' (extensionIntegers K L) ((n + 1 : ℕ) : ℝ)
          + 1 := Nat.ceil_lt_add_one hnn
    have h4 := hφn1k
    rw [hφk] at h4
    have h3 : (⌈herbrandPhi K' (extensionIntegers K L)
        ((n + 1 : ℕ) : ℝ)⌉₊ : ℝ) < (a : ℝ) := by
      linarith
    exact_mod_cast h3
  rw [mem_ramificationGroup_iff_lt_lowerIndex, ← ha]
  exact_mod_cast hceil

/-- The real-`u` form the right-derivative gluing consumes: for `u ∈ [n, n+1)`, the
right-slope index `⌊φ_{L/K'}(u)⌋ + 1` of `φ_{K'/K}` lands in the alignment window, so
`(G/H)_{⌊φ(u)⌋+1} = (G/H)_{⌈φ(n+1)⌉}` — the composite `φ_{K'/K} ∘ φ_{L/K'}` has constant
right-slope on `[n, n+1)`, matching `φ_{L/K}`'s via Pass 74. -/
theorem ramificationGroup_comap_floor_add_one_eq {n : ℕ} {u : ℝ}
    (hun : (n : ℝ) ≤ u) (hu : u < ((n + 1 : ℕ) : ℝ)) :
    ramificationGroup K
        ((extensionIntegers K L).comap (algebraMap K' L))
        (⌊herbrandPhi K' (extensionIntegers K L) u⌋₊ + 1)
      = ramificationGroup K
          ((extensionIntegers K L).comap (algebraMap K' L))
          ⌈herbrandPhi K' (extensionIntegers K L) ((n + 1 : ℕ) : ℝ)⌉₊ := by
  have hmono := herbrandPhi_monotone K' (extensionIntegers K L)
  have hφnu : herbrandPhi K' (extensionIntegers K L) (n : ℝ)
      ≤ herbrandPhi K' (extensionIntegers K L) u := hmono hun
  have hφu1 : herbrandPhi K' (extensionIntegers K L) u
      < herbrandPhi K' (extensionIntegers K L) ((n + 1 : ℕ) : ℝ) :=
    herbrandPhi_strictMono K' (extensionIntegers K L) hu
  have hφu0 : (0 : ℝ) ≤ herbrandPhi K' (extensionIntegers K L) u := by
    rw [← herbrandPhi_zero K' (extensionIntegers K L)]
    apply hmono
    exact le_trans (by exact_mod_cast Nat.zero_le n) hun
  apply ramificationGroup_comap_eq_of_lt K K'
  · calc herbrandPhi K' (extensionIntegers K L) (n : ℝ)
        ≤ herbrandPhi K' (extensionIntegers K L) u := hφnu
      _ < (⌊herbrandPhi K' (extensionIntegers K L) u⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one _
      _ = ((⌊herbrandPhi K' (extensionIntegers K L) u⌋₊ + 1 : ℕ) : ℝ) :=
          by push_cast; ring
  · by_contra hcon
    push Not at hcon
    have h1 : ⌈herbrandPhi K' (extensionIntegers K L)
        ((n + 1 : ℕ) : ℝ)⌉₊
        ≤ ⌊herbrandPhi K' (extensionIntegers K L) u⌋₊ := by omega
    have h2 : herbrandPhi K' (extensionIntegers K L) ((n + 1 : ℕ) : ℝ)
        ≤ herbrandPhi K' (extensionIntegers K L) u :=
      le_trans (Nat.le_ceil _)
        (le_trans (by exact_mod_cast h1) (Nat.floor_le hφu0))
    linarith


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms ramificationGroup_comap_eq_of_lt
#print axioms ramificationGroup_comap_floor_add_one_eq

end Anabelian
