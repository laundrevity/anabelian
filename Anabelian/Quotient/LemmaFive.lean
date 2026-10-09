/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.NumericalLemmaFive
import Anabelian.Quotient.Surjective
import Mathlib

/-!
# SERRE IV §3 LEMMA 5: `(G/H)_{φ_{L/K'}(u)} = G_u H/H` (Pass 73)

**Herbrand's renumbering lemma is a theorem.** For a tower `K ⊆ K' ⊆ L` of finite
extensions of a nonarchimedean local field (`L/K` and `K'/K` normal, `L/K'` Galois), and
every `u : ℕ`:

> **`(ramificationGroup K (𝒪_L) u).map (decompositionQuotient)
>   = ramificationGroup K (𝒪_L ∩ K') ⌈φ_{L/K'}(u)⌉₊`**
> (`map_ramificationGroup_eq_ceil`)

— the image of `G_u` in the quotient `Gal(K'/K)`-side is the lower filtration of the
subextension at the `φ_{L/K'}`-renumbered index (the `⌈·⌉₊`-convention matching Pass 45's
real-indexed upper numbering: Serre's `(G/H)_v := (G/H)_{⌈v⌉}`). This is the statement that
makes the **upper numbering quotient-compatible**: Prop. 15 (`φ`-transitivity) and Prop. 14
(**Herbrand's theorem** `(G/H)^v = G^v H/H`) are its corollaries — the next passes.

The proof: fix `σ̄`; a lift exists (Pass 52); for `σ̄ ≠ 1` Pass 72 supplies the maximizer
`s₁`, `j(σ̄) = m`, `i_{K'/K}(σ̄) = a`, and `a = φ_{L/K'}(m−1) + 1`; then
`σ̄ ∈ LHS ↔ u < m` (the lift-membership characterization — the profile bounds the fiber,
the maximizer realizes it) and `σ̄ ∈ RHS ↔ ⌈φ(u)⌉ < a ↔ u < m` (Pass 51's Lemma 1 + the
ceiling bridge through `φ`'s strict monotonicity).

## Honesty

The renumbering identity for the Galois theory of a **given** tower — **no reach toward
R1–R3**; nothing recovered from an abstract group. Prop. 15 and Prop. 14 are NOT claimed —
next passes. No new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


section MaxFromProfile

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [Normal K K']
variable (A : ValuationSubring L)

/-- The fiber index profile bounds the whole fiber: every lift of `σ̄` has index `≤ m`
(every fiber element is `s₁·dr h` — Pass 56's coset bijection — and the profile caps it). -/
theorem lowerIndex_le_of_profile {s₁ : A.decompositionSubgroup K} {m : ℕ}
    (hprof : ∀ h : A.decompositionSubgroup K',
      lowerIndex K A (s₁ * decompositionRestrict K K' A h)
        = min (lowerIndex K' A h) (m : ℕ∞))
    {s : A.decompositionSubgroup K}
    (hs : decompositionQuotient K K' A s
      = decompositionQuotient K K' A s₁) :
    lowerIndex K A s ≤ (m : ℕ∞) := by
  obtain ⟨h, hh⟩ := (decompositionFiberEquiv K K' A s₁).surjective ⟨s, hs⟩
  have hs' : s₁ * decompositionRestrict K K' A h = s := congrArg Subtype.val hh
  rw [← hs', hprof h]
  exact min_le_right _ _

/-- **The lift-membership characterization**: `σ̄` has a lift in `G_u` iff `u < j(σ̄)` —
one direction by the fiber bound, the other by the maximizer itself (Pass 51's Lemma 1 on
both). -/
theorem decompositionQuotient_mem_map_iff {s₁ : A.decompositionSubgroup K} {m : ℕ}
    (hm : (m : ℕ∞) = lowerIndex K A s₁)
    (hmax : ∀ s : A.decompositionSubgroup K,
      decompositionQuotient K K' A s
          = decompositionQuotient K K' A s₁
        → lowerIndex K A s ≤ (m : ℕ∞))
    (u : ℕ) :
    decompositionQuotient K K' A s₁
        ∈ (ramificationGroup K A u).map (decompositionQuotient K K' A)
      ↔ u < m := by
  constructor
  · rintro ⟨s, hsGu, hs⟩
    have h1 : (u : ℕ∞) < lowerIndex K A s :=
      (mem_ramificationGroup_iff_lt_lowerIndex K A).mp hsGu
    have h2 : (u : ℕ∞) < (m : ℕ∞) := lt_of_lt_of_le h1 (hmax s hs)
    exact_mod_cast h2
  · intro hu
    have h : s₁ ∈ ramificationGroup K A u := by
      rw [mem_ramificationGroup_iff_lt_lowerIndex, ← hm]
      exact_mod_cast hu
    exact Subgroup.mem_map.mpr ⟨s₁, h, rfl⟩

end MaxFromProfile

section CeilBridge

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [Finite (A.decompositionSubgroup K)]

/-- **The ceiling bridge**: given `a = φ(m−1) + 1` (a natural — Pass 72's integrality),
`⌈φ(u)⌉ < a ↔ u < m` — the strict monotonicity of `φ` (Pass 44) squeezed through
`Nat.ceil`. Degenerate `m = 0` rides on `φ(−1) = −1`. -/
theorem ceil_herbrandPhi_lt_iff {m a u : ℕ}
    (ha : (a : ℝ) = herbrandPhi K A ((m : ℝ) - 1) + 1) :
    ⌈herbrandPhi K A (u : ℝ)⌉₊ < a ↔ u < m := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have ha0 : (a : ℝ) = 0 := by
      rw [ha, herbrandPhi_eq_id K A (by norm_num)]
      norm_num
    have ha0' : a = 0 := by exact_mod_cast ha0
    subst ha0'
    simp
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    have hφn : herbrandPhi K A (n : ℝ) = (a : ℝ) - 1 := by
      rw [ha]
      push_cast
      ring_nf
    constructor
    · intro hlt
      by_contra hge
      push Not at hge
      have h1 : herbrandPhi K A ((n + 1 : ℕ) : ℝ)
          ≤ herbrandPhi K A (u : ℝ) := by
        apply (herbrandPhi_monotone K A)
        exact_mod_cast hge
      have h2 : herbrandPhi K A (n : ℝ)
          < herbrandPhi K A ((n + 1 : ℕ) : ℝ) := by
        apply herbrandPhi_strictMono K A
        push_cast
        linarith
      have h3 : ((a : ℕ) : ℝ) - 1 < herbrandPhi K A (u : ℝ) := by
        rw [← hφn]
        linarith
      have h4 : a - 1 < ⌈herbrandPhi K A (u : ℝ)⌉₊ := by
        rcases Nat.eq_zero_or_pos a with ha0 | hapos
        · subst ha0
          omega
        · rw [Nat.lt_ceil]
          push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hapos.ne')] at h3 ⊢
          exact h3
      omega
    · intro hu
      have h1 : herbrandPhi K A (u : ℝ)
          ≤ herbrandPhi K A (n : ℝ) := by
        apply herbrandPhi_monotone K A
        have : u ≤ n := by omega
        exact_mod_cast this
      have hapos : 1 ≤ a := by
        by_contra h0
        push Not at h0
        interval_cases a
        · -- a = 0: φ(n) = −1, but φ(n) ≥ 0 for n ≥ 0
          have h5 : (0 : ℝ) ≤ herbrandPhi K A (n : ℝ) := by
            rw [← herbrandPhi_zero K A]
            apply herbrandPhi_monotone K A
            exact_mod_cast Nat.zero_le n
          rw [hφn] at h5
          norm_num at h5
      have h2 : ⌈herbrandPhi K A (u : ℝ)⌉₊ ≤ a - 1 := by
        rw [Nat.ceil_le]
        rw [hφn] at h1
        push_cast [Nat.cast_sub hapos]
        exact h1
      omega

end CeilBridge

section LemmaFive

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Normal K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **SERRE IV §3 LEMMA 5**: `(G/H)_{φ_{L/K'}(u)} = G_u H/H` — in project terms, the image
of the `u`-th ramification group of `L/K` under the quotient restriction is the
`⌈φ_{L/K'}(u)⌉`-th ramification group of `K'/K`:

`(G_u).map (decompositionQuotient) = ramificationGroup K B ⌈φ_{L/K'}(u)⌉₊`.

Membership on both sides through Pass 51's Lemma 1, mediated by Pass 72's numerical
identity and the ceiling bridge; surjectivity (Pass 52) supplies the lift, and `σ̄ = 1` is
trivial. -/
theorem map_ramificationGroup_eq_ceil (u : ℕ) :
    (ramificationGroup K (extensionIntegers K L) u).map
        (decompositionQuotient K K' (extensionIntegers K L))
      = ramificationGroup K
          ((extensionIntegers K L).comap (algebraMap K' L))
          ⌈herbrandPhi K' (extensionIntegers K L) (u : ℝ)⌉₊ := by
  have := Fintype.ofFinite ((extensionIntegers K L).decompositionSubgroup K')
  ext τ
  -- surjectivity: σ̄ has a lift s₀
  obtain ⟨s₀, rfl⟩ := decompositionQuotient_extensionIntegers_surjective K K'
    (L := L) τ
  by_cases hσ : decompositionQuotient K K' (extensionIntegers K L) s₀ = 1
  · -- σ̄ = 1: in both sides
    rw [hσ]
    simp only [Subgroup.one_mem]
  · -- σ̄ ≠ 1: the numerical Lemma 5 (P72)
    obtain ⟨s₁, m, a, hfib, hm, hprof, ha, hφ⟩ :=
      exists_lowerIndex_eq_herbrandPhi K K' s₀ hσ
    have hmax : ∀ s : (extensionIntegers K L).decompositionSubgroup K,
        decompositionQuotient K K' (extensionIntegers K L) s
            = decompositionQuotient K K' (extensionIntegers K L) s₁
          → lowerIndex K (extensionIntegers K L) s ≤ (m : ℕ∞) :=
      fun s hs => lowerIndex_le_of_profile K K' (extensionIntegers K L) hprof hs
    constructor
    · intro hmem
      -- lift in G_u ⟹ u < m ⟹ ⌈φ(u)⌉ < a ⟹ σ̄ ∈ B-filtration
      rw [← hfib] at hmem
      have hu : u < m :=
        (decompositionQuotient_mem_map_iff K K' (extensionIntegers K L)
          hm hmax u).mp hmem
      have hlt : ⌈herbrandPhi K' (extensionIntegers K L) (u : ℝ)⌉₊
          < a :=
        (ceil_herbrandPhi_lt_iff K' (extensionIntegers K L) hφ).mpr hu
      rw [mem_ramificationGroup_iff_lt_lowerIndex, ← ha]
      exact_mod_cast hlt
    · intro hmem
      rw [mem_ramificationGroup_iff_lt_lowerIndex, ← ha] at hmem
      have hlt : ⌈herbrandPhi K' (extensionIntegers K L) (u : ℝ)⌉₊
          < a := by exact_mod_cast hmem
      have hu : u < m :=
        (ceil_herbrandPhi_lt_iff K' (extensionIntegers K L) hφ).mp hlt
      rw [← hfib]
      exact (decompositionQuotient_mem_map_iff K K' (extensionIntegers K L)
        hm hmax u).mpr hu

end LemmaFive


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms lowerIndex_le_of_profile
#print axioms decompositionQuotient_mem_map_iff
#print axioms ceil_herbrandPhi_lt_iff
#print axioms map_ramificationGroup_eq_ceil

end Anabelian
