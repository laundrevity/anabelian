/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.LemmaFive
import Mathlib

/-!
# The card multiplicativity `|G_u| = |(G/H)_{⌈φ(u)⌉}| · |H_u|` (Pass 74)

The arithmetic heart of **Prop. 15** (`φ`-transitivity, Serre IV §3). For the tower
`K ⊆ K' ⊆ L` and every `u : ℕ`:

> **`Nat.card (G_u) = Nat.card ((G/H)_{⌈φ_{L/K'}(u)⌉}) * Nat.card (H_u)`**
> (`card_ramificationGroup_eq_mul`)

Three ingredients, one generic count. The generic count (`card_subgroup_eq_card_map_mul`):
for any hom `f` and subgroup `S`, `|S| = |S.map f| · |ker f ⊓ S|` — Lagrange on `f|_S` +
the first isomorphism theorem. Applied to `dq|_{G_u}`: the **image** is the `B`-filtration
at `⌈φ_{L/K'}(u)⌉` — **Lemma 5** (Pass 73); the **kernel** is `range dr ⊓ G_u` (Pass 50's
`ker dq = range dr`) `= (H_u).map dr` (Pass 46's compatibility `H_u = H ∩ G_u`), of card
`|H_u|` (Pass 46's injectivity).

Why this is the heart of Prop. 15: `φ_{L/K}'(u) = 1/(G_0 : G_u)` (Pass 47), and by this
multiplicativity `(G_0 : G_u) = ((G/H)_0 : (G/H)_{⌈φ(u)⌉}) · (H_0 : H_u)` — exactly the
chain-rule slope of `φ_{K'/K} ∘ φ_{L/K'}` at `u`. The analytic gluing (two piecewise-linear
functions with equal value at `0` and equal slopes agree) is the next pass; the counting is
now done.

## Honesty

Counting for a given tower — **no reach toward R1–R3**. Prop. 15 itself (the equality of
functions `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}`) is NOT claimed — the analytic gluing remains.
No new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


/-- Generic counting: `|S| = |S.map f| · |ker f ⊓ S|` — Lagrange on the restriction
`f|_S` plus the first isomorphism theorem. -/
theorem card_subgroup_eq_card_map_mul {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (S : Subgroup G) :
    Nat.card S = Nat.card (S.map f) * Nat.card (f.ker ⊓ S : Subgroup G) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.restrict S).ker
  rw [h1]
  congr 1
  · rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (f.restrict S)).toEquiv,
        MonoidHom.restrict_range]
  · rw [MonoidHom.ker_restrict, ← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]

section Multiplicativity

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Normal K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **THE CARD MULTIPLICATIVITY** (the arithmetic heart of Prop. 15): for every `u : ℕ`,

`|G_u| = |(G/H)_{⌈φ_{L/K'}(u)⌉}| · |H_u|`

— the generic counting on `dq|_{G_u}`, with the image identified by **Lemma 5** (Pass 73),
the kernel by `ker dq = range dr` (Pass 50) and `H_u = H ∩ G_u` (Pass 46), and the kernel's
card by `dr`'s injectivity (Pass 46). Dividing the `u`-instance by the `0`-instance gives
the index-multiplicativity `(G_0 : G_u) = ((G/H)_0 : (G/H)_{⌈φ(u)⌉}) · (H_0 : H_u)` — the
slope identity `φ_{L/K}' = (φ_{K'/K} ∘ φ_{L/K'})'` in card form. -/
theorem card_ramificationGroup_eq_mul (u : ℕ) :
    Nat.card (ramificationGroup K (extensionIntegers K L) u)
      = Nat.card (ramificationGroup K
            ((extensionIntegers K L).comap (algebraMap K' L))
            ⌈herbrandPhi K' (extensionIntegers K L) (u : ℝ)⌉₊)
        * Nat.card (ramificationGroup K' (extensionIntegers K L) u) := by
  rw [card_subgroup_eq_card_map_mul
    (decompositionQuotient K K' (extensionIntegers K L))
    (ramificationGroup K (extensionIntegers K L) u)]
  congr 1
  · rw [map_ramificationGroup_eq_ceil K K' u]
  · rw [decompositionQuotient_ker, ← ramificationGroup_map_eq,
        Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (decompositionRestrict_injective K K'
            (extensionIntegers K L))).toEquiv.symm]

/-- The `u = 0` base of the multiplicativity: `|G_0| = |(G/H)_0| · |H_0|` — Serre's
`e_{L/K} = e_{K'/K} · e_{L/K'}` at the inertia level (via `⌈φ(0)⌉ = 0`). -/
theorem card_ramificationGroup_zero_eq_mul :
    Nat.card (ramificationGroup K (extensionIntegers K L) 0)
      = Nat.card (ramificationGroup K
            ((extensionIntegers K L).comap (algebraMap K' L)) 0)
        * Nat.card (ramificationGroup K' (extensionIntegers K L) 0) := by
  have h := card_ramificationGroup_eq_mul K K' (L := L) 0
  rwa [show ⌈herbrandPhi K' (extensionIntegers K L) ((0 : ℕ) : ℝ)⌉₊
      = 0 from by
    rw [Nat.cast_zero, herbrandPhi_zero]
    simp] at h

end Multiplicativity


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms card_subgroup_eq_card_map_mul
#print axioms card_ramificationGroup_eq_mul
#print axioms card_ramificationGroup_zero_eq_mul

end Anabelian
