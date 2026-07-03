/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionGeneratorRep
import Anabelian.SubextensionCharPoly
import Mathlib

/-!
# Prop. 3 direction (ii): the remainder-vanishing brick (Pass 61)

The monic-division argument of Serre IV §1 Prop. 3 (ii) divides `g − C y` by Serre's monic
`F` over `B = 𝒪_L ∩ K'` and must kill the remainder. This pass is that killing — the last
genuinely new mathematics before Prop. 3:

> **a polynomial over `B` of degree `< |Gal(L/K')|` whose `ι`-image vanishes at `x` is zero**
> (`eq_zero_of_map_comapRingHom_eval_eq_zero`).

The degree count: over `K'`, the polynomial still kills `x` (move the coefficients along
`B ⊆ K'` — the two evaluation routes `B → 𝒪_L → L` and `B → K' → L` agree); the minimal
polynomial of `x` over `K'` has degree `[K'(x) : K'] = [L : K']` (Pass 60's `L = K'(x)`)
`= |Gal(L/K')| = |D_{K'}(𝒪_L)|` (Galois + Pass 55's `D = ⊤`); minimality
(`minpoly.degree_le_of_ne_zero`) forbids a smaller-degree nonzero annihilator.

With this, direction (ii) is pure gluing: divide, kill the remainder by this brick (`F` is
monic of degree exactly `|H|` — Pass 55), transport the division identity along `σ̄`, and
evaluate at `x`.

## Honesty

A degree bound for a tower of given fields — **no reach toward R1–R3**; nothing recovered
from an abstract group. Neither the division nor `b ∣ a` is claimed. No new
`structure`/`class`; no owed witness; D1 N/A; D2 stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Polynomial IntermediateField
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [FiniteDimensional K' L] [IsGalois K' L]
variable [Fintype ((extensionIntegers K L).decompositionSubgroup K')]

/-- **The remainder-vanishing brick** (Serre IV §1, inside the proof of Prop. 3): a
polynomial over `B = 𝒪_L ∩ K'` of degree `< |D_{K'}(𝒪_L)| = [L : K']` whose `ι`-image kills
the generator `x` is zero. Over `K'` it would be a nonzero annihilator of `x` of degree below
`deg (minpoly K' x) = [K'(x) : K'] = [L : K']` (Pass 60's `L = K'(x)` + Galois cardinality +
Pass 55's `D_{K'}(𝒪_L) = ⊤`) — impossible by minimality. -/
theorem eq_zero_of_map_comapRingHom_eval_eq_zero
    {x : ↥(extensionIntegers K L)}
    (hgen : Subring.closure
      (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}) = ⊤)
    {r : Polynomial ↥((extensionIntegers K L).comap (algebraMap K' L))}
    (hr : (r.map (comapRingHom K' (extensionIntegers K L))).eval x = 0)
    (hdeg : r.natDegree
      < Fintype.card ((extensionIntegers K L).decompositionSubgroup K')) :
    r = 0 := by
  by_contra hr0
  -- the coefficients move to K'[X], where the polynomial still kills x
  have hrK0 : r.map ((extensionIntegers K L).comap (algebraMap K' L)).subtype ≠ 0 := by
    intro h
    exact hr0 (Polynomial.map_injective _ Subtype.coe_injective
      (by rw [h, Polynomial.map_zero]))
  have haev : Polynomial.aeval (x : L)
      (r.map ((extensionIntegers K L).comap (algebraMap K' L)).subtype) = 0 := by
    have h1 : ((extensionIntegers K L).subtype)
        ((r.map (comapRingHom K' (extensionIntegers K L))).eval x) = 0 := by
      rw [hr]; exact map_zero _
    rw [Polynomial.eval_map, Polynomial.hom_eval₂] at h1
    have hcomp : (algebraMap K' L).comp
        ((extensionIntegers K L).comap (algebraMap K' L)).subtype
        = ((extensionIntegers K L).subtype).comp
            (comapRingHom K' (extensionIntegers K L)) :=
      RingHom.ext fun b => rfl
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
    exact h1
  -- the degree count: deg (minpoly K' x) = [L : K'] = |D_{K'}(𝒪_L)|
  have hxint : IsIntegral K' (x : L) := IsIntegral.of_finite K' _
  have h2 : Module.finrank K' K'⟮(x : L)⟯ = (minpoly K' (x : L)).natDegree :=
    IntermediateField.adjoin.finrank hxint
  have h3 : IntermediateField.adjoin K' {(x : L)} = ⊤ :=
    adjoin_generator_eq_top K K' hgen
  rw [h3, IntermediateField.finrank_top'] at h2
  have h4 : Nat.card (L ≃ₐ[K'] L) = Module.finrank K' L :=
    IsGalois.card_aut_eq_finrank K' L
  have h5 : (extensionIntegers K L).decompositionSubgroup K' = ⊤ :=
    decompositionSubgroup_extensionIntegers_restrict_eq_top K K'
  have h6 : Nat.card ↥((extensionIntegers K L).decompositionSubgroup K')
      = Nat.card (L ≃ₐ[K'] L) := by
    rw [h5]
    exact Subgroup.card_top
  have h7 : Fintype.card ((extensionIntegers K L).decompositionSubgroup K')
      = (minpoly K' (x : L)).natDegree := by
    rw [← Nat.card_eq_fintype_card, h6, h4, ← h2]
  -- minimality forbids the small annihilator
  have hle := minpoly.degree_le_of_ne_zero K' (x : L) hrK0 haev
  have hle2 : (minpoly K' (x : L)).natDegree
      ≤ (r.map ((extensionIntegers K L).comap (algebraMap K' L)).subtype).natDegree :=
    Polynomial.natDegree_le_natDegree hle
  have hrKdeg : (r.map ((extensionIntegers K L).comap
      (algebraMap K' L)).subtype).natDegree = r.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Subtype.coe_injective r
  omega

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms eq_zero_of_map_comapRingHom_eval_eq_zero

end Anabelian
