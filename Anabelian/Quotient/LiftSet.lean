/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.Basic
import Anabelian.Quotient.CharPoly
import Mathlib

/-!
# Toward Serre IV §1 Prop. 3: the lift-set identity (Pass 56)

Prop. 3 compares `σ̄y − y` with the product `∏_{s ↦ σ̄} (s·x − x)` **over the lifts of `σ̄`**.
This pass supplies the two facts that make that product computable:

1. **The fiber is a coset, explicitly**: for any `s₀` in the fiber of `σ̄` under
   `decompositionQuotient`, the map `h ↦ s₀ · (decompositionRestrict h)` is a **bijection**
   from `Gal(L/K')`'s decomposition group onto the fiber (`decompositionFiberEquiv`) — Pass
   50's exactness (`ker = range`) gives surjectivity onto the fiber, Pass 46's injectivity
   gives injectivity. So "`∑`/`∏` over the lifts of `σ̄`" *is* "`∑`/`∏` over `H`,
   reparametrized" — the form every Prop.-3 computation uses.
2. **The lift-set identity** (the headline): transporting Serre's polynomial (Pass 55) along
   `s₀`'s ring action gives exactly the fiber product —
   `(∏_{h ∈ H} (X − h·x)).map s₀ = ∏_{h ∈ H} (X − (s₀ · dr h)·x)`, and evaluated at `x`:
   `∏_{h} (x − (s₀ · dr h)·x)` — which by (1) is `± ∏_{s ↦ σ̄} (s·x − x)`. Combined with
   Pass 55's descent (`f = F.map (comapRingHom)`, `F` over `𝒪_L ∩ K'`), direction (i) of
   Prop. 3 reduces to coefficient-telescoping on `σ̄F − F` — the next brick.

The per-factor identity `s₀ • (h • x) = (s₀ * decompositionRestrict h) • x` is
**definitional** (Pass 46's action agreement is `rfl`), which is why the headline proof is
four lines: the entire content is the bookkeeping already built in Passes 46/50/55.

## What is proved (all axiom-free)

* `map_fullProdXSubSMul` — the headline identity above; `map_fullProdXSubSMul_eval` — its
  value at `x` (the Prop.-3 product, `H`-parametrized).
* `decompositionQuotient_decompositionRestrict` (`= 1`, pointwise form of Pass 50's composite
  triviality) and `decompositionQuotient_mul_decompositionRestrict` (`s₀ · dr h` stays in the
  fiber).
* **`decompositionFiberEquiv`** — `H ≃ {s // decompositionQuotient s = decompositionQuotient
  s₀}`, by `Equiv.ofBijective`; `decompositionFiberEquiv_apply_coe` (`rfl`) records the
  underlying map, so products/sums transport along it by `Equiv.prod_comp`-style reindexing.

## Honesty

Bookkeeping for a tower of given fields — **no reach toward R1–R3**; nothing recovered from an
abstract group. No divisibility of Prop. 3 is proved here: this is the reindexing layer that
the telescoping (direction (i)) and the division argument (direction (ii)) will consume. No
new `structure`/`class` (`decompositionFiberEquiv` is a `def` of an `Equiv`); no owed witness;
D1 N/A; D2 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Polynomial
open scoped Pointwise

namespace Anabelian

section MapIdentity

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable (A : ValuationSubring L)
variable [Fintype (A.decompositionSubgroup K')]

/-- **The lift-set identity**: transporting Serre's polynomial `∏_{h ∈ H} (X − h·x)` (Pass 55)
along the ring action of `s₀ ∈ D(A)` yields the product over the coset `s₀ · H` —
`∏_{h} (X − (s₀ · decompositionRestrict h)·x)`. The per-factor step is definitional (Pass 46's
action agreement); the rest is `map` distributing over the product. -/
theorem map_fullProdXSubSMul (s₀ : A.decompositionSubgroup K) (x : ↥A) :
    (fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x).map
        ((MulSemiringAction.toRingAut (A.decompositionSubgroup K) (↥A) s₀ :
          ↥A ≃+* ↥A) : ↥A →+* ↥A)
      = ∏ h : A.decompositionSubgroup K',
          (Polynomial.X - Polynomial.C ((s₀ * decompositionRestrict K K' A h) • x)) := by
  rw [fullProdXSubSMul, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun h _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 1

/-- The lift-set identity evaluated at `x`: the transported polynomial takes the value
`∏_{h} (x − (s₀ · dr h)·x)` — up to sign, Prop. 3's product `∏_{s ↦ σ̄} (s·x − x)` in its
`H`-parametrized form. -/
theorem map_fullProdXSubSMul_eval (s₀ : A.decompositionSubgroup K) (x : ↥A) :
    ((fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x).map
        ((MulSemiringAction.toRingAut (A.decompositionSubgroup K) (↥A) s₀ :
          ↥A ≃+* ↥A) : ↥A →+* ↥A)).eval x
      = ∏ h : A.decompositionSubgroup K',
          (x - (s₀ * decompositionRestrict K K' A h) • x) := by
  rw [map_fullProdXSubSMul K K' A s₀ x, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun h _ => ?_
  simp

end MapIdentity

section Fiber

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [Normal K K']
variable (A : ValuationSubring L)

/-- Pointwise form of Pass 50's composite triviality: elements of `Gal(L/K')`'s decomposition
group restrict to the identity of `K'`. -/
theorem decompositionQuotient_decompositionRestrict (h : A.decompositionSubgroup K') :
    decompositionQuotient K K' A (decompositionRestrict K K' A h) = 1 := by
  have h1 := DFunLike.congr_fun (decompositionQuotient_comp_decompositionRestrict K K' A) h
  simpa using h1

/-- Multiplying by an `H`-element does not move the fiber: `s₀ · dr h` lifts the same `σ̄`. -/
theorem decompositionQuotient_mul_decompositionRestrict
    (s₀ : A.decompositionSubgroup K) (h : A.decompositionSubgroup K') :
    decompositionQuotient K K' A (s₀ * decompositionRestrict K K' A h)
      = decompositionQuotient K K' A s₀ := by
  rw [map_mul, decompositionQuotient_decompositionRestrict, mul_one]

/-- **The fiber of `decompositionQuotient` is a coset of `H`, explicitly**: for any `s₀`, the
map `h ↦ s₀ · decompositionRestrict h` is a bijection from `Gal(L/K')`'s decomposition group
onto `{s | decompositionQuotient s = decompositionQuotient s₀}`. Injectivity is Pass 46
(`decompositionRestrict_injective`); surjectivity is Pass 50's exactness (`ker = range`).
Sums and products over the lifts of `σ̄` transport along this to sums and products over `H`. -/
noncomputable def decompositionFiberEquiv (s₀ : A.decompositionSubgroup K) :
    A.decompositionSubgroup K' ≃
      {s : A.decompositionSubgroup K //
        decompositionQuotient K K' A s = decompositionQuotient K K' A s₀} := by
  refine Equiv.ofBijective
    (fun h => ⟨s₀ * decompositionRestrict K K' A h,
      decompositionQuotient_mul_decompositionRestrict K K' A s₀ h⟩) ⟨?_, ?_⟩
  · intro h₁ h₂ hh
    have h2 : s₀ * decompositionRestrict K K' A h₁ = s₀ * decompositionRestrict K K' A h₂ :=
      congrArg Subtype.val hh
    exact decompositionRestrict_injective K K' A (mul_left_cancel h2)
  · rintro ⟨s, hs⟩
    have h3 : s₀⁻¹ * s ∈ (decompositionQuotient K K' A).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, inv_mul_cancel]
    rw [decompositionQuotient_ker] at h3
    obtain ⟨h, hh⟩ := h3
    refine ⟨h, ?_⟩
    apply Subtype.ext
    change s₀ * decompositionRestrict K K' A h = s
    rw [hh]
    exact mul_inv_cancel_left s₀ s

/-- The underlying map of `decompositionFiberEquiv`, by `rfl` — the hook for
`Equiv.prod_comp`-style transport of products and sums over the lift set. -/
theorem decompositionFiberEquiv_apply_coe (s₀ : A.decompositionSubgroup K)
    (h : A.decompositionSubgroup K') :
    ((decompositionFiberEquiv K K' A s₀) h).1 = s₀ * decompositionRestrict K K' A h := rfl

end Fiber

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms map_fullProdXSubSMul
#print axioms map_fullProdXSubSMul_eval
#print axioms decompositionQuotient_decompositionRestrict
#print axioms decompositionQuotient_mul_decompositionRestrict
#print axioms decompositionFiberEquiv
#print axioms decompositionFiberEquiv_apply_coe

end Anabelian
