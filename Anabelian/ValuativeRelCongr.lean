/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Congruence lemmas for valuative relations and group uniformities (Pass 40, abstract half)

Three reusable, project-agnostic lemmas powering the spectral seam of the assembly:

* **`ofValuation_congr`** — equivalent valuations induce **equal** valuative relations (the
  class is `@[ext]`; equivalence is exactly the pointwise `vle`-iff). Topology identifications
  downstream become honest `rw`s, never homeomorphism arguments.
* **`ofValuation_eq_of_same_subring`** — a valuation with the same unit ball as a valuation
  subring induces the same relation as the subring's valuation
  (`Valuation.isEquiv_iff_val_le_one` + `valuation_le_one_iff`).
* **`uniformSpace_eq_of_isUniformAddGroup`** — an additive-commutative group carries at most
  one group uniformity per topology (`uniformity_eq_comap_nhds_zero` on both sides): the
  bridge that lets `CompleteSpace` transfer along topology equalities.

## Honesty

Abstract bricks only; nothing about local fields or `L` is claimed here. No new
`structure`/`class`; no owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract
group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open ValuativeRel

/-- **Equivalent valuations induce equal valuative relations**: `IsEquiv` is precisely the
pointwise `vle`-iff, and the relation class is extensional. -/
theorem ofValuation_congr {F : Type*} [Field F] {Γ Γ' : Type*}
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Γ']
    (v : Valuation F Γ) (w : Valuation F Γ') (h : v.IsEquiv w) :
    ValuativeRel.ofValuation v = ValuativeRel.ofValuation w := by
  ext x y
  exact h x y

/-- **Same unit ball, same relation**: a valuation whose unit ball is a given valuation
subring induces the same valuative relation as the subring's own valuation. -/
theorem ofValuation_eq_of_same_subring {F : Type*} [Field F] (A : ValuationSubring F)
    {Γ' : Type*} [LinearOrderedCommGroupWithZero Γ'] (w : Valuation F Γ')
    (h : ∀ x, w x ≤ 1 ↔ x ∈ A) :
    ValuativeRel.ofValuation A.valuation = ValuativeRel.ofValuation w :=
  ofValuation_congr _ _ (Valuation.isEquiv_iff_val_le_one.mpr
    (fun {x} => (A.valuation_le_one_iff x).trans (h x).symm))

/-- **At most one group uniformity per topology** on an additive commutative group: any two
uniformities making it a uniform additive group and inducing the same topology are equal. -/
theorem uniformSpace_eq_of_isUniformAddGroup {G : Type*} [AddCommGroup G]
    (u₁ u₂ : UniformSpace G) (h : u₁.toTopologicalSpace = u₂.toTopologicalSpace)
    (hg₁ : @IsUniformAddGroup G u₁ _) (hg₂ : @IsUniformAddGroup G u₂ _) : u₁ = u₂ := by
  haveI hr₁ : @IsRightUniformAddGroup G u₁ _ :=
    @IsUniformAddGroup.isRightUniformAddGroup G u₁ _ hg₁
  haveI hr₂ : @IsRightUniformAddGroup G u₂ _ :=
    @IsUniformAddGroup.isRightUniformAddGroup G u₂ _ hg₂
  refine UniformSpace.ext ?_
  rw [@uniformity_eq_comap_nhds_zero G u₁ _ hr₁, @uniformity_eq_comap_nhds_zero G u₂ _ hr₂]
  exact congrArg (fun t => Filter.comap (fun p : G × G => p.2 - p.1) (@nhds G t 0)) h

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms ofValuation_congr
#print axioms ofValuation_eq_of_same_subring
#print axioms uniformSpace_eq_of_isUniformAddGroup

end Anabelian
