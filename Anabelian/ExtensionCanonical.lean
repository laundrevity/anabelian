/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib
import Anabelian.ExtensionLocalFieldInstance
import Anabelian.ExtensionMonogenic
import Anabelian.ValuativeRelCongr

/-!
# The canonicity obligation: base-independence of `extensionValuativeRel` across towers (Pass 43)

The obligation deferred since Pass 38, gating the iteration of the theory up towers `M/L/K` and
hence the ascent (Herbrand `φ`/`ψ`, upper numbering — Serre IV §3). `extensionValuativeRel K L`
is a `def`, not an instance, precisely *because* for a tower `K ⊆ K' ⊆ L` the valuative relation
on `L` built from the base `K` must be proved equal to the one built from the intermediate base
`K'`. This file discharges that:

> **`extensionValuativeRel_base_independent`** — for a tower `K ⊆ K' ⊆ L` of finite separable
> extensions, `extensionValuativeRel K L = extensionValuativeRel K' L` (`K'` carrying the
> extension local-field structure of Pass 41).

The mathematical content is **integral-closure transitivity**: `𝒪_L` is the integral closure of
`𝒪[K]` in `L`, and equally the integral closure of `𝒪[K']` in `L`, because `𝒪[K']` is itself the
integral closure of `𝒪[K]` in `K'` (the assembly's self-consistency). The pieces:

* **`integer_extensionValuativeRel_eq`** — *self-consistency*: under `extensionValuativeRel K K'`,
  the integer ring `𝒪[K']` is exactly `extensionIntegers K K'`. Pure `Compatible` bookkeeping
  (the `K'`-analogue of Pass 39's `valued_integer_extensionValuativeRel`, on the canonical
  valuation, no `Valued`/uniformity).
* **`isIntegral_base_iff`** — *transitivity*: for `x : L`, integrality over `𝒪[K]` is equivalent
  to integrality over `𝒪[K']` (`IsIntegral.tower_top` one way; `isIntegral_trans` the other, since
  `𝒪[K']` is integral over `𝒪[K]`).
* **`extensionIntegers_base_independent`** — the two valuation subrings of `L` coincide.
* **`extensionValuativeRel_base_independent`** — hence the relations coincide (`congrArg` of
  `ofValuation ∘ ·.valuation`).

## Honesty

Nothing here recovers anything from an abstract group; this is a structural fact *about* the
tower's valuation theory, strictly below R1. No new `structure`/`class`; no owed witness; D1 N/A;
D2 untouched (no spectral structure enters any statement — integrality is the native
characterisation, `mem_extensionIntegers_iff` is `Iff.rfl`). With this discharged,
`extensionValuativeRel` could be promoted to an instance; we keep it a `def` (the upstream
diamond-avoidance design) and expose the equality as a theorem, exactly as Mathlib does for its
own local valuative structures.

## Axiom status

Intended: standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`,
unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable (L : Type*) [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
  [FiniteDimensional K' L]

/-- **Self-consistency of the assembly**: under the extension valuative structure on `K'`, its
integer ring `𝒪[K']` is exactly `extensionIntegers K K'` (the integral closure of `𝒪[K]` in `K'`).
Pure `Compatible` bookkeeping on the canonical valuation — the `K'`-analogue of Pass 39's
`valued_integer_eq_of_compatible`, here without invoking the `Valued`/uniformity layer. -/
theorem integer_extensionValuativeRel_eq :
    letI := extensionValuativeRel K K'
    (𝒪[K'] : Subring K') = (extensionIntegers K K').toSubring := by
  letI := extensionValuativeRel K K'
  haveI hcomp : (extensionIntegers K K').valuation.Compatible :=
    Valuation.Compatible.ofValuation (extensionIntegers K K').valuation
  have key : ∀ x : K', valuation K' x ≤ valuation K' 1 ↔
      (extensionIntegers K K').valuation x ≤ (extensionIntegers K K').valuation 1 := fun x =>
    (Valuation.Compatible.vle_iff_le (v := valuation K') x 1).symm.trans
      (Valuation.Compatible.vle_iff_le (v := (extensionIntegers K K').valuation) x 1)
  ext x
  rw [Valuation.mem_integer_iff]
  constructor
  · intro hx
    have h2 := (key x).mp (by rwa [map_one])
    rw [map_one] at h2
    exact (extensionIntegers K K').mem_of_valuation_le_one x h2
  · intro hx
    have h2 : (extensionIntegers K K').valuation x ≤ (extensionIntegers K K').valuation 1 := by
      rw [map_one]
      exact (extensionIntegers K K').valuation_le_one ⟨x, hx⟩
    have h3 := (key x).mpr h2
    rwa [map_one] at h3

omit [FiniteDimensional K' L] in
/-- **Transitivity (the engine)**: for `x : L`, integrality over `𝒪[K]` is equivalent to
integrality over the intermediate integers `extensionIntegers K K'`. Forward by enlarging the base
ring (`IsIntegral.tower_top`); backward because `extensionIntegers K K' = integralClosure 𝒪[K] K'`
is integral over `𝒪[K]` (`isIntegral_trans`). The base ring `↥(extensionIntegers K K')` acts on `L`
through `K'` via Mathlib's ambient subring-algebra instance; the scalar tower over `𝒪[K]` is the
`extensionAlgebraMap` factorisation. -/
theorem isIntegral_base_iff (x : L) :
    IsIntegral ↥𝒪[K] x ↔ IsIntegral ↥(extensionIntegers K K') x := by
  -- `↑(algebraMap 𝒪[K] → 𝒪_{K'}, of r) = algebraMap K K' ↑r` (the `extensionAlgebraMap` coercion).
  have hcoe : ∀ r : ↥𝒪[K],
      ((algebraMap ↥𝒪[K] ↥(extensionIntegers K K') r : ↥(extensionIntegers K K')) : K')
        = algebraMap K K' (r : K) := fun r => by
    change ((extensionAlgebraMap K K' r : ↥(extensionIntegers K K')) : K') = _
    rw [coe_extensionAlgebraMap]
  -- the tower `𝒪[K] → 𝒪_{K'} → K'` (needed to reflect integrality through the subring inclusion).
  haveI sclK' : IsScalarTower ↥𝒪[K] ↥(extensionIntegers K K') K' := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have lhs : algebraMap ↥𝒪[K] K' r = algebraMap K K' (r : K) := rfl
    have rhs : algebraMap ↥(extensionIntegers K K') K'
        (algebraMap ↥𝒪[K] ↥(extensionIntegers K K') r) = algebraMap K K' (r : K) := by
      change ((algebraMap ↥𝒪[K] ↥(extensionIntegers K K') r : ↥(extensionIntegers K K')) : K') = _
      rw [hcoe r]
    rw [lhs, rhs]
  -- the tower `𝒪[K] → 𝒪_{K'} → L` agrees with the ambient `𝒪[K] → L` (factoring through `K'`).
  haveI tower : IsScalarTower ↥𝒪[K] ↥(extensionIntegers K K') L := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have lhs : algebraMap ↥𝒪[K] L r = algebraMap K L (r : K) := rfl
    have rhs : algebraMap ↥(extensionIntegers K K') L
        (algebraMap ↥𝒪[K] ↥(extensionIntegers K K') r) = algebraMap K L (r : K) := by
      change algebraMap K' L
          ((algebraMap ↥𝒪[K] ↥(extensionIntegers K K') r : ↥(extensionIntegers K K')) : K') = _
      rw [hcoe r, ← IsScalarTower.algebraMap_apply K K' L (r : K)]
    rw [lhs, rhs]
  -- `𝒪_{K'}` is integral over `𝒪[K]` (it is the integral closure of `𝒪[K]` in `K'`).
  haveI hint : Algebra.IsIntegral ↥𝒪[K] ↥(extensionIntegers K K') := by
    refine ⟨fun b => ?_⟩
    have hb : IsIntegral ↥𝒪[K] (algebraMap ↥(extensionIntegers K K') K' b) :=
      (mem_extensionIntegers_iff K K' (b : K')).mp b.2
    exact (isIntegral_algebraMap_iff Subtype.coe_injective).mp hb
  exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans x hx⟩

/-- **Base-independence of `𝒪_L`**: the valuation subring `𝒪_L` is the same whether built over the
base `K` or over the intermediate field `K'` (carrying the extension structure). -/
theorem extensionIntegers_base_independent [Algebra.IsSeparable K K'] :
    letI := extensionValuativeRel K K'
    letI := ValuativeRel.topologicalSpace K'
    haveI := isNonarchimedeanLocalField_extension K K'
    haveI : FiniteDimensional K L := Module.Finite.trans K' L
    extensionIntegers K L = extensionIntegers K' L := by
  letI := extensionValuativeRel K K'
  letI := ValuativeRel.topologicalSpace K'
  haveI := isNonarchimedeanLocalField_extension K K'
  haveI : FiniteDimensional K L := Module.Finite.trans K' L
  -- self-consistency packaged as a ring iso of the two intermediate bases.
  have hSC : (𝒪[K'] : Subring K') = (extensionIntegers K K').toSubring :=
    integer_extensionValuativeRel_eq K K'
  refine SetLike.ext (fun x => ?_)
  rw [mem_extensionIntegers_iff K L x, mem_extensionIntegers_iff K' L x]
  rw [isIntegral_base_iff K K' L x]
  -- bridge `IsIntegral (extensionIntegers K K') x ↔ IsIntegral 𝒪[K'] x` along `hSC`.
  exact (RingEquiv.isIntegral_iff (RingEquiv.subringCongr hSC.symm)
    (by ext b; rfl) x)

/-- **THE CANONICITY THEOREM**: for a tower `K ⊆ K' ⊆ L` of finite separable extensions, the
valuative relation on `L` is the same whether constructed from the base `K` or from the
intermediate field `K'`. This discharges the canonicity obligation deferred since Pass 38 and
makes intermediate fields usable as base fields — the prerequisite for the ascent (Herbrand,
upper numbering). -/
theorem extensionValuativeRel_base_independent [Algebra.IsSeparable K K'] :
    letI := extensionValuativeRel K K'
    letI := ValuativeRel.topologicalSpace K'
    haveI := isNonarchimedeanLocalField_extension K K'
    haveI : FiniteDimensional K L := Module.Finite.trans K' L
    extensionValuativeRel K L = extensionValuativeRel K' L := by
  letI := extensionValuativeRel K K'
  letI := ValuativeRel.topologicalSpace K'
  haveI := isNonarchimedeanLocalField_extension K K'
  haveI : FiniteDimensional K L := Module.Finite.trans K' L
  exact congrArg (fun A : ValuationSubring L => ValuativeRel.ofValuation A.valuation)
    (extensionIntegers_base_independent K K' L)

-- Reproducible axiom audit (re-runs on every `lake build`). Intended standard-axioms-only.
#print axioms integer_extensionValuativeRel_eq
#print axioms isIntegral_base_iff
#print axioms extensionIntegers_base_independent
#print axioms extensionValuativeRel_base_independent

end Anabelian
