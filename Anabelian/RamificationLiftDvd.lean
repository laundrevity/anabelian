/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.RamificationLiftSet
import Anabelian.ExtensionComapIntegers
import Mathlib

/-!
# Serre IV §1 Prop. 3, direction (i): `a ∣ b` (Pass 58)

The first of Prop. 3's two divisibilities is now a theorem: for `σ̄` in the subextension's
decomposition group and any lift `s₀`,

> **`ι(σ̄y − y)` divides `∏_{s ↦ σ̄} (x − s·x)` in `𝒪_L`**

(`y` the generator of `B = 𝒪_L ∩ K'` over `𝒪_K`, `ι : B →+* 𝒪_L`, the product over the
lifts in its `H`-parametrized form). Serre's argument, in the project's bricks: every
coefficient of `σ̄F − F` is divisible by `a = σ̄y − y` (Pass 57's telescoping); pushing along
`ι` and evaluating at `x`, the value is `(σ̄f)(x) − f(x) = (σ̄f)(x)` (Pass 55: `f(x) = 0`)
`= ∏_{s ↦ σ̄} (x − s·x)` (Pass 56's lift-set identity). The glue supplied here:

* **the equivariance** `ι(σ̄ • c) = s₀ • ι(c)` — Pass 50's action-compatibility
  (`algebraMap_decompositionQuotient_smul`), packaged at the `comapRingHom` level and lifted
  to polynomials: `(σ̄ • F).map ι = (F.map ι).map s₀` — the coefficient-wise `D(B)`-action
  downstairs maps to the `s₀`-transport upstairs;
* the generic **`dvd_eval_of_dvd_coeff`** — an element dividing every coefficient divides
  every evaluation.

## What is proved (all axiom-free)

* `dvd_eval_of_dvd_coeff` — generic (any `CommRing`).
* `comapRingHom_decompositionQuotient_smul` — the equivariance, element level;
  `map_comapRingHom_smul` — the equivariance, polynomial level.
* **`comapRingHom_smul_sub_dvd_liftProd`** — the abstract headline: given Pass 55's descent
  (`hF`) and Pass 57's telescoping (`hdvd`), `ι(σ̄y − y) ∣ ∏_h (x − (s₀ · dr h)·x)`.
* **`exists_generator_dvd_liftProd`** — the `𝒪_L` form, hypothesis-free: one `y ∈ B` with
  **`i_{K'/K}(σ̄) = addVal_B(σ̄y − y)`** for every `σ̄` (Pass 57) **and** the divisibility
  above for **every** `x` and every lift `s₀`. Direction (i), assembled.

## Honesty

Structure of a tower of given fields — **no reach toward R1–R3**; nothing recovered from an
abstract group. This is one direction of Prop. 3's comparison: `a ∣ b`. The converse `b ∣ a`
(the monic-division argument) and the `addVal` bookkeeping (fiber sum + `e'`-dilation) remain
— next bricks, deliberately unbuilt. No new `structure`/`class`; no owed witness; D1 N/A; D2
stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Polynomial
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

/-- An element dividing every coefficient of a polynomial divides every evaluation of it. -/
theorem dvd_eval_of_dvd_coeff {R : Type*} [CommRing R] {d z : R} {P : Polynomial R}
    (h : ∀ n, d ∣ P.coeff n) : d ∣ P.eval z := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.dvd_sum fun i _ => (h i).mul_right _

section Abstract

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [Normal K K']
variable (A : ValuationSubring L)

/-- **The equivariance**: `comapRingHom` intertwines the `σ̄ = decompositionQuotient s₀`
action on `B = A ∩ K'` with the `s₀`-action on `A` — Pass 50's
`algebraMap_decompositionQuotient_smul`, at the subring level. -/
theorem comapRingHom_decompositionQuotient_smul (s₀ : A.decompositionSubgroup K)
    (b : ↥(A.comap (algebraMap K' L))) :
    comapRingHom K' A (decompositionQuotient K K' A s₀ • b)
      = s₀ • comapRingHom K' A b :=
  Subtype.ext (algebraMap_decompositionQuotient_smul K K' A s₀ b)

/-- The equivariance at the polynomial level: mapping the coefficient-wise `σ̄`-transport of
`F` along `ι` is the `s₀`-transport of `F.map ι`. -/
theorem map_comapRingHom_smul (s₀ : A.decompositionSubgroup K)
    (F : Polynomial ↥(A.comap (algebraMap K' L))) :
    (decompositionQuotient K K' A s₀ • F).map (comapRingHom K' A)
      = (F.map (comapRingHom K' A)).map
          ((MulSemiringAction.toRingAut (A.decompositionSubgroup K) (↥A) s₀ :
            ↥A ≃+* ↥A) : ↥A →+* ↥A) := by
  ext n
  rw [Polynomial.coeff_map, Polynomial.coeff_smul, Polynomial.coeff_map, Polynomial.coeff_map]
  exact congrArg Subtype.val (comapRingHom_decompositionQuotient_smul K K' A s₀ (F.coeff n))

/-- **Prop. 3, direction (i), abstract form**: with Pass 55's descent (`hF`: `F` over
`B = A ∩ K'` maps to Serre's polynomial) and Pass 57's telescoping (`hdvd`: `a = σ̄y − y`
divides every `σ̄`-displacement in `B`), `ι(a)` divides the lift-set product
`∏_h (x − (s₀ · dr h)·x)`. Every coefficient of `σ̄F − F` is divisible by `a`; push along
`ι`, evaluate at `x`; the value is `(σ̄f)(x) − f(x) = ∏ − 0` by Passes 56 and 55. -/
theorem comapRingHom_smul_sub_dvd_liftProd [Fintype (A.decompositionSubgroup K')]
    (s₀ : A.decompositionSubgroup K) (x : ↥A)
    {F : Polynomial ↥(A.comap (algebraMap K' L))}
    (hF : F.map (comapRingHom K' A)
      = fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x)
    {y : ↥(A.comap (algebraMap K' L))}
    (hdvd : ∀ c : ↥(A.comap (algebraMap K' L)),
      (decompositionQuotient K K' A s₀ • y - y) ∣ (decompositionQuotient K K' A s₀ • c - c)) :
    comapRingHom K' A (decompositionQuotient K K' A s₀ • y - y)
      ∣ ∏ h : A.decompositionSubgroup K',
          (x - (s₀ * decompositionRestrict K K' A h) • x) := by
  have hcoeff : ∀ n, (decompositionQuotient K K' A s₀ • y - y)
      ∣ ((decompositionQuotient K K' A s₀ • F - F).coeff n) := by
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_smul]
    exact hdvd (F.coeff n)
  have hcoeff2 : ∀ n,
      comapRingHom K' A (decompositionQuotient K K' A s₀ • y - y)
      ∣ (((decompositionQuotient K K' A s₀ • F - F).map (comapRingHom K' A)).coeff n) := by
    intro n
    rw [Polynomial.coeff_map]
    exact map_dvd (comapRingHom K' A) (hcoeff n)
  have heval := dvd_eval_of_dvd_coeff (z := x) hcoeff2
  have hval : (((decompositionQuotient K K' A s₀ • F - F).map (comapRingHom K' A)).eval x)
      = ∏ h : A.decompositionSubgroup K',
          (x - (s₀ * decompositionRestrict K K' A h) • x) := by
    rw [Polynomial.map_sub, Polynomial.eval_sub, map_comapRingHom_smul K K' A s₀ F, hF,
        map_fullProdXSubSMul_eval K K' A s₀ x, fullProdXSubSMul_eval, sub_zero]
  rwa [hval] at heval

end Abstract

section Instantiate

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [FiniteDimensional K' L] [IsGalois K' L]
variable [Fintype ((extensionIntegers K L).decompositionSubgroup K')]

/-- **Prop. 3, direction (i), at `𝒪_L`** (hypothesis-free): there is one `y ∈ B = 𝒪_L ∩ K'`
with, simultaneously, **the concrete `i_{K'/K}`** — `lowerIndex K B σ̄ = addVal_B (σ̄y − y)`
for every `σ̄` (the sum formula's left side) — **and the divisibility `a ∣ b`** — for every
`x ∈ 𝒪_L` and every lift `s₀`, `ι(σ̄y − y)` divides the lift-set product
`∏_h (x − (s₀ · dr h)·x)`. Passes 55–57 assembled. -/
theorem exists_generator_dvd_liftProd :
    ∃ y : ↥((extensionIntegers K L).comap (algebraMap K' L)),
      (∀ σ : ((extensionIntegers K L).comap (algebraMap K' L)).decompositionSubgroup K,
        lowerIndex K ((extensionIntegers K L).comap (algebraMap K' L)) σ
          = IsDiscreteValuationRing.addVal
              ↥((extensionIntegers K L).comap (algebraMap K' L)) (σ • y - y))
      ∧ ∀ (x : ↥(extensionIntegers K L))
          (s₀ : (extensionIntegers K L).decompositionSubgroup K),
          comapRingHom K' (extensionIntegers K L)
              (decompositionQuotient K K' (extensionIntegers K L) s₀ • y - y)
            ∣ ∏ h : (extensionIntegers K L).decompositionSubgroup K',
                (x - (s₀ * decompositionRestrict K K' (extensionIntegers K L) h) • x) := by
  obtain ⟨y, _, hdvd, haddval⟩ := exists_generator_comap_spec K K' (L := L)
  refine ⟨y, haddval, fun x s₀ => ?_⟩
  obtain ⟨F, hF, _, _⟩ := exists_fullProdXSubSMul_lift_extensionIntegers K K' (L := L) x
  exact comapRingHom_smul_sub_dvd_liftProd K K' (extensionIntegers K L) s₀ x hF
    (fun c => hdvd _ c)

end Instantiate

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms dvd_eval_of_dvd_coeff
#print axioms comapRingHom_decompositionQuotient_smul
#print axioms map_comapRingHom_smul
#print axioms comapRingHom_smul_sub_dvd_liftProd
#print axioms exists_generator_dvd_liftProd

end Anabelian
