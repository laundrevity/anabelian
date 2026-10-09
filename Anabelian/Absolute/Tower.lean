/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Absolute.FullGroup
import Mathlib

/-!
# Bricks B2 (+ B4's heart): the profinite tower plumbing (Pass 81)

Second brick of the L2 capstone. The absolute upper numbering will live on
`Gal(K^sep/K)`, presented by Mathlib's `FiniteGaloisIntermediateField` system; this file
supplies the `≤`-pair plumbing in EXACTLY Mathlib's `finGaloisGroupMap` conventions
(`Galois/Profinite.lean`) — same algebra structure (`RingHom.toAlgebra ∘
Subsemiring.inclusion`), same tower proof, same transition map (`restrictNormalHom`) — so
that everything composes with `finGaloisGroupFunctor` definitionally:

* `leAlgebra`, `leAlgebra_isScalarTower`, `leAlgebra_finiteDimensional`,
  `leAlgebra_isGalois` — the instance package for a pair `L₁ ≤ L₂` (finite-dimensionality
  from the FINITE level, not the infinite ambient; separability of intermediate fields is
  already a Mathlib instance, probe-verified).
* **`map_fullUpperRamificationGroup_le`** — the payoff, ahead of schedule (this was
  planned as brick B4): **Herbrand's theorem along the profinite transitions** — for
  `L₁ ≤ L₂` in `FiniteGaloisIntermediateField K E`, any separable `E`,

  `(G^v(L₂/K)).map (restrictNormalHom ↥L₁) = G^v(L₁/K)`.

  B1's transport theorem fires at the tower `(K, ↥L₁, ↥L₂)` once the package above is
  `letI`-ed in. This is the compatible-system property that brick B3's `⨅`-definition of
  `G^v(K^sep/K)` will lean on, and brick B5's surjectivity will exploit level by level.

## Honesty

Plumbing in Mathlib's own conventions plus one instantiation of B1 — **no reach toward
R1–R3**. The absolute `G^v` (B3) and its projection surjectivity (B5) are NOT claimed. No
new `structure`/`class` beyond an `abbrev` for an existing Mathlib construction; no owed
witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


section Plumbing

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/- Separability of intermediate fields of a separable extension is already a Mathlib
instance — verified by probe; no declaration needed. -/

end Plumbing

section Tower

variable {k E : Type*} [Field k] [Field E] [Algebra k E]
variable (L₁ L₂ : FiniteGaloisIntermediateField k E)

/-- The algebra structure on a `≤`-pair of finite Galois intermediate fields, in EXACTLY
Mathlib's `finGaloisGroupMap` convention (`RingHom.toAlgebra ∘ Subsemiring.inclusion`) —
so everything built here is definitionally aligned with `finGaloisGroupFunctor`. -/
abbrev leAlgebra (h : L₁ ≤ L₂) : Algebra ↥L₁ ↥L₂ :=
  RingHom.toAlgebra (Subsemiring.inclusion h)

/-- The `≤`-pair algebra is a scalar tower over the base (again Mathlib's convention:
`of_algebraMap_eq' rfl`). -/
theorem leAlgebra_isScalarTower (h : L₁ ≤ L₂) :
    letI := leAlgebra L₁ L₂ h
    IsScalarTower k ↥L₁ ↥L₂ :=
  letI := leAlgebra L₁ L₂ h
  IsScalarTower.of_algebraMap_eq' rfl

/-- Finite-dimensionality of the `≤`-pair — from the FINITE level (the
`FiniteGaloisIntermediateField` structure), not the (typically infinite) ambient. -/
theorem leAlgebra_finiteDimensional (h : L₁ ≤ L₂) :
    letI := leAlgebra L₁ L₂ h
    FiniteDimensional ↥L₁ ↥L₂ := by
  let := leAlgebra L₁ L₂ h
  have := leAlgebra_isScalarTower L₁ L₂ h
  exact FiniteDimensional.right k ↥L₁ ↥L₂

/-- The `≤`-pair is Galois (`L₂/k` Galois ⟹ `L₂/L₁` Galois, `tower_top`). -/
theorem leAlgebra_isGalois (h : L₁ ≤ L₂) :
    letI := leAlgebra L₁ L₂ h
    IsGalois ↥L₁ ↥L₂ := by
  let := leAlgebra L₁ L₂ h
  have := leAlgebra_isScalarTower L₁ L₂ h
  exact IsGalois.tower_top_of_isGalois k ↥L₁ ↥L₂

end Tower

section Compatibility

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {E : Type*} [Field E] [Algebra K E] [Algebra.IsSeparable K E]
variable (L₁ L₂ : FiniteGaloisIntermediateField K E)

/-- **HERBRAND'S THEOREM ALONG THE PROFINITE TRANSITIONS** (the two-level compatibility,
brick B4's heart): for finite Galois intermediate fields `L₁ ≤ L₂` of ANY separable
extension `E/K` of the local base, the transition map `Gal(L₂/K) → Gal(L₁/K)` (Mathlib's
`restrictNormalHom`, the map of `finGaloisGroupFunctor`) carries `G^v(L₂/K)` onto
`G^v(L₁/K)` — the compatible-system property that makes the `⨅`-definition of
`G^v(K^sep/K)` (brick B3) the right object. -/
theorem map_fullUpperRamificationGroup_le (h : L₁ ≤ L₂) (v : ℝ) :
    letI := leAlgebra L₁ L₂ h
    haveI := leAlgebra_isScalarTower L₁ L₂ h
    (fullUpperRamificationGroup K ↥L₂ v).map (AlgEquiv.restrictNormalHom ↥L₁)
      = fullUpperRamificationGroup K ↥L₁ v := by
  let := leAlgebra L₁ L₂ h
  have := leAlgebra_isScalarTower L₁ L₂ h
  have := leAlgebra_finiteDimensional L₁ L₂ h
  have := leAlgebra_isGalois L₁ L₂ h
  exact map_fullUpperRamificationGroup_eq K ↥L₁ (L := ↥L₂) v

end Compatibility


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms leAlgebra
#print axioms leAlgebra_isScalarTower
#print axioms leAlgebra_finiteDimensional
#print axioms leAlgebra_isGalois
#print axioms map_fullUpperRamificationGroup_le

end Anabelian
