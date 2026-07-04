/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Herbrand.Main
import Mathlib

/-!
# Brick B1: the ramification filtrations on the full Galois group (Pass 80)

First brick of the L2 capstone (the Pass-79 design: `G^v` on `Gal(K^sep/K)`). The finite
arc (Passes 50–78) lives on decomposition subgroups `D(𝒪_L) ≤ (L ≃ₐ[K] L)`; the profinite
stack (`FiniteGaloisIntermediateField`, `restrictNormalHom`, `continuousMulEquivToLimit`)
speaks full Galois groups. This file is the translation layer:

* **`fullRamificationGroup K L u`**, **`fullUpperRamificationGroup K L v`** — the
  filtrations as subgroups of the FULL `L ≃ₐ[K] L`, by `.map (D.subtype)` (Pass 78's
  common-ambient idiom, promoted to definitions; `D = ⊤` under normality, Pass 52, so
  nothing is lost).
* **`subtype_comp_decompositionQuotient`** — the square: `dq` IS
  `AlgEquiv.restrictNormalHom`, conjugated by the inclusions — by `rfl` (Pass 50 built it
  that way; this is the receipt).
* **`map_fullRamificationGroup_eq`** — Lemma 5, full-group form.
* **`map_fullUpperRamificationGroup_eq`** — **Herbrand's theorem, full-group form**:
  `(G^v(L/K)).map (restrictNormalHom K') = G^v(K'/K)` — the transition maps of the
  profinite system carry `G^v` to `G^v` on the nose.

Each transport proof is four rewrites: `Subgroup.map_map`, the square, `map_map` back, the
finite-arc theorem (P73/P77), and the carrier equality (P57). Next bricks: B2
(intermediate-field plumbing), B3 (the `⨅` definition on `Gal(K^sep/K)` + closedness), B4
(functorial compatibility), B5 (projection surjectivity).

## Honesty

A translation layer for a given finite extension — **no reach toward R1–R3**; the absolute
`G^v` is NOT yet defined (B3), and its projection surjectivity (B5) is the real theorem
ahead. The definitions re-package proved objects along an inclusion — no rule-2
obligation beyond the underlying ones (the filtration's models/witnesses live at Pass 23;
these are images under a fixed hom, not new structure). No owed witness; D1 N/A; D2
untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


section Defs

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The lower ramification filtration on the full Galois group** `L ≃ₐ[K] L`: the image
of the decomposition-subgroup filtration under the inclusion (Pass 78's common-ambient
idiom, promoted to a definition). Under `[Normal K L]` the decomposition subgroup is `⊤`
(Pass 52), so nothing is lost. -/
noncomputable def fullRamificationGroup (u : ℕ) : Subgroup (L ≃ₐ[K] L) :=
  (ramificationGroup K (extensionIntegers K L) u).map
    ((extensionIntegers K L).decompositionSubgroup K).subtype

/-- **The upper ramification filtration on the full Galois group** `L ≃ₐ[K] L` — the
carrier on which the absolute (`Gal(K^sep/K)`) upper numbering will be assembled (bricks
B3–B5). -/
noncomputable def fullUpperRamificationGroup (v : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  (upperRamificationGroup K (extensionIntegers K L) v).map
    ((extensionIntegers K L).decompositionSubgroup K).subtype

end Defs

section Square

variable (K : Type*) [Field K]
variable (K' : Type*) [Field K'] [Algebra K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable (A : ValuationSubring L)

/-- **The square**: the quotient restriction `dq` IS Mathlib's
`AlgEquiv.restrictNormalHom`, conjugated by the subtype inclusions — definitionally
(`rfl`): Pass 50 built `dq` from `restrictNormalHom` and this square is the receipt. -/
theorem subtype_comp_decompositionQuotient :
    ((A.comap (algebraMap K' L)).decompositionSubgroup K).subtype.comp
        (decompositionQuotient K K' A)
      = (AlgEquiv.restrictNormalHom K').comp (A.decompositionSubgroup K).subtype :=
  MonoidHom.ext fun _ => rfl

end Square

section Transport

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Normal K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **LEMMA 5, full-group form** (Serre IV §3): under `restrictNormalHom`, the image of
the `u`-th full lower ramification group of `L/K` is that of `K'/K` at `⌈φ_{L/K'}(u)⌉` —
the interface form the profinite stack consumes. -/
theorem map_fullRamificationGroup_eq (u : ℕ) :
    (fullRamificationGroup K L u).map (AlgEquiv.restrictNormalHom K')
      = fullRamificationGroup K K'
          ⌈herbrandPhi K' (extensionIntegers K L) (u : ℝ)⌉₊ := by
  unfold fullRamificationGroup
  rw [Subgroup.map_map, ← subtype_comp_decompositionQuotient K K'
    (extensionIntegers K L), ← Subgroup.map_map,
    map_ramificationGroup_eq_ceil K K' u,
    extensionIntegers_comap_eq K K' (L := L)]

/-- **HERBRAND'S THEOREM, full-group form** (Serre IV §3 Prop. 14): under
`restrictNormalHom : (L ≃ₐ[K] L) →* (K' ≃ₐ[K] K')`,

`(G^v(L/K)).map (restrictNormalHom K') = G^v(K'/K)`

— the transition maps of the profinite system carry the upper filtration to the upper
filtration, exactly. This is the compatibility that bricks B3–B5 turn into
`G^v(K^sep/K)`. -/
theorem map_fullUpperRamificationGroup_eq (v : ℝ) :
    (fullUpperRamificationGroup K L v).map (AlgEquiv.restrictNormalHom K')
      = fullUpperRamificationGroup K K' v := by
  unfold fullUpperRamificationGroup
  rw [Subgroup.map_map, ← subtype_comp_decompositionQuotient K K'
    (extensionIntegers K L), ← Subgroup.map_map,
    map_upperRamificationGroup_eq K K' v,
    extensionIntegers_comap_eq K K' (L := L)]

end Transport


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms fullRamificationGroup
#print axioms fullUpperRamificationGroup
#print axioms subtype_comp_decompositionQuotient
#print axioms map_fullRamificationGroup_eq
#print axioms map_fullUpperRamificationGroup_eq

end Anabelian
