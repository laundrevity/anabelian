/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Absolute.Tower
import Mathlib

/-!
# Brick B3: the upper numbering on the infinite Galois group (Pass 82)

The L2 capstone's object exists. For a nonarchimedean local `K` and ANY extension `E/K`:

> **`absoluteUpperRamificationGroup K E v : Subgroup (E ≃ₐ[K] E)`**
> `:= ⨅ (L : FiniteGaloisIntermediateField K E), (G^v(L/K)).comap (restrictNormalHom L)`

— the preimage-intersection over the finite Galois subextensions (the Pass-79 design). At
`E := separableClosure K (AlgebraicClosure K)` this is **`G^v(K^sep/K)`, the upper
numbering on the absolute Galois group** — the filtration whose group-theoretic
recoverability is the entry point of the anabelian program (the local reconstruction of
Mochizuki's *Topics I* starts from exactly this data on `Gal(K̄/K)`). The generality in
`E` also covers the maximal abelian extension and other infinite subextensions downstream
(the L3 interface).

Provided here: the definition, the membership characterization
(`mem_absoluteUpperRamificationGroup_iff`), **closedness in the Krull topology**
(`isClosed_absoluteUpperRamificationGroup` — each factor is a preimage of a finite
discrete level under Mathlib's continuous `restrictNormalHom`), and the easy half of the
projection compatibility (`map_absoluteUpperRamificationGroup_le`). What makes this
definition RIGHT — rather than merely well-formed — is Herbrand's theorem (Passes 77–81):
the finite levels form a compatible system, so the intersection is an inverse limit and
the projections should be SURJECTIVE onto every finite level. That surjectivity (brick
B5) is the capstone's remaining theorem.

## Honesty

A definition + three formal properties for a given base — **no reach toward R1–R3**;
nothing is recovered from an abstract group, and the projection surjectivity (B5, the
content-bearing theorem) is NOT claimed. Rule-2 note: the definition is a `def` (an
`iInf` of comaps of proved objects), not a `structure`/`class` — no new constraint
content; the finite-level filtration's witnesses live at Pass 23. No owed witness; D1
N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (E : Type*) [Field E] [Algebra K E]

/-- **The upper ramification filtration on the (possibly infinite) Galois group** of
`E/K`: `σ ∈ G^v(E/K)` iff its restriction to EVERY finite Galois subextension lies in the
finite-level `G^v` — the preimage-intersection over Mathlib's
`FiniteGaloisIntermediateField` system (the Pass-79 carrier decision). At
`E := separableClosure K (AlgebraicClosure K)` this is the upper numbering on the absolute
Galois group `Gal(K^sep/K)`; the generality also covers the maximal abelian and other
infinite subextensions downstream. Herbrand's theorem (Passes 77–81) is what makes this
the right object: the finite levels form a compatible system. -/
noncomputable def absoluteUpperRamificationGroup (v : ℝ) : Subgroup (E ≃ₐ[K] E) :=
  ⨅ L : FiniteGaloisIntermediateField K E,
    (fullUpperRamificationGroup K ↥L v).comap
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField)

/-- Membership: restriction to every finite Galois subextension lies in the finite-level
filtration. -/
theorem mem_absoluteUpperRamificationGroup_iff {v : ℝ} {σ : E ≃ₐ[K] E} :
    σ ∈ absoluteUpperRamificationGroup K E v
      ↔ ∀ L : FiniteGaloisIntermediateField K E,
          AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField σ
            ∈ fullUpperRamificationGroup K ↥L v := by
  simp [absoluteUpperRamificationGroup, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- **`G^v(E/K)` is closed in the Krull topology**: each factor is the preimage of a
subset of a finite discrete group under a continuous restriction
(`InfiniteGalois.restrictNormalHom_continuous`), and an intersection of closed sets is
closed. The closedness that matches the fundamental theorem of infinite Galois theory's
closed-subgroup correspondence. -/
theorem isClosed_absoluteUpperRamificationGroup (v : ℝ) :
    IsClosed ((absoluteUpperRamificationGroup K E v : Set (E ≃ₐ[K] E))) := by
  have h1 : ((absoluteUpperRamificationGroup K E v : Set (E ≃ₐ[K] E)))
      = ⋂ L : FiniteGaloisIntermediateField K E,
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField) ⁻¹'
            (fullUpperRamificationGroup K ↥L v : Set _) := by
    simp [absoluteUpperRamificationGroup, Subgroup.coe_iInf, Subgroup.coe_comap]
  rw [h1]
  exact isClosed_iInter fun L =>
    (isClosed_discrete _).preimage
      (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)

/-- The easy half of the projection compatibility (brick B5): the image of `G^v(E/K)` at
each finite level lands INSIDE `G^v(L/K)`. The reverse inclusion — every finite-level
element lifts — is the compactness theorem, next. -/
theorem map_absoluteUpperRamificationGroup_le
    (L : FiniteGaloisIntermediateField K E) (v : ℝ) :
    (absoluteUpperRamificationGroup K E v).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField)
      ≤ fullUpperRamificationGroup K ↥L v :=
  Subgroup.map_le_iff_le_comap.mpr (iInf_le _ L)


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms absoluteUpperRamificationGroup
#print axioms mem_absoluteUpperRamificationGroup_iff
#print axioms isClosed_absoluteUpperRamificationGroup
#print axioms map_absoluteUpperRamificationGroup_le

end Anabelian
