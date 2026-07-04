/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Absolute.Main
import Mathlib

/-!
# L3.0: the maximal abelian extension (Pass 86)

The first rung of the L3 ladder (the Pass-85 design): **the stage of local class field
theory exists**. For any Galois `E/K`:

* **`maximalAbelianSubextension K E`** — the fixed field of the closed commutator
  subgroup of `Gal(E/K)`, via the fundamental theorem of infinite Galois theory; at
  `E = K^sep` this is **`K^ab`**, the maximal abelian extension.
* `K^ab/K` **is Galois** (`isGalois_maximalAbelianSubextension` — normality of the closed
  commutator subgroup through `normal_iff_isGalois`).
* **`Gal(K^ab/K)` is the topological abelianization** of `Gal(E/K)`
  (`maximalAbelianGalEquiv`) and is **abelian** (`maximalAbelianSubextension_mul_comm`).
* **Maximality is a theorem, not a name** (`le_maximalAbelianSubextension`): every
  abelian normal subextension lies inside it.
* **`G^v(K^ab/K)` fires as-is** — the sanity example instantiates Pass 82's
  `absoluteUpperRamificationGroup` at `↥K^ab`, exactly as that definition's generality
  was designed to allow. The two sides of L3.4's ramification correspondence — the unit
  filtration of `K^×` and this `G^v(K^ab/K)` — now both exist; the map between them is
  the L3.3 wall.

## Honesty

A definitional rung for a given base — **no reach toward R1–R3**; local class field
theory (the reciprocity map, L3.3) is NOT claimed, and nothing here recovers anything
from an abstract group. Rule-2 note: the one `def` with a claiming NAME
(`maximalAbelianSubextension`) carries its own justification theorem
(`le_maximalAbelianSubextension` — maximality proved, not stipulated); no new
`structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set InfiniteGalois
open scoped Pointwise ValuativeRel commutatorElement
open ValuativeRel

namespace Anabelian


variable (K : Type*) [Field K]
variable (E : Type*) [Field E] [Algebra K E] [IsGalois K E]

/-- The topological closure of the commutator subgroup of `Gal(E/K)` — the kernel of the
topological abelianization. -/
noncomputable def commutatorClosure : Subgroup (E ≃ₐ[K] E) :=
  (commutator (E ≃ₐ[K] E)).topologicalClosure

instance commutatorClosure_normal : (commutatorClosure K E).Normal :=
  Subgroup.is_normal_topologicalClosure _

omit [IsGalois K E] in
theorem isClosed_commutatorClosure : IsClosed ((commutatorClosure K E) : Set (E ≃ₐ[K] E)) :=
  Subgroup.isClosed_topologicalClosure _

/-- **The maximal abelian subextension** `K^ab ∩ E`: the fixed field of the closed
commutator subgroup, via the fundamental theorem of infinite Galois theory. At
`E = K^sep` this is `K^ab`, the maximal abelian extension of `K` — the stage of local
class field theory. -/
noncomputable def maximalAbelianSubextension : IntermediateField K E :=
  IntermediateField.fixedField (commutatorClosure K E)

/-- The Galois correspondence, closed case: the fixing subgroup of the maximal abelian
subextension is exactly the closed commutator subgroup. -/
theorem fixingSubgroup_maximalAbelianSubextension :
    (maximalAbelianSubextension K E).fixingSubgroup = commutatorClosure K E :=
  fixingSubgroup_fixedField
    (⟨commutatorClosure K E, isClosed_commutatorClosure K E⟩ : ClosedSubgroup (E ≃ₐ[K] E))

/-- `K^ab/K` is Galois (the closed commutator subgroup is normal;
`normal_iff_isGalois`). -/
instance isGalois_maximalAbelianSubextension :
    IsGalois K ↥(maximalAbelianSubextension K E) := by
  rw [← normal_iff_isGalois]
  rw [fixingSubgroup_maximalAbelianSubextension]
  infer_instance

/-- **`Gal(K^ab/K)` is the topological abelianization of `Gal(E/K)`**:
`Gal(E/K) ⧸ closure(commutator) ≃* Gal(K^ab/K)` (Mathlib's `normalAutEquivQuotient`). -/
noncomputable def maximalAbelianGalEquiv :
    (E ≃ₐ[K] E) ⧸ (commutatorClosure K E)
      ≃* (↥(maximalAbelianSubextension K E) ≃ₐ[K] ↥(maximalAbelianSubextension K E)) :=
  normalAutEquivQuotient
    (⟨commutatorClosure K E, isClosed_commutatorClosure K E⟩ : ClosedSubgroup (E ≃ₐ[K] E))

omit [IsGalois K E] in
/-- The quotient by the closed commutator subgroup is commutative (commutator elements
die). -/
theorem quotient_commutatorClosure_mul_comm
    (x y : (E ≃ₐ[K] E) ⧸ (commutatorClosure K E)) : x * y = y * x := by
  induction x using QuotientGroup.induction_on with | _ a =>
  induction y using QuotientGroup.induction_on with | _ b =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h1 : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
    group
  rw [h1]
  exact Subgroup.le_topologicalClosure _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

/-- **`Gal(K^ab/K)` is abelian** — transported through the abelianization equivalence.
(Stated as a theorem, not a `CommGroup` instance, to avoid a second `Group`-structure
path on `AlgEquiv`.) -/
theorem maximalAbelianSubextension_mul_comm
    (σ τ : ↥(maximalAbelianSubextension K E) ≃ₐ[K] ↥(maximalAbelianSubextension K E)) :
    σ * τ = τ * σ := by
  obtain ⟨x, rfl⟩ := (maximalAbelianGalEquiv K E).surjective σ
  obtain ⟨y, rfl⟩ := (maximalAbelianGalEquiv K E).surjective τ
  rw [← map_mul, ← map_mul, quotient_commutatorClosure_mul_comm K E x y]

/-- **MAXIMALITY** (the name is earned, not asserted): every abelian normal subextension
lies inside `K^ab` — its Galois group kills all commutators, so its fixing subgroup
contains the closed commutator subgroup, and the correspondence flips. -/
theorem le_maximalAbelianSubextension (L : IntermediateField K E) [Normal K ↥L]
    (h : ∀ σ τ : (↥L ≃ₐ[K] ↥L), σ * τ = τ * σ) :
    L ≤ maximalAbelianSubextension K E := by
  have h1 : commutatorClosure K E ≤ L.fixingSubgroup := by
    apply Subgroup.topologicalClosure_minimal
    · change ⁅(⊤ : Subgroup (E ≃ₐ[K] E)), ⊤⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      have h2 : AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L ⁅g₁, g₂⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (h _ _)
      rw [← L.restrictNormalHom_ker]
      exact h2
    · exact fixingSubgroup_isClosed L
  exact (IntermediateField.le_iff_le (commutatorClosure K E) L).mpr h1


section Sanity

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (E : Type*) [Field E] [Algebra K E] [IsGalois K E]

/-- `G^v(K^ab/K)` — Pass 82's absolute upper numbering, instantiated at the maximal
abelian subextension. The Galois side of L3.4's ramification correspondence. -/
noncomputable example (v : ℝ) :
    Subgroup (↥(maximalAbelianSubextension K E)
      ≃ₐ[K] ↥(maximalAbelianSubextension K E)) :=
  absoluteUpperRamificationGroup K ↥(maximalAbelianSubextension K E) v

end Sanity

-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms commutatorClosure
#print axioms maximalAbelianSubextension
#print axioms fixingSubgroup_maximalAbelianSubextension
#print axioms isGalois_maximalAbelianSubextension
#print axioms maximalAbelianGalEquiv
#print axioms maximalAbelianSubextension_mul_comm
#print axioms le_maximalAbelianSubextension

end Anabelian
