/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.RamificationFiltration
import Mathlib

/-!
# The ascent: lower-numbering subgroup compatibility (Serre IV §1 Prop. 2) (Pass 46)

The first prerequisite for **Herbrand's theorem** (the quotient-compatibility of the upper
numbering — Pass 45's `upperRamificationGroup`): how the lower-numbering filtration behaves under a
sub-extension.

> **`ramificationGroup_eq_comap`** — Serre, *Local Fields*, IV §1 Prop. 2: for a tower
> `K ⊆ K' ⊆ L`, `H_u = H ∩ G_u`, where `H = Gal(L/K') ↪ G = Gal(L/K)`.

The lower numbering is **intrinsic to `L`**: `G_i = {σ | ∀ a ∈ 𝒪_L, σa − a ∈ 𝔪_L^{i+1}}` depends
only on the action on the valuation subring `A`, not on the base field. So for the *same* `A` (and
Pass 43 made `A = 𝒪_L` base-independent across the tower), the ramification condition transfers
verbatim along restriction of scalars `Gal(L/K') → Gal(L/K)`. The action agreement is
**definitional** (`rfl`), so the whole proposition reduces to subring/stabilizer bookkeeping.

## What is proved (all axiom-free)

* `decompositionRestrict` — the restriction-of-scalars monoid hom `Gal(L/K') →* Gal(L/K)`
  (`AlgEquiv.restrictScalars`), injective (`decompositionRestrict_injective`), with
  `decompositionRestrict σ • a = σ • a` by `rfl` (`decompositionRestrict_smul`) — the actions agree.
* `restrictScalars_smul_valuationSubring`, `mem_stabilizer_restrictScalars` — the restriction acts
  on `A` (as a valuation subring) exactly as the original, so it preserves the decomposition group.
* **`ramificationGroup_eq_comap`** — Prop. 2 in `comap` form: `ramificationGroup K' A i =
  (ramificationGroup K A i).comap decompositionRestrict`.
* **`ramificationGroup_map_eq`** — the same as the textbook `H_u = H ∩ G_u`:
  `(ramificationGroup K' A i).map decompositionRestrict = decompositionRestrict.range ⊓
  ramificationGroup K A i`.

## Honesty

A structural fact about the ramification filtration of a tower — **no reach toward R1–R3**; nothing
recovered from an abstract group. Stated for a general `A : ValuationSubring L` (it does not itself
need finiteness or the local-field structure); the relevance to local fields is via `A = 𝒪_L`,
whose base-independence across the tower is Pass 43. No new `structure`/`class`
(`decompositionRestrict` is a `def` of a `MonoidHom`; the results are about `Subgroup`s); no owed
witness; D1 N/A; D2 N/A.

**NEXT** (toward Herbrand's theorem): `φ`-transitivity `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` (Serre IV §3
Prop. 15), then the quotient relationship `(G/H)^v = G^v H/H` (Prop. 14) itself.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable (A : ValuationSubring L)

/-- Restriction of scalars acts on the valuation subring `A` exactly as the original automorphism:
`σ.restrictScalars K • A = σ • A` (the underlying map of `L` is unchanged). -/
theorem restrictScalars_smul_valuationSubring (σ : L ≃ₐ[K'] L) :
    σ.restrictScalars K • A = σ • A := by
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

/-- A `K'`-automorphism fixing `A` restricts to a `K`-automorphism fixing `A`. -/
theorem mem_stabilizer_restrictScalars {σ : L ≃ₐ[K'] L}
    (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[K'] L) A) :
    σ.restrictScalars K ∈ MulAction.stabilizer (L ≃ₐ[K] L) A := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [restrictScalars_smul_valuationSubring K K' A, hσ]

/-- **The restriction-of-scalars map on decomposition groups** `Gal(L/K') →* Gal(L/K)`, the group
inclusion attached to the tower `K ⊆ K' ⊆ L`. -/
noncomputable def decompositionRestrict :
    A.decompositionSubgroup K' →* A.decompositionSubgroup K where
  toFun σ := ⟨σ.1.restrictScalars K, mem_stabilizer_restrictScalars K K' A σ.2⟩
  map_one' := by apply Subtype.ext; ext x; rfl
  map_mul' σ τ := by apply Subtype.ext; ext x; rfl

/-- The two decomposition actions on `A` agree: `decompositionRestrict σ` acts as `σ` (by `rfl`). -/
@[simp] theorem decompositionRestrict_smul (σ : A.decompositionSubgroup K') (a : ↥A) :
    decompositionRestrict K K' A σ • a = σ • a := rfl

theorem decompositionRestrict_injective :
    Function.Injective (decompositionRestrict K K' A) := by
  intro σ τ h
  apply Subtype.ext
  have heq : σ.1.restrictScalars K = τ.1.restrictScalars K := Subtype.ext_iff.mp h
  ext x
  exact AlgEquiv.ext_iff.mp heq x

/-- **Subgroup compatibility of the lower numbering** (Serre, *Local Fields*, IV §1 Prop. 2), in
`comap` form: for the tower `K ⊆ K' ⊆ L`, the ramification filtration of the upper extension is the
restriction of the lower one — `ramificationGroup K' A i = (ramificationGroup K A i).comap
decompositionRestrict`. The membership condition `∀ a, σ a − a ∈ 𝔪^{i+1}` is intrinsic to `A`, so it
is unchanged by restriction of scalars (`decompositionRestrict_smul` is `rfl`). -/
theorem ramificationGroup_eq_comap (i : ℕ) :
    ramificationGroup K' A i
      = (ramificationGroup K A i).comap (decompositionRestrict K K' A) := by
  ext σ
  simp only [Subgroup.mem_comap, mem_ramificationGroup_iff, decompositionRestrict_smul]

/-- The textbook form `H_u = H ∩ G_u` of Serre IV §1 Prop. 2: the image of the upper extension's
ramification group is its intersection with the lower one (`H = decompositionRestrict.range`). -/
theorem ramificationGroup_map_eq (i : ℕ) :
    (ramificationGroup K' A i).map (decompositionRestrict K K' A)
      = (decompositionRestrict K K' A).range ⊓ ramificationGroup K A i := by
  rw [ramificationGroup_eq_comap K K' A i, Subgroup.map_comap_eq]

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms restrictScalars_smul_valuationSubring
#print axioms mem_stabilizer_restrictScalars
#print axioms decompositionRestrict
#print axioms decompositionRestrict_smul
#print axioms decompositionRestrict_injective
#print axioms ramificationGroup_eq_comap
#print axioms ramificationGroup_map_eq

end Anabelian
