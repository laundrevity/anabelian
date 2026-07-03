/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Rung L1: the residue-reduction map (faithfulness half)

Rung **L1** of `ROADMAP.md` includes the *residue reduction* `Gal(K̄/K) ↠ Gal(𝔽_q̄/𝔽_q)` for a local
field `K` — the prototype of the local-to-residue map that local reconstruction (R1) consumes. This
file proves the **faithfulness (injective) half** of the abstract version of that map, the strongest
clean fragment Mathlib's (definition-only) ramification API supports.

## What Mathlib provides (and does not)

`RingTheory/Valuation/RamificationGroup.lean` (the *entire* ramification API in `v4.30.0`) contains
**only definitions**, no theorems: for a valuation subring `A` of `L/K`,
* `ValuationSubring.decompositionSubgroup K A` — the stabilizer of `A` in `Gal(L/K) = L ≃ₐ[K] L`;
* its `MulSemiringAction` on the residue field `IsLocalRing.ResidueField A`, packaged as the
  **residue-reduction homomorphism** `MulSemiringAction.toRingAut …`
  (`decompositionSubgroup →* RingAut (ResidueField A)`);
* `ValuationSubring.inertiaSubgroup K A` — *defined* as the **kernel** of that reduction map.

There is **no** surjectivity, no identification of the target with a residue Galois group
`Gal(𝔽_q̄/𝔽_q)`, and no maximal-unramified-extension theory. Those are the substantive (and absent)
content; see "Scope" below.

## What is proved here

* `Anabelian.inertiaSubgroup_eq_reductionKer` — the definitional identity
  `inertiaSubgroup = ker (residue reduction)`.
* `Anabelian.mem_inertiaSubgroup_iff` — the usable characterization: an element of the decomposition
  group lies in the inertia subgroup **iff it acts trivially on the residue field**.
* `Anabelian.residueReduction_quotient_injective` — the **faithful embedding**: an *injective* map
  from `decompositionSubgroup ⧸ inertiaSubgroup` into `RingAut (ResidueField A)`. Its domain is
  `_ ⧸ (reduction).ker = _ ⧸ inertiaSubgroup K A` by definition.

Together: the residue reduction is a group hom whose kernel is exactly inertia, so
decomposition-mod-inertia embeds faithfully into the residue automorphism group — the injective half
of `decomposition/inertia ≅ Gal(residue/residue)`.

## Honesty: genuine but light; what it is NOT

This is **genuine L1 content in new (ramification) territory**, not a restatement of Passes 0–3, but
it is **light**: because Mathlib's ramification API is definitions only, each result is a short
derivation (`MonoidHom.mem_ker`, `QuotientGroup.kerLift_injective`) applied to the residue-reduction
map. The **surjectivity half** — the genuinely hard, R1-relevant content (the reduction is *onto*
the residue Galois group; needs maximal-unramified / Hensel-lifting theory) — is **absent from
Mathlib** and is *not* attempted here; it is logged as an L1 sub-target in `ROADMAP.md`.

**Not reconstruction.** Every statement is a property of the Galois action of a *given* field on its
*given* residue field; nothing is recovered from an abstract topological group (no reach toward
R1–R3).

**No load-bearing hypothesis / owed witness.** The results hold for *any* valuation subring `A` of
any `L/K`; there is no hypothesis whose removal breaks the conclusion, so no Owed witness is
incurred. No `structure`/`class` is introduced.

## Axiom status

Standard axioms only (`#print axioms` below). Pass-4 ledger delta: **0 DEBT / 0 FOUNDATIONAL**;
0 owed witnesses added.
-/

open ValuationSubring IsLocalRing

namespace Anabelian

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The inertia subgroup is, by definition, the kernel of the residue-reduction homomorphism
`decompositionSubgroup K A →* RingAut (ResidueField A)`. -/
theorem inertiaSubgroup_eq_reductionKer (A : ValuationSubring L) :
    ValuationSubring.inertiaSubgroup K A =
      (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)).ker := rfl

/-- **Characterization of inertia.** An automorphism in the decomposition group lies in the inertia
subgroup iff it acts trivially on the residue field. (The defining property of inertia, made usable:
inertia is exactly the pointwise stabilizer of the residue field inside the decomposition group.) -/
theorem mem_inertiaSubgroup_iff (A : ValuationSubring L) (σ : A.decompositionSubgroup K) :
    σ ∈ ValuationSubring.inertiaSubgroup K A ↔
      ∀ x : ResidueField A,
        MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A) σ x = x := by
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker, RingEquiv.ext_iff]
  simp

/-- **Faithfulness half of the residue reduction.** The residue-reduction map induces an *injective*
homomorphism `decompositionSubgroup ⧸ inertiaSubgroup ↪ RingAut (ResidueField A)`. That is, distinct
cosets of inertia act differently on the residue field. (The domain `_ ⧸ (reduction).ker` is
`_ ⧸ inertiaSubgroup K A` by `inertiaSubgroup_eq_reductionKer`.)

The *surjectivity* half — that this embedding hits all of the residue Galois group — is the hard,
R1-relevant content absent from Mathlib; see this file's module docstring and `ROADMAP.md`. -/
theorem residueReduction_quotient_injective (A : ValuationSubring L) :
    Function.Injective (QuotientGroup.kerLift
      (MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A))) :=
  QuotientGroup.kerLift_injective _

-- Reproducible axiom audit (re-runs on every `lake build`). Expected: the three standard axioms.
#print axioms inertiaSubgroup_eq_reductionKer
#print axioms mem_inertiaSubgroup_iff
#print axioms residueReduction_quotient_injective

end Anabelian
