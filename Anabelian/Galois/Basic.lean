/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Perfect

/-!
# Pass 0 seed lemma: faithfulness of the Galois correspondence

This is the first axiom-free, genuinely Galois-theoretic lemma of the project. It is the
**analog of a "seed"**: small, honest content that touches the project's actual subject
(absolute Galois groups and the infinite Galois correspondence) and exercises the Mathlib
API inventoried in `NOTES.md`.

## What is proved

`Anabelian.fixingSubgroup_injective`: for an (infinite) Galois extension `K/k`, the assignment
sending an intermediate field `L` to its fixing subgroup `Gal(K/L) ≤ Gal(K/k)` is **injective**.
Equivalently — and this is how it is proved — an intermediate field is *recovered* from its
subgroup as the fixed field of that subgroup (`InfiniteGalois.fixedField_fixingSubgroup`).

`Anabelian.absoluteGaloisGroup_fixingSubgroup_injective`: the same statement specialized to the
**absolute Galois group** `G_K := Gal(K^al/K)` of a *perfect* field `K` (number fields, finite
fields, and characteristic-0 local fields are all perfect — i.e. exactly the fields of anabelian
interest). The lattice of algebraic subextensions of `K^al/K` injects into the subgroup lattice
of `G_K`.

## Why this is "anabelian-flavored" — and the honest limits of that claim

Anabelian geometry recovers arithmetic/geometric objects from their Galois (étale fundamental)
groups. The most primitive *precondition* for any such reconstruction is **faithfulness**: distinct
objects must determine distinct groups, otherwise nothing could be recovered. The lemma here is
exactly that faithfulness, for the lattice of subextensions. It is the formal "this is even
possible in principle" floor.

It is emphatically **not** a reconstruction theorem. The map `L ↦ Gal(K/L)` here is built from the
*given* action of `Gal(K/k)` on the *given* field `K`. Genuine anabelian reconstruction
(Neukirch–Uchida; and above it, Mochizuki's mono-anabelian recovery) runs the other way: it
recovers the field — up to isomorphism, then algorithmically/functorially — from the *abstract
topological group alone*, with no a priori field or action handed to it. That hard converse is the
multi-year target named in `ROADMAP.md`; nothing here approaches it. See `NOTES.md` for the honest
scope statement governing this pass.

## Axiom status

Both results depend only on the standard axioms `propext`, `Classical.choice`, `Quot.sound`
(verified by the `#print axioms` commands below, which re-run on every build). Per `AXIOM_LEDGER.md`
these are free; this pass introduces **zero** `DEBT` and **zero** `FOUNDATIONAL` axioms.

## Main Mathlib API doing the real work

* `InfiniteGalois.fixedField_fixingSubgroup` — the round-trip `fixedField (fixingSubgroup L) = L`,
  itself a consequence of Mathlib's fundamental theorem of infinite Galois theory
  (`InfiniteGalois.IntermediateFieldEquivClosedSubgroup`).
* `Field.absoluteGaloisGroup` — `Gal(K^al/K)` packaged as a type.
* The instance `[PerfectField K] → IsGalois K (AlgebraicClosure K)`, which lets the general
  statement specialize to the absolute Galois group.

## References

* Mathlib: `Mathlib/FieldTheory/Galois/Infinite.lean` and
  `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`.
* J. Neukirch, *Algebraic Number Theory* (1992) — for the contrast: the deep converse direction.
-/

namespace Anabelian

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- **Faithfulness of the (infinite) Galois correspondence.**
For a Galois extension `K/k`, distinct intermediate fields have distinct fixing subgroups of
`Gal(K/k)`; equivalently, an intermediate field is recovered from its subgroup as its fixed field.

This is the most primitive precondition of anabelian reconstruction (distinct objects ⟹ distinct
groups). It is *not* reconstruction: the map uses the given action of `Gal(K/k)` on `K`. -/
theorem fixingSubgroup_injective [IsGalois k K] :
    Function.Injective
      (IntermediateField.fixingSubgroup : IntermediateField k K → Subgroup Gal(K/k)) := by
  intro L₁ L₂ h
  rw [← InfiniteGalois.fixedField_fixingSubgroup L₁,
      ← InfiniteGalois.fixedField_fixingSubgroup L₂, h]

/-- Specialization of `fixingSubgroup_injective` to the **absolute Galois group**
`G_K = Gal(K^al/K)` of a perfect field `K` (number fields, finite fields, and char-0 local fields
are perfect). The lattice of algebraic subextensions of `K^al/K` injects into the subgroup lattice
of `G_K`.

The hypothesis `PerfectField K` is exactly what makes `K^al/K` separable, hence Galois, so that the
infinite Galois correspondence applies to the absolute Galois group. -/
theorem absoluteGaloisGroup_fixingSubgroup_injective
    (K : Type*) [Field K] [PerfectField K] :
    Function.Injective
      (IntermediateField.fixingSubgroup :
        IntermediateField K (AlgebraicClosure K) → Subgroup (Field.absoluteGaloisGroup K)) :=
  fixingSubgroup_injective

-- Reproducible axiom audit (re-runs on every `lake build`). Expected: the three standard axioms.
#print axioms fixingSubgroup_injective
#print axioms absoluteGaloisGroup_fixingSubgroup_injective

end Anabelian
