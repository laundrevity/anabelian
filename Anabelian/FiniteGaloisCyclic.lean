/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.FiniteField
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Rung L1, toward `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`: the finite levels `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n`

## The risk this pass addresses, and the decision

Six passes in, the project holds several *halves* (one `FOUNDATIONAL` boundary; the surjective half
of `≅ Ẑ`, Pass 6; the injective half of the residue reduction, Pass 4) but no L1 *whole* beyond the
finite-field results. A pile of halves reads as progress but closes nothing — the project-level
relocate-and-never-close pattern. The preferred move is to **close a whole**.

The targeted whole — **`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`** (route (i)) — turns out **not closable axiom-free this
pass**: Pass 6's surjective half of `zhatToGalois : Ẑ → Gal` used clean topology, but the
**injective** half needs `Ẑ`'s presentation as `lim ℤ/n` (Mathlib's
`Ẑ = ProfiniteGrp.completion (Multiplicative ℤ)` is indexed by `FiniteIndexNormalSubgroup`, **not**
`ℤ/n`) and the cofinal matching of that inverse system with `Gal`'s — genuinely multi-pass, and
**not** available off the shelf (Pass 7 `NOTES.md`). So `≅ Ẑ` is a genuine multi-pass item; per the
route-(i) fallback we make **real axiom-free progress on the injective half** by closing its
per-level ingredient — and we do **not** posit the iso (or its injective half) as `FOUNDATIONAL`:
closing-by-positing is fake closing, the stacking trap.

## What is proved — a complete, closed, axiom-free theorem

`Anabelian.galoisFiniteField_mulEquivZMod`: for a **finite** field extension `L/K` (finite fields),
the Galois group is cyclic of order the degree, i.e.
`Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L))`.

Proof: `Gal(L/K)` is `IsCyclic` (finite-field instance) of `Nat.card = Module.finrank K L`
(`IsGalois.card_aut_eq_finrank`; finite extensions of finite fields are automatically Galois), and a
finite cyclic group of order `n` is `≃* Multiplicative (ZMod n)` (`zmodCyclicMulEquiv`).

This is a **complete whole** (a closed structural theorem, not a half), and it is exactly the
**per-level data of `≅ Ẑ`'s injective half**: `Ẑ = lim ℤ/n` and
`Gal(𝔽_q̄/𝔽_q) = lim Gal(𝔽_{q^n}/𝔽_q)`, so the level isos `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n` are the
ingredient that — once `Ẑ`'s inverse-system
presentation and the cofinal matching are formalized (the remaining multi-pass work) — yields the
full iso.

## Honesty

This is **genuine but modest**: the proof is short (it assembles existing API —
`IsGalois.card_aut_eq_finrank`, the finite-field `IsCyclic` instance, `zmodCyclicMulEquiv`) —
matching
the Pass-1/Pass-4 "genuine but light" bar — but it is a *complete* theorem, not another half, and it
is the missing per-level piece toward `≅ Ẑ`. The full `≅ Ẑ` is **not** closed here and is **not**
posited; its remaining gap (the `Ẑ`-side `lim ℤ/n` presentation + cofinal matching) is logged in
`ROADMAP.md`.

**Recovers nothing from an abstract group.** This is the structure of the Galois group of *given*
finite fields; no reach toward R1–R3. No load-bearing hypothesis (it holds for every finite `L/K`),
no `structure`/`class`, hence no rule-2 or owed-witness obligation.

## Axiom status

Standard axioms only (`#print axioms` below). Pass-7 ledger delta: **0 / 0** (no `DEBT`, no new
`FOUNDATIONAL`). The one existing `FOUNDATIONAL` entry (`residueReduction_surjective`, Pass 5) is
untouched and unused here.
-/

namespace Anabelian

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L]

/-- **The Galois group of a finite extension of finite fields is cyclic of order the degree:**
`Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L))`. This is the per-level ingredient of the
injective half of `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (the level `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n`). -/
noncomputable def galoisFiniteField_mulEquivZMod :
    Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L)) :=
  IsGalois.card_aut_eq_finrank K L ▸ (zmodCyclicMulEquiv (inferInstance : IsCyclic Gal(L/K))).symm

-- Reproducible axiom audit. Standard axioms only — no `DEBT`, no `FOUNDATIONAL` used.
#print axioms galoisFiniteField_mulEquivZMod

end Anabelian
