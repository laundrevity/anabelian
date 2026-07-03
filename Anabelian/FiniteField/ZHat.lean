/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.FiniteField.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Rung L1, toward `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`: the surjection `Ẑ ↠ Gal(𝔽_q̄/𝔽_q)`

This is the **discipline-inversion** pass (Pass 6). After Pass 5 made the project's first
`FOUNDATIONAL` entry, the avoidance to rule out is **`FOUNDATIONAL`-stacking**: importing a fresh
boundary for each hard sub-target and piling structure on a growing tower of posits — a slow replay
of IUT Stage-1. The metric guard (`CLAUDE.md` rule 3): a rising `FOUNDATIONAL` count is not
progress.
So this pass adds **no** boundary; it does real, axiom-free structural work.

## The decision: (Z), axiom-free, no new boundary

Of the two permitted routes — (A) discharge the Pass-5 boundary `residueReduction_surjective` into a
theorem on strictly-lower `DEBT`, and (Z) the `≅ Ẑ` residue-side identification axiom-free —
inventory
(Pass 6 `NOTES.md`) found (A) **blocked**: the surjection's content *is* the unramified↔residue
correspondence, whose lifting step is irreducibly absent (no maximal-unramified extension / `K^ur`),
so no clean strictly-lower `DEBT` exists without the cardinal sin, and the infrastructure below it
needs the (absent) valuation on `K̄`. So we take **(Z)**.

## What is proved (axiom-free; ledger stays `1 FOUNDATIONAL / 0 DEBT`)

`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (the profinite completion of `ℤ`) is the classical structure of a finite field's
absolute Galois group. Pass 2 proved it **procyclic** (Frobenius topologically generates). Here we
build the actual map of the classical iso and prove its **surjective half**:

* `Anabelian.ZHat` — `Ẑ`, the profinite completion of `ℤ` (`ProfiniteGrp.completion`).
* `Anabelian.zhatToGalois` — the canonical continuous hom `Ẑ → Gal(K̄/K)` for a finite field `K`,
  from the profinite-completion **universal property** applied to `n ↦ Frobⁿ`.
  (`Gal(AlgebraicClosure K/K) = Field.absoluteGaloisGroup K`.)
* `Anabelian.zhatToGalois_etaFn` — it sends the image of `n` to `Frobⁿ` (the defining property).
* `Anabelian.zhatToGalois_surjective` — **it is surjective**: its range is closed (continuous image
  of the compact `Ẑ`) and contains the powers of Frobenius, dense by Pass 2; closed + dense ⟹ all.

This is the **surjective half** of `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` — the structural analogue of Pass 4's
*injective* half of the residue reduction.

## Honesty: genuine, not a fragment; what remains

Not a light fragment: it is the actual map of the classical iso, built via the profinite-completion
universal property (`ProfiniteGrp.ProfiniteCompletion.lift`) — beyond Pass 2's bare procyclic
generation. The **full iso** `≅ Ẑ` needs the remaining **injective** half (equivalently the finite
quotients `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n` matching the inverse system of `Ẑ`); that is genuinely multi-pass
and is logged as the remaining L1 work in `ROADMAP.md`.

**Recovers nothing from an abstract group.** This is the structure of the Galois group of a *given*
finite field; no reach toward R1–R3.

## Axiom status

Standard axioms only (`#print axioms` below). Pass-6 ledger delta: **0 / 0**. The one existing
`FOUNDATIONAL` entry (`residueReduction_surjective`, Pass 5) is untouched and unused here.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion

namespace Anabelian

/-- `Ẑ`, the profinite completion of `ℤ` (as the completion of its multiplicative copy). -/
noncomputable abbrev ZHat : ProfiniteGrp := completion (GrpCat.of (Multiplicative ℤ))

variable (K : Type) [Field K] [Fintype K]

/-- The residue Galois group `Gal(K̄/K)` of a finite field, as a `ProfiniteGrp`. -/
noncomputable abbrev galoisProfinite : ProfiniteGrp := ProfiniteGrp.of (Gal(AlgebraicClosure K/K))

/-- `n ↦ Frobⁿ`, as a homomorphism `Multiplicative ℤ → Gal(K̄/K)` in `GrpCat`. -/
noncomputable def frobeniusGrpHom : GrpCat.of (Multiplicative ℤ) ⟶ GrpCat.of (galoisProfinite K) :=
  GrpCat.ofHom (zpowersHom _ (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)))

/-- The canonical continuous homomorphism `Ẑ → Gal(K̄/K)` of a finite field `K`, from the
profinite-completion universal property applied to `n ↦ Frobⁿ`. -/
noncomputable def zhatToGalois : ZHat ⟶ galoisProfinite K := lift (frobeniusGrpHom K)

/-- The canonical map sends the image of `n : ℤ` to the `n`-th power of Frobenius. -/
theorem zhatToGalois_etaFn (n : Multiplicative ℤ) :
    (Hom.hom (zhatToGalois K)) (etaFn _ n) =
      FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ (Multiplicative.toAdd n) :=
  DFunLike.congr_fun (congrArg GrpCat.Hom.hom (lift_eta (frobeniusGrpHom K))) n

/-- **The canonical map `Ẑ ↠ Gal(𝔽_q̄/𝔽_q)` is surjective** — the surjective half of
`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`. Its range is closed (continuous image of the compact `Ẑ`) and contains the
powers of Frobenius, dense by Pass 2; a closed dense set is everything. -/
theorem zhatToGalois_surjective : Function.Surjective ⇑(Hom.hom (zhatToGalois K)) := by
  have hclosed : IsClosed (Set.range ⇑(Hom.hom (zhatToGalois K))) :=
    (isCompact_range (Hom.hom (zhatToGalois K)).continuous).isClosed
  have hsub : (Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) :
      Set (Gal(AlgebraicClosure K/K))) ⊆ Set.range ⇑(Hom.hom (zhatToGalois K)) := by
    rintro _ ⟨m, rfl⟩
    exact ⟨etaFn _ (Multiplicative.ofAdd m), by rw [zhatToGalois_etaFn]; rfl⟩
  have hdense : Dense (Subgroup.zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic K
      (AlgebraicClosure K)) : Set (Gal(AlgebraicClosure K/K))) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe,
        Anabelian.frobenius_topologicalClosure_eq_top K, Subgroup.coe_top]
  rw [← Set.range_eq_univ]
  exact hclosed.closure_eq ▸ (hdense.mono hsub).closure_eq

-- Reproducible axiom audit. All standard axioms only — no `DEBT`, no `FOUNDATIONAL` used.
#print axioms zhatToGalois_etaFn
#print axioms zhatToGalois_surjective

end Anabelian
