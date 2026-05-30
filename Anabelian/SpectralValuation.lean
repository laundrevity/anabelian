/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Rung L1, discharging the one boundary: the spectral valuation ring `𝒪[K̄]` (Pass 11, route (a))

## The inflection decision this file embodies

Pass 10 closed `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`, the first L1 whole of depth. Pass 11 is an **inflection
decision**
(Pass-5-style): a banked milestone invites *breadth-without-depth* — opening clean fragments while
the
one boundary `residueReduction_surjective` (Pass 5) sits undischarged. The decision, documented
before
code, is **route (a): begin discharging that boundary**, not (b) open an independent sub-target.

**Why (a), driven by the common-prerequisite finding + a tractability correction:** the valuation on
`K̄` is the *common gate* for both routes — (a) needs it for the residue field `𝓀[K̄]` and the
reduction
map; (b)'s ramification groups `G_i` are defined *via* the valuation and the unramified/tame/wild
filtration sits *on* the residue reduction (and that filtration machinery is **absent** from
Mathlib).
So (b) is no independent escape. And **Pass 6's "valuation on `K̄` irreducibly absent" was wrong**:
`spectralNorm.normedField` + `NormedField.toValued` give `Valued K̄ ℝ≥0` (cf. `NumberTheory/Padics/`
`Complex.lean`, which does exactly this for `ℂ_p`), whence `𝒪[K̄]`/`𝓀[K̄]`; and `Krasner.lean`'s
`IsKrasner` is the lifting machinery. The valuation on `K̄` is therefore the **highest-leverage
strictly-lower brick**, and this file builds its foundation.

## What is built (the first strictly-lower brick, axiom-free)

For a nonarchimedean normed field `K` (the natural home of `spectralNorm`):

* `Anabelian.spectralIntegers K : Subring (AlgebraicClosure K)` — the **spectral valuation ring**
  `𝒪[K̄] = {x | spectralNorm K K̄ x ≤ 1}` (closed unit ball). A subring because `spectralNorm` is
  nonarchimedean (`isNonarchimedean_spectralNorm`) and submultiplicative (`spectralNorm_mul`).
* `Anabelian.spectralIntegers_mem_iff_galois` — **the absolute Galois group preserves `𝒪[K̄]`**:
every
  `σ ∈ Gal(K̄/K)` is an isometry for the spectral norm (`spectralNorm_eq_of_equiv`), so `σ x ∈
  𝒪[K̄]`
  iff `x ∈ 𝒪[K̄]`. This is the setup for the residue reduction `Gal(K̄/K) → Aut 𝓀[K̄]`.

## Honesty: this is the FIRST brick, not the discharge

This does **not** discharge `residueReduction_surjective`; it builds the foundational valuation ring
it
needs. Graded as **strictly-lower infrastructure** (axiom-free), genuinely on the discharge path
(not
adjacent: the valuation on `K̄` gates the whole route). **Nothing is posited** — in particular the
*lifting/surjectivity* (the irreducible heart, whose positing would be the cardinal sin) is
untouched.
The remaining route (logged in `AXIOM_LEDGER.md` / `ROADMAP.md`): bridge `IsNonarchimedeanLocalField
K`
→ `NormedField K` (`ValuativeRel → Valued → RankOne → Valued.toNormedField`) → this valuation on
`K̄` →
residue field `𝓀[K̄]` (via `NormedField.toValued`) → the reduction map → lifting (`IsKrasner` +
maximal-unramified) → surjectivity. On the strength of this begun construction + the corrected
tractability, `residueReduction_surjective` is **reclassified `FOUNDATIONAL → DEBT`** this pass (see
the
Reclassification log) — a genuine commitment to discharge in-project, not a paper relabel.

**Recovers nothing from an abstract group.** No new `structure`/`class` (so no rule-2 obligation);
the
only hypotheses are the genuine `[NormedField K] [IsUltrametricDist K]` that `spectralNorm`
requires.

## Axiom status

Standard axioms only (`#print axioms` below). Pass-11 ledger delta on *this file*: **0 axioms**
(strictly-lower, axiom-free). The pass's overall ledger move is the `FOUNDATIONAL → DEBT`
reclassification of `residueReduction_surjective` (no new axiom; `1 FOUNDATIONAL / 0 DEBT` becomes
`0 FOUNDATIONAL / 1 DEBT`).
-/

open Polynomial

namespace Anabelian

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The spectral valuation ring `𝒪[K̄]`** of the algebraic closure of a nonarchimedean normed
field
`K`: the closed unit ball `{x | spectralNorm K K̄ x ≤ 1}`. It is a subring because the spectral norm
is
nonarchimedean (`isNonarchimedean_spectralNorm`) and submultiplicative (`spectralNorm_mul`). -/
noncomputable def spectralIntegers : Subring (AlgebraicClosure K) where
  carrier := {x | spectralNorm K (AlgebraicClosure K) x ≤ 1}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    calc spectralNorm K (AlgebraicClosure K) (x * y)
        ≤ spectralNorm K (AlgebraicClosure K) x * spectralNorm K (AlgebraicClosure K) y :=
          spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic x) (Algebra.IsAlgebraic.isAlgebraic y)
      _ ≤ 1 := mul_le_one₀ hx (spectralNorm_nonneg _) hy
  one_mem' := by simp only [Set.mem_setOf_eq, spectralNorm_one, le_refl]
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    exact le_trans (isNonarchimedean_spectralNorm x y) (max_le hx hy)
  zero_mem' := by simp only [Set.mem_setOf_eq, spectralNorm_zero]; norm_num
  neg_mem' {x} hx := by
    simp only [Set.mem_setOf_eq, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic x)] at *
    exact hx

/-- Membership in `𝒪[K̄]` is exactly `spectralNorm ≤ 1`. -/
theorem mem_spectralIntegers (x : AlgebraicClosure K) :
    x ∈ spectralIntegers K ↔ spectralNorm K (AlgebraicClosure K) x ≤ 1 := Iff.rfl

/-- **The absolute Galois group preserves the spectral valuation ring `𝒪[K̄]`.** Every
`σ ∈ Gal(K̄/K)` is an isometry for the spectral norm (`spectralNorm_eq_of_equiv`), so it maps
`𝒪[K̄]`
onto itself. This is the foundation of the residue reduction `Gal(K̄/K) → Aut 𝓀[K̄]`. -/
theorem spectralIntegers_mem_iff_galois (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (x : AlgebraicClosure K) : σ x ∈ spectralIntegers K ↔ x ∈ spectralIntegers K := by
  rw [mem_spectralIntegers, mem_spectralIntegers, ← spectralNorm_eq_of_equiv σ x]

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms spectralIntegers
#print axioms spectralIntegers_mem_iff_galois

end Anabelian
