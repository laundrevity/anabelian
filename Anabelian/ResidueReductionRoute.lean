/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.SpectralValuation
import Mathlib.RingTheory.Invariant.Profinite

/-!
# Rung L1, route (a): the lifting is NOT a wall — the keystone is present (Pass 12)

## The primary deliverable: the lifting-tractability verdict

Pass 11 began discharging the one `DEBT` (`residueReduction_surjective`) and flagged the **lifting**
— "every residue automorphism lifts to `Gal(K̄/K)`", the heart of the surjection, which Pass 6
called
"irreducibly absent" — as the unverified hard step. **This pass front-loads that uncertainty and the
verdict is decisive: the lifting is NOT a wall, and the maximal-unramified / `K^ur` edifice is NOT
needed.** Mathlib already proves the residue-reduction surjectivity in the profinite setting:

* **`Ideal.Quotient.stabilizerHom_surjective_of_profinite`**
(`Mathlib/RingTheory/Invariant/Profinite.lean`)
  — for a **profinite group `G` acting continuously** on a (discrete) commutative ring `B` over `A`,
  with `Algebra.IsInvariant A B G` and `Q` a prime of `B` over `P` of `A`, the decomposition group
  `stabilizer G Q` **surjects onto** `Aut((B/Q)/(A/P))` (the residue-field automorphisms). It is
  assembled from the finite level (`stabilizerHom_surjective` / `exists_of_isInvariant`, the
  arithmetic
  Frobenius) via exactly the profinite limit machinery used to close `≅ Ẑ`
  (`isoLimittoFiniteQuotientFunctor`, `exist_openNormalSubgroup_sub_open_nhds_of_one`).

This is **the surjection** `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)` (with `stabilizer = ⊤` since the maximal ideal of
`𝒪[K̄]` is the unique prime over `𝔪[K]`). So the discharge is **reachable via a bounded sequence of
strictly-lower bricks** — not a multi-pass maximal-unramified construction. (Corrects Pass 6's
"irreducibly absent" *and* Pass 11's route, which had assumed `IsKrasner` + maximal-unramified for
the
lifting; `IsKrasner` is in fact field-*generation*, not Galois-lifting, and is not needed here.)

## Revised discharge route (keystone PRESENT; `DEBT` still open)

To discharge `residueReduction_surjective` (over `IsNonarchimedeanLocalField K`), apply
`stabilizerHom_surjective_of_profinite` with `G = Gal(K̄/K)`, `B = 𝒪[K̄]` (the valuation ring =
integral closure of `𝒪[K]` in `K̄`), `A = 𝒪[K]`, `Q = 𝔪[K̄]`, `P = 𝔪[K]`. Steps:
- **Step 1 ✅ (Pass 11):** the valuation ring `𝒪[K̄]` (`spectralIntegers`) + `Gal(K̄/K)` preserves
it.
- **Step 1b ✅ (Pass 12, this file):** the Galois **`MulSemiringAction` on `𝒪[K̄]`**
  (`spectralIntegers_isInvariant` ⟹ `IsInvariantSubring.toMulSemiringAction`) — the
  `MulSemiringAction
  G B` the keystone consumes.
- **Step 2 (remaining):** the `𝒪[K]`-algebra / `Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal` framing with
  discrete `B` + `ContinuousSMul` (the keystone's hypotheses); likely cleanest via
  `integralClosure 𝒪[K] (AlgebraicClosure K)` (ring-theoretic, no `spectralNorm` needed there) with
  `𝒪[K̄] = spectralIntegers` as the valuation-ring identification.
- **Step 3 (remaining):** `Q = 𝔪[K̄]` over `P = 𝔪[K]`; residue `B/Q ≅ 𝓀̄`, `A/P = 𝓀[K]`,
  `Aut((B/Q)/(A/P)) = Gal(𝓀̄/𝓀)`; `stabilizer G Q = ⊤`.
- **Step 4 (remaining — KEYSTONE PRESENT):** apply `stabilizerHom_surjective_of_profinite`;
reinterpret
  as `Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K]` surjective — discharging the
  `axiom` (deleting it, replacing with a `theorem`). **Until that deletion, the `DEBT` stays open.**

## What is built this pass (Step 1b, strictly-lower, axiom-free)

* `Anabelian.spectralIntegers_isInvariant` — `Gal(K̄/K)` acts on `𝒪[K̄]` as an invariant subring
  (`IsInvariantSubring`), from Pass 11's `spectralIntegers_mem_iff_galois`. Via
  `IsInvariantSubring.toMulSemiringAction` this yields the `MulSemiringAction (Gal(K̄/K)) 𝒪[K̄]`
  that
  the keystone's setup requires — a genuine, strictly-lower, on-route brick.

**Nothing cardinal-sin posited:** the surjection/lifting is **not** stubbed — it is supplied by a
present Mathlib theorem, to be *applied* (not posited) in a later pass. No new axiom. The one `DEBT`
(`residueReduction_surjective`) remains **open**, not discharged (its `axiom` is still present).

## `DEBT` status

**Open. Route-steps remaining: [Step 2: `IsInvariant` integral-closure framing; Step 3: residue
identification `𝓀̄/𝓀` + `stabilizer = ⊤`; Step 4: apply the present keystone].** Single `DEBT`
(`residueReduction_surjective`); no new axiom introduced; ledger unchanged at `0 FOUNDATIONAL / 1
DEBT`.

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2 obligation).
-/

namespace Anabelian

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The absolute Galois group acts on `𝒪[K̄]` as an invariant subring** (Pass 12, route step 1b).
From Pass 11's `spectralIntegers_mem_iff_galois`. Via `IsInvariantSubring.toMulSemiringAction` this
provides the `MulSemiringAction (Gal(K̄/K)) 𝒪[K̄]` that `stabilizerHom_surjective_of_profinite`
consumes. -/
instance spectralIntegers_isInvariant :
    IsInvariantSubring (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (spectralIntegers K) where
  smul_mem σ {x} hx := (spectralIntegers_mem_iff_galois K σ x).mpr hx

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms spectralIntegers_isInvariant

end Anabelian
