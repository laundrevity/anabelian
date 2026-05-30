/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueReductionRoute
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Rung L1, discharging the `DEBT`: the keystone's ring `𝒪[K̄] = integralClosure 𝒪[K] K̄` (Pass 13)

## The keystone fit-verdict (primary deliverable — route-first-step on the keystone)

The discharge of `residueReduction_surjective` applies
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` (Pass 12). Its **exact hypotheses**,
probe-verified:
`A B : CommRing`, `Algebra A B`, `[MulSemiringAction G B] [SMulCommClass G A B]`, `G` **profinite**
(`CompactSpace` + `TotallyDisconnectedSpace` + `IsTopologicalGroup`), `B` with `[TopologicalSpace
B]`
**`[DiscreteTopology B]`** `[ContinuousSMul G B]`, `(P : Ideal A) (Q : Ideal B) [Q.IsPrime]`
`[Q.LiesOver P] [Algebra.IsInvariant A B G]`; conclusion `stabilizer G Q ↠ Aut((B/Q)/(A/P))`.

**Does `𝒪[K̄]`/`Gal(K̄/K)` literally satisfy these? Two findings:**
1. **`B` must be DISCRETE** — the keystone's topology on `B` is the *algebraic* (discrete) one with
   `ContinuousSMul` meaning open stabilizers (the Krull-topology setup), **not** the valuation
   topology
   on `𝒪[K̄]`. So `B` is given the discrete topology (a free choice on the integral-closure ring);
   the
   spectral/valuation topology of Passes 11–12 is *not* what the keystone consumes. (Route
   reframing,
   not a wall.)
2. **`G = Gal(K̄/K)` profinite needs `IsGalois K (AlgebraicClosure K)`** — verified ABSENT for a
general
   field (`CompactSpace Gal(K̄/K)` fails without it; it holds when `K` is perfect, e.g. char-0 /
   mixed-
   characteristic local fields, but **not** for imperfect equal-characteristic ones like `𝔽_q((t))`,
   where `K̄/K` is inseparable). This is a genuine **route prerequisite** to track: the keystone
   discharge needs `Gal(K̄/K)` profinite, available via `[IsGalois K (AlgebraicClosure K)]`; the
   imperfect case needs the separable-closure framing (`Aut(K̄/K) ≅ Gal(K^sep/K)`) and is deferred.

## Route pivot: use `integralClosure 𝒪[K] K̄` directly (no `NormedField` bridge, no D2 diamond)

The keystone wants `B` a `CommRing` with `Algebra A B` + `Algebra.IsInvariant A B G` + the
`G`-action —
which is exactly `B = integralClosure 𝒪[K] K̄` over `A = 𝒪[K]`, **native to the
`IsNonarchimedeanLocalField`
(`ValuativeRel`) setting**. This pivots away from the Pass-11/12 `spectralNorm` route: working with
the
integral closure directly **avoids the `IsNonarchimedeanLocalField → NormedField` bridge entirely**,
and
with it the watched `NormedField`-bridge diamond (so **no D2 is incurred**). The `spectralNorm`
valuation
ring (Passes 11–12) remains a valid identification of the same object (`𝒪[K̄] = spectralIntegers K =
integralClosure 𝒪[K] K̄`) but is not on the critical path to the discharge.

## What is built (this pass — strictly-lower, axiom-free, over the exact setting)

For `K` a nonarchimedean local field (`𝒪[K]` its ring of integers, `K̄ = AlgebraicClosure K`):
* `Anabelian.galoisIntegers K` — the keystone's ring `B = 𝒪[K̄] = integralClosure 𝒪[K] K̄` (as a
  `Subring (AlgebraicClosure K)`).
* `Anabelian.isIntegral_map_galois` — every `σ ∈ Gal(K̄/K)` preserves integrality over `𝒪[K]` (it is
  `𝒪[K]`-linear via the tower `𝒪[K] → K → K̄`; `IsIntegral.map` + `AlgHom.restrictScalars`).
* `Anabelian.galoisIntegers_isInvariant` — hence `Gal(K̄/K)` acts on `𝒪[K̄]` as an
`IsInvariantSubring`,
  yielding (via `IsInvariantSubring.toMulSemiringAction`) the `MulSemiringAction (Gal(K̄/K)) 𝒪[K̄]`
  the
  keystone consumes. **Route step 1b, on the keystone's actual `B`.**

## `DEBT` status: OPEN — not discharged

The `axiom residueReduction_surjective` is **still present** (discharge ⟺ its deletion).
**Route-steps
remaining:** [Step 2: `Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal` (`𝒪[K] = 𝒪[K̄]^Gal`) + `DiscreteTopology`
+
`ContinuousSMul` + the `IsGalois K K̄` profinite prerequisite; Step 3: `Q = 𝔪[K̄]` over `P = 𝔪[K]`,
residue `𝒪[K̄]/𝔪[K̄] ≅ AlgebraicClosure 𝓀[K]`, `Aut = Gal(𝓀̄/𝓀)`, `stabilizer = ⊤`; Step 4: apply
the
keystone, **delete the axiom**]. **Nothing cardinal-sin posited** — the surjection is a present
theorem
to be *applied*, never stubbed. No new axiom; ledger unchanged at `0 FOUNDATIONAL / 1 DEBT`.

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2 obligation). D1 (ℚ-diamond) N/A (local field, no `Algebra ℚ (AC ℚ)`);
no D2 incurred (the integral-closure route avoids the `NormedField` bridge).
-/

open scoped ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The keystone's ring `B = 𝒪[K̄]`**: the integral closure of `𝒪[K]` in `K̄`, as a
`Subring (AlgebraicClosure K)`. This is the ring on which `stabilizerHom_surjective_of_profinite`
acts
to give the residue reduction `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)`. -/
noncomputable def galoisIntegers : Subring (AlgebraicClosure K) :=
  (integralClosure ↥𝒪[K] (AlgebraicClosure K)).toSubring

omit [TopologicalSpace K] in
/-- Every `σ ∈ Gal(K̄/K)` preserves integrality over `𝒪[K]` (it is `𝒪[K]`-linear via the tower
`𝒪[K] → K → K̄`). -/
theorem isIntegral_map_galois (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    {x : AlgebraicClosure K} (hx : IsIntegral ↥𝒪[K] x) : IsIntegral ↥𝒪[K] (σ x) :=
  hx.map ((σ.toAlgHom).restrictScalars ↥𝒪[K])

/-- **The absolute Galois group acts on `𝒪[K̄] = integralClosure 𝒪[K] K̄` as an invariant subring.**
Via `IsInvariantSubring.toMulSemiringAction` this provides the `MulSemiringAction (Gal(K̄/K)) 𝒪[K̄]`
that `stabilizerHom_surjective_of_profinite` consumes (route step 1b, on the keystone's actual
ring). -/
instance galoisIntegers_isInvariant :
    IsInvariantSubring (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (galoisIntegers K) where
  smul_mem σ {x} hx := by
    have hxi : IsIntegral ↥𝒪[K] x := hx
    exact hxi.map ((σ.toAlgHom).restrictScalars ↥𝒪[K])

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms isIntegral_map_galois
#print axioms galoisIntegers_isInvariant

end Anabelian
