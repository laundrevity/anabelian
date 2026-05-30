/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueReductionIntegral
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Rung L1, discharging the `DEBT`: brick 3a (`𝒪[K̄]` local), the route comparison (Pass 17)

## Where this stands

The discharge of `residueReduction_surjective` (perfect case) applies
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` to `G = Gal(K̄/K)`,
`B = 𝒪[K̄] = integralClosure 𝒪[K] K̄`, `A = 𝒪[K]`, `Q = 𝔪[K̄]`. Done: steps 1, 1b, 2a, 2b, and **3c
modulo 3a** (`galoisResidueField_isAlgClosed`: the residue field at any maximal ideal is
algebraically
closed). The last substantial gate is **3a: `𝒪[K̄]` is local**, so that `𝔪[K̄]` is *the* maximal
ideal
(the unique prime over `𝔪[K]`, making `Q = 𝔪[K̄]` Galois-invariant ⟹ `stabilizer = ⊤`, and feeding
3c).

## The 3a route comparison — by estimated pass-count, across three routes (Pass-17 primary)

Pass 16 compared two routes by binary absent/present. This pass probed **three** routes and
estimated
each by **relative pass-count** (the target is *local-ness*, an `IsLocalRing` with maximal ideal the
valuation's `𝔪[K̄]` — NOT necessarily the full `ValuationRing` structure):

- **(i) native `ValuationRing`.** `integralClosure 𝒪[K] K̄` is a `ValuationRing` (⟹ `IsLocalRing`
  free
  via `ValuationRing.isLocalRing`), needing the unique-extension-of-the-valuation-to-`K̄` theory.
  Probe: `ValuativeExtension` (`ValuativeRel/Basic.lean:1292`) is **compatibility-only** — it
  assumes
  `[ValuativeRel B]` already and does **not** construct the `ValuativeRel`/valuation on `K̄`. No
  canonical `ValuativeRel (AlgebraicClosure K)`. So this is the full from-scratch extension theory.
  **Estimate: ~3 passes, no D2.**
- **(ii) `spectralNorm` (carries a tracked D2).** `Valued.integer K̄` for the spectral `Valued` on
  `K̄`
  is a `ValuationRing` ⟹ `IsLocalRing` **for free** (`ValuationSubring` → `ValuationRing` →
  `IsLocalRing`); `Padics/Complex.lean` is the exact template (`spectralNorm.normedField`,
  `NormedField.toValued`, `Valued … ℝ≥0` on the *non-complete* `AlgebraicClosure`). The only real
  work
  is the **bridge** `integralClosure 𝒪[K] K̄ = Valued.integer K̄`, i.e.
  `spectralNorm x ≤ 1 ↔ IsIntegral 𝒪[K] x` — and Pass 16's "absent" was **wrong**: it is reachable
  via
  `spectralNorm y = spectralValue (minpoly K y)` (`SpectralNorm.lean:379`) +
  **`spectralValue_le_one_iff`**
  (`:202`, monic ⟹ `≤ 1 ↔ all coeffs norm ≤ 1`) + this pass's algebraic brick (coeffs in `𝒪[K]` ↔
  integral). Cost: the bridge (~1 pass) + the D2 setup (`NormedField K`/`RankOne` on the local
  field,
  the `Padics`/`LocalField.Basic` pattern). **Estimate: ~2 passes + a tracked D2.**
- **(iii) Henselian-local-direct.** `𝒪[K]` is Henselian (complete ⟹ Henselian); the integral closure
  of a Henselian local ring in an algebraic extension is local. Probe: `HenselianLocalRing` exists
  (`Henselian.lean:108`) but `grep Henselian` hits **only that one file** — its `TFAE` is
  root-lifting
  only, with **no** integral-closure-local clause; even `HenselianLocalRing 𝒪[K]` does not
  synthesize.
  So this needs: `𝒪[K]` Henselian (some work) + integral-closure-in-finite-extension local (absent,
  from TFAE) + a filtered colimit to `K̄` (absent). **Estimate: ~2–3 passes, no D2.**

**Decision: route (ii), incur the tracked D2.** By the cost principle — a tracked **D2** instance
diamond is a *bounded, documented, fix-once* hygiene debt (logged like D1), **cheaper than the 2–3
passes of from-scratch foundational valuation/Henselian theory** that (i)/(iii) require — route (ii)
is
**materially shortest** (~2 passes) because local-ness is *free* (`Valued.integer` is a
  `ValuationRing`)
and the bridge is *reachable* (`spectralValue_le_one_iff`). **This reverses Pass 16's "stay
native"**,
legitimately and on new evidence: Pass 16 grepped only `spectralNorm.*le_one` and missed
`spectralValue_le_one_iff`, and had not found that `Valued.integer` gives local-ness for free — so
its
magnitude estimate for (ii) was wrong. This is a magnitude decision, **not** a D2-reflex (the
opposite
direction from Pass 16).

## Built this pass — the algebraic half of route (ii)'s bridge (D2-free, strictly-lower)

* `isIntegral_iff_minpoly_coeff_mem` — for `x : K̄`, `IsIntegral 𝒪[K] x ↔ ∀ i, (minpoly K x).coeff i
  ∈
  𝒪[K]`. The forward direction is `minpoly.isIntegrallyClosed_eq_field_fractions` (`𝒪[K]` integrally
  closed, `K = Frac 𝒪[K]`, so `minpoly K x` is the base-changed `minpoly 𝒪[K] x`); the reverse lifts
  `minpoly K x` to a monic poly over `𝒪[K]` via `Polynomial.toSubring`. This is the **algebraic
  core**
  of the bridge `integralClosure 𝒪[K] K̄ = {x | spectralNorm x ≤ 1}`: the remaining (D2-incurring)
  half
  is `coeff ∈ 𝒪[K] ↔ ‖coeff‖ ≤ 1` (norm↔valuation) chained through `spectralValue_le_one_iff`. It is
  **D2-free** — incurring D2 is deferred to exactly the step that needs the norm.

  Note local-ness genuinely **cannot** be finished purely algebraically: an integral `x` is a unit
  iff
  the constant coeff of `minpoly K x` is a unit in `𝒪[K]`, but showing the non-units form an *ideal*
  (closed under `+`) needs the multiplicative, ultrametric `spectralNorm` (= max over conjugates) —
  the
  structure that makes `Valued.integer K̄` a valuation ring. Hence route (ii)'s D2 is not avoidable.

## `DEBT` status: OPEN — not discharged

The `axiom residueReduction_surjective` is **still present**. Brick **3a is in progress** (this pass
chose route (ii) and built the bridge's algebraic half). **Route-steps remaining: [3a via route
(ii):
(a) D2 setup — `NormedField K`/`RankOne`/`spectralNorm.normedField K K̄` ⟹ `Valued K̄ ℝ≥0`, ⟹
`IsLocalRing (Valued.integer K̄)` free; (b) the norm half of the bridge `‖coeff‖ ≤ 1 ↔ coeff ∈ 𝒪[K]`
+
`spectralValue_le_one_iff` ⟹ `integralClosure 𝒪[K] K̄ = Valued.integer K̄`; (c) transport ⟹
`IsLocalRing (integralClosure 𝒪[K] K̄)` = 3a]; 3b residue algebraic; 3d/3e (supported); Step 4 apply
keystone + delete axiom (perfect-case narrowing)].** Done: 1, 1b, 2a, 2b, 3c-modulo-3a, **bridge
algebraic half (this pass)**. **Nothing cardinal-sin posited** — 3a is being *built*, not stubbed;
no
`DEBT` posits `𝒪[K̄]` local / a `ValuationRing` / the residue iso. Ledger unchanged at
`0 FOUNDATIONAL / 1 DEBT`.

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2). D1 N/A; **D2 not yet incurred this pass** (the algebraic-half brick
is
norm-free) but **decided to be incurred** for 3a's spectral steps (a)/(b) next pass — logged, not
silent.
-/

open Polynomial

namespace Anabelian

open scoped ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- **Algebraic half of route (ii)'s bridge.** For `x : K̄`, membership in `𝒪[K̄] = integralClosure
𝒪[K] K̄` (i.e. integrality over `𝒪[K]`) is equivalent to the `K`-minimal polynomial of `x` having
all
coefficients in `𝒪[K]`. Forward: `𝒪[K]` is integrally closed with `K = Frac 𝒪[K]`, so `minpoly K x`
is the base change of `minpoly 𝒪[K] x` (`minpoly.isIntegrallyClosed_eq_field_fractions`). Reverse:
lift `minpoly K x` to a monic polynomial over `𝒪[K]` (`Polynomial.toSubring`). Norm-free, hence
D2-free;
the algebraic core of `integralClosure 𝒪[K] K̄ = {x | spectralNorm x ≤ 1}`. -/
theorem isIntegral_iff_minpoly_coeff_mem (x : AlgebraicClosure K) :
    IsIntegral ↥𝒪[K] x ↔ ∀ i, (minpoly K x).coeff i ∈ (𝒪[K] : Subring K) := by
  have halg : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  constructor
  · intro hx i
    have hmap : minpoly K x = (minpoly ↥𝒪[K] x).map (algebraMap ↥𝒪[K] K) :=
      minpoly.isIntegrallyClosed_eq_field_fractions K (AlgebraicClosure K) hx
    rw [hmap, coeff_map]
    exact (minpoly ↥𝒪[K] x).coeff i |>.2
  · intro h
    have hsub : (↑(minpoly K x).coeffs : Set K) ⊆ (𝒪[K] : Subring K) := by
      intro a ha
      rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact h i
    refine ⟨(minpoly K x).toSubring (𝒪[K] : Subring K) hsub,
      (Polynomial.monic_toSubring _ _ _).mpr (minpoly.monic halg), ?_⟩
    show aeval x _ = 0
    rw [← Polynomial.aeval_map_algebraMap K x,
        show algebraMap ↥𝒪[K] K = (𝒪[K] : Subring K).subtype from rfl,
        Polynomial.map_toSubring]
    exact minpoly.aeval K x

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms isIntegral_iff_minpoly_coeff_mem

end Anabelian
