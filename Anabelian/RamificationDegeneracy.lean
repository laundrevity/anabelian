/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.GaloisInertia

/-!
# Rung L2 opening verdict: naive lower numbering on `Gal(K̄/K)` is DEGENERATE — proved (Pass 22)

The planned L2 opening move was: define the lower-numbering ramification filtration directly on the
absolute Galois group as `G_i := (𝔪[K̄]^(i+1)).inertia Gal(K̄/K)` (the same `Ideal.inertia` device
as Pass 21's `G_0 = galoisInertia`), then prove antitonicity/normality. **This pass refutes that
plan before committing it**: the filtration is *degenerate* — `G_i = G_0` for every `i` — because

* `maximalIdeal_galoisIntegers_sq` — **`𝔪[K̄]² = 𝔪[K̄]`**: the maximal ideal of `𝒪[K̄]` is
  idempotent. `K̄` is algebraically closed, so every `x ∈ 𝔪[K̄]` has a square root `y` in `K̄`;
  `y` is integral (root of the monic `T² − x`), hence in `𝒪[K̄]`; `y` is a non-unit (else `x = y²`
  would be a unit), hence in `𝔪[K̄]`; so `x = y·y ∈ 𝔪[K̄]²`. (Value-theoretically: the value group
  of `K̄` is divisible, so there is no smallest positive valuation.)
* `maximalIdeal_galoisIntegers_pow_eq` — hence `𝔪[K̄]^n = 𝔪[K̄]` for every `n ≠ 0`.
* `inertia_maximalIdeal_pow_collapse` — hence `(𝔪[K̄]^(i+1)).inertia Gal(K̄/K) = galoisInertia K`
  for every `i`: **the would-be `G_i` all coincide with `G_0`.**

## Why this is the deliverable, not a detour

This is the rule-2 discipline working *before* a vacuous definition is committed rather than after:
a `G_i` defined this way would compile, and its "theorems" (antitone, normal) would all hold —
**vacuously**, since the groups never come apart for distinct `i`. The degeneracy is here *proved*
axiom-free (a constructible failure, the project's currency), not merely asserted.

## The corrected L2 architecture (Serre, *Local Fields*, ch. IV)

Classically the lower-numbering filtration is defined for **finite** Galois extensions `L/K`
(where `𝒪_L` is a DVR — powers of `𝔪_L` strictly decrease), via
`G_i(L/K) = {σ | ∀ x ∈ 𝒪_L, σx − x ∈ 𝔪_L^(i+1)}` — `Ideal.inertia` is still the right device,
*at finite level*. Lower numbering is **not** compatible with passing to the inverse limit
(precisely the degeneracy proved here, seen from the other side); the filtration of the *absolute*
group is the **upper numbering** `G^v`, obtained from the finite levels via the Herbrand function
`φ`/`ψ` and quotient-compatibility. So the honest L2 ladder is: (1) finite-level `G_i(L/K)` over a
DVR + its basic theory; (2) Herbrand `φ`/`ψ` and upper numbering at finite level; (3) the limit
`G^v ≤ Gal(K̄/K)`. Mathlib has none of this (re-verified Pass 22: `RamificationGroup.lean` is still
definition-only — decomposition/inertia only; no filtration, no Herbrand function); the gaps are
logged in `ROADMAP.md`, not stubbed.

## Honesty: what this is and is NOT

A short, real, axiom-free refutation plus the corrected dependency map — in the tradition of the
Pass-13 fit-verdict and Pass-16/17 route decisions: the cheapest possible pass that prevents a
wrong (vacuous) foundation for L2. It proves a genuine structural fact about `𝒪[K̄]` (idempotent
maximal ideal) that is also independently useful (e.g. it shows `𝒪[K̄]` is not Noetherian and has
no uniformizer — the concrete reason "DVR-style" arguments must stay at finite level).

**Not reconstruction.** A fact about a given field's integers; no reach toward R1–R3.

**No new owed witness, no new `structure`/`class`.** Nothing here claims a load-bearing
hypothesis; the pass *discharges* (preemptively) the come-apart obligation a naive `G_i`
definition would have incurred and failed.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
D1 N/A; D2 unchanged (no valuation on `K̄` appears in any statement).
-/

open scoped ValuativeRel Pointwise

namespace Anabelian

open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local instance] isLocalRing_galoisIntegers

/-- **The maximal ideal of `𝒪[K̄]` is idempotent: `𝔪[K̄]² = 𝔪[K̄]`.** Every `x ∈ 𝔪[K̄]` has a
square root `y ∈ K̄` (algebraically closed); `y` is integral over `𝒪[K̄]` (monic `T² − x`) hence
lies in `𝒪[K̄]` (transitivity of integrality); `y` is a non-unit (a unit's square is a unit), so
`y ∈ 𝔪[K̄]` (local), and `x = y·y ∈ 𝔪[K̄]²`. Value-theoretically: the value group of `K̄` is
divisible, so no element of `𝔪[K̄]` has minimal positive valuation. Consequences: `𝒪[K̄]` is not
Noetherian, has no uniformizer, and the powers of `𝔪[K̄]` do not filter anything
(`maximalIdeal_galoisIntegers_pow_eq`). -/
theorem maximalIdeal_galoisIntegers_sq :
    maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) ^ 2 =
      maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := by
  set B := ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) with hB
  refine le_antisymm (Ideal.pow_le_self two_ne_zero) ?_
  intro x hx
  -- a square root of `x` in the algebraically closed `K̄`
  obtain ⟨y, hy2⟩ := IsAlgClosed.exists_pow_nat_eq (k := AlgebraicClosure K)
    (x : AlgebraicClosure K) (n := 2) two_pos
  -- `y` is integral over `𝒪[K̄]` (monic `T² − x`), hence over `𝒪[K]`, hence in `𝒪[K̄]`
  have hyB : IsIntegral B y :=
    ⟨Polynomial.X ^ 2 - Polynomial.C x, Polynomial.monic_X_pow_sub_C x two_ne_zero, by
      simp [hy2, sub_eq_zero]; rfl⟩
  haveI : Algebra.IsIntegral ↥𝒪[K] B := integralClosure.AlgebraIsIntegral
  have hy0 : IsIntegral ↥𝒪[K] y := isIntegral_trans _ hyB
  have hymem : y ∈ integralClosure ↥𝒪[K] (AlgebraicClosure K) := hy0
  set Y : B := ⟨y, hymem⟩ with hYdef
  have hYsq : Y ^ 2 = x := by
    apply Subtype.ext
    exact hy2
  -- `Y` is a non-unit (else `x = Y²` would be a unit), so `Y ∈ 𝔪[K̄]`
  have hxnu : ¬ IsUnit x := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx)
  have hYm : Y ∈ maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hxnu (hYsq ▸ hu.pow 2)
  have hx2 : x ∈ maximalIdeal B * maximalIdeal B := by
    rw [← hYsq, pow_two]
    exact Ideal.mul_mem_mul hYm hYm
  rwa [pow_two]

/-- `𝔪[K̄]^n = 𝔪[K̄]` for every `n ≠ 0` — the powers of the maximal ideal of `𝒪[K̄]` collapse
(induction from `maximalIdeal_galoisIntegers_sq`). -/
theorem maximalIdeal_galoisIntegers_pow_eq {n : ℕ} (hn : n ≠ 0) :
    maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) ^ n =
      maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih (Nat.succ_ne_zero k), ← pow_two, maximalIdeal_galoisIntegers_sq]

/-- **The naive lower-numbering ramification filtration on `Gal(K̄/K)` is DEGENERATE** — the
would-be `G_i := (𝔪[K̄]^(i+1)).inertia Gal(K̄/K)` equals `G_0 = galoisInertia K` for *every* `i`.
This is the proved-failure verdict that rules out defining lower numbering directly on the
absolute Galois group: a `G_i` so defined would pin nothing (no two of them ever come apart).
The classical filtration lives at finite levels `L/K` (DVR), with the absolute-group filtration
in *upper* numbering via Herbrand — see the module docstring and `ROADMAP.md` (L2). -/
theorem inertia_maximalIdeal_pow_collapse (i : ℕ) :
    (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) ^ (i + 1)).inertia
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) = galoisInertia K := by
  rw [maximalIdeal_galoisIntegers_pow_eq K i.succ_ne_zero]
  rfl

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms maximalIdeal_galoisIntegers_sq
#print axioms maximalIdeal_galoisIntegers_pow_eq
#print axioms inertia_maximalIdeal_pow_collapse

end Anabelian
