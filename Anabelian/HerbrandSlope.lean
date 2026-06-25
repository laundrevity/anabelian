/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.HerbrandFunction
import Mathlib

/-!
# The ascent: the slope of the Herbrand function `φ'(u) = 1/(G_0 : G_u)` (Pass 47)

The **defining derivative property** of the Herbrand function (Serre, *Local Fields*, IV §3): on
each open interval `(n, n+1)`, `φ` is affine with slope `|G_{n+1}|/|G_0| = 1/(G_0 : G_u)`. We prove
it directly from the integral definition `φ(u) = ∫_0^u dt/(G_0 : G_t)` by the **fundamental theorem
of calculus**: the integrand is locally constant away from the integer breakpoints, so it is
continuous there, and FTC differentiates the primitive.

> **`herbrandPhi_hasDerivAt_Ioo`** — for `u ∈ (n, n+1)`,
> `HasDerivAt (herbrandPhi K A) (|G_{n+1}| / |G_0|) u`.

## What is proved (all axiom-free)

* `herbrandPhiSeq_hasDerivAt_Ioo` / `herbrandPhiSeq_hasDerivAt_neg` — abstractly (on an order
  sequence `g`): `HasDerivAt φ (g_{n+1}/g_0) u` for `u ∈ (n, n+1)`, and `HasDerivAt φ 1 u` for
  `u < 0` (where `φ = id`). Each via `intervalIntegral.integral_hasDerivAt_right`, the integrand
  being `EventuallyEq` to a constant near `u` (`Nat.floor` is locally constant off the integers).
* `herbrandPhiSeq_deriv_Ioo` / `herbrandPhiSeq_deriv_neg` — the `deriv` form.
* `herbrandPhi_hasDerivAt_Ioo` / `herbrandPhi_hasDerivAt_neg` and their `deriv` forms — the
  instantiation: `φ'_{L/K}(u) = |G_{n+1}|/|G_0|` for `u ∈ (n, n+1)`, i.e. `1/(G_0 : G_u)` since
  `G_u = G_{⌈u⌉} = G_{n+1}` and `|G_{n+1}|/|G_0| = (G_0 : G_{n+1})⁻¹` (Lagrange).

## Honesty / scope

This is the **defining derivative property** and a clean prerequisite for the *differentiation*
route to `φ`-transitivity `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` (Serre IV §3 Prop. 15) and Herbrand's
theorem: both sides of the transitivity identity are continuous, piecewise-affine, agree at `0`,
and one compares their slopes. **It is NOT transitivity itself** — that additionally needs the
*index-multiplicativity* relating the three filtrations `|G_i|`, `|H_i| = |H ∩ G_i|` (Pass 46),
`|(G/H)_j|` across the tower (Serre's Lemma 5 / the quotient half of Herbrand's theorem), which is
the genuinely multi-pass arithmetic wall; nothing of it is claimed or half-built here.

A structural fact about a given extension's `φ` — strictly below R1; recovers nothing from an
abstract group. No new `structure`/`class`. The instantiation carries
`[Finite (A.decompositionSubgroup K)]` (automatic at the finite level, gives `|G_i| ≥ 1`), a
standing finiteness, not a claimed-essential hypothesis; no owed witness. D1 N/A; D2 N/A.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open MeasureTheory Filter Topology Set

namespace Anabelian

/-! ## The slope, abstractly -/

/-- The integrand of `φ` is locally constant on `(n, n+1)`, so FTC gives `φ` the affine slope
`g_{n+1}/g_0` there. -/
theorem herbrandPhiSeq_hasDerivAt_Ioo (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    {n : ℕ} {u : ℝ} (hu : u ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    HasDerivAt (herbrandPhiSeq g) (g (n + 1) / g 0) u := by
  have heq : herbrandIntegrand g =ᶠ[𝓝 u] fun _ => g (n + 1) / g 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    have hfloor : ⌊x⌋₊ = n := Nat.floor_eq_on_Ico n x ⟨hx.1.le, hx.2⟩
    have hx0 : ¬ x ≤ 0 := not_le.mpr (lt_of_le_of_lt (Nat.cast_nonneg n) hx.1)
    simp only [herbrandIntegrand, herbrandIndex, if_neg hx0, hfloor]
  have hsmaf : StronglyMeasurableAtFilter (herbrandIntegrand g) (𝓝 u) :=
    ⟨univ, univ_mem, by
      rw [Measure.restrict_univ]
      exact (herbrandIntegrand_antitone g hg hg0).measurable.aestronglyMeasurable⟩
  have hval : herbrandIntegrand g u = g (n + 1) / g 0 := heq.eq_of_nhds
  rw [← hval]
  exact intervalIntegral.integral_hasDerivAt_right
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 u) hsmaf heq.continuousAt

/-- For `u < 0` the integrand is the constant `1`, so `φ` has slope `1` (it is `id` there). -/
theorem herbrandPhiSeq_hasDerivAt_neg (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    {u : ℝ} (hu : u < 0) : HasDerivAt (herbrandPhiSeq g) 1 u := by
  have heq : herbrandIntegrand g =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds hu] with x hx
    have hxle : x ≤ 0 := (Set.mem_Iio.mp hx).le
    simp only [herbrandIntegrand, herbrandIndex, if_pos hxle]
    exact div_self (ne_of_gt hg0)
  have hsmaf : StronglyMeasurableAtFilter (herbrandIntegrand g) (𝓝 u) :=
    ⟨univ, univ_mem, by
      rw [Measure.restrict_univ]
      exact (herbrandIntegrand_antitone g hg hg0).measurable.aestronglyMeasurable⟩
  have hval : herbrandIntegrand g u = 1 := heq.eq_of_nhds
  rw [← hval]
  exact intervalIntegral.integral_hasDerivAt_right
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 u) hsmaf heq.continuousAt

theorem herbrandPhiSeq_deriv_Ioo (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    {n : ℕ} {u : ℝ} (hu : u ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    deriv (herbrandPhiSeq g) u = g (n + 1) / g 0 :=
  (herbrandPhiSeq_hasDerivAt_Ioo g hg hg0 hu).deriv

theorem herbrandPhiSeq_deriv_neg (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    {u : ℝ} (hu : u < 0) : deriv (herbrandPhiSeq g) u = 1 :=
  (herbrandPhiSeq_hasDerivAt_neg g hg hg0 hu).deriv

/-! ## Instantiation: `φ'_{L/K}(u) = 1/(G_0 : G_u)` -/

open ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- **The slope of `φ`** on `(n, n+1)` is `|G_{n+1}| / |G_0| = 1/(G_0 : G_u)` (Serre IV §3): the
defining derivative property of the Herbrand function. -/
theorem herbrandPhi_hasDerivAt_Ioo [Finite (A.decompositionSubgroup K)] {n : ℕ} {u : ℝ}
    (hu : u ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    HasDerivAt (herbrandPhi K A)
      ((Nat.card (ramificationGroup K A (n + 1)) : ℝ) / Nat.card (ramificationGroup K A 0)) u :=
  herbrandPhiSeq_hasDerivAt_Ioo _ (ramificationOrders_antitone K A)
    (ramificationOrders_pos K A 0) hu

/-- For `u < 0`, `φ_{L/K}` has slope `1` (`φ = id` there). -/
theorem herbrandPhi_hasDerivAt_neg [Finite (A.decompositionSubgroup K)] {u : ℝ} (hu : u < 0) :
    HasDerivAt (herbrandPhi K A) 1 u :=
  herbrandPhiSeq_hasDerivAt_neg _ (ramificationOrders_antitone K A)
    (ramificationOrders_pos K A 0) hu

theorem herbrandPhi_deriv_Ioo [Finite (A.decompositionSubgroup K)] {n : ℕ} {u : ℝ}
    (hu : u ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    deriv (herbrandPhi K A) u
      = (Nat.card (ramificationGroup K A (n + 1)) : ℝ) / Nat.card (ramificationGroup K A 0) :=
  (herbrandPhi_hasDerivAt_Ioo K A hu).deriv

theorem herbrandPhi_deriv_neg [Finite (A.decompositionSubgroup K)] {u : ℝ} (hu : u < 0) :
    deriv (herbrandPhi K A) u = 1 :=
  (herbrandPhi_hasDerivAt_neg K A hu).deriv

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms herbrandPhiSeq_hasDerivAt_Ioo
#print axioms herbrandPhiSeq_hasDerivAt_neg
#print axioms herbrandPhiSeq_deriv_Ioo
#print axioms herbrandPhiSeq_deriv_neg
#print axioms herbrandPhi_hasDerivAt_Ioo
#print axioms herbrandPhi_hasDerivAt_neg
#print axioms herbrandPhi_deriv_Ioo
#print axioms herbrandPhi_deriv_neg

end Anabelian
