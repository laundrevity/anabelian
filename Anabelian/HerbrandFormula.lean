/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.HerbrandFunction
import Mathlib

/-!
# The ascent: the explicit piecewise-linear formula for `φ` (Pass 48)

The concrete closed form of the Herbrand function (Serre, *Local Fields*, IV §3): `φ` is the
continuous piecewise-linear function with `φ(0) = 0` whose graph on `[n, n+1]` is the segment of
slope `g_{n+1}/g_0`. We read it off the integral definition `φ(u) = ∫_0^u dt/(G_0 : G_t)` (Pass 44)
— the integrand is **constant `g_{n+1}/g_0` on each unit interval `(n, n+1)`** (up to the
measure-zero integer breakpoints), so the integral splits into a partial sum plus an affine
remainder.

> **`herbrandPhi_natCast`** — `φ(n) = (|G_1| + … + |G_n|)/|G_0|`;
> **`herbrandPhi_eq_affine_formula`** — for `u ∈ [n, n+1]`,
> `φ(u) = (|G_1| + … + |G_n| + (u−n)·|G_{n+1}|)/|G_0|`.

This is the *global* counterpart of Pass 47's *differential* statement (`φ'(u) = 1/(G_0 : G_u)` on
`(n, n+1)`); proving it via the integral (rather than by integrating the slope) sidesteps the
breakpoint-derivative bookkeeping.

## What is proved (all axiom-free)

* `herbrandSeq_integral_sub_Icc` — over any `[a, b] ⊆ [n, n+1]`, `∫_a^b dt/(G_0:G_t) =
  (b−a)·g_{n+1}/g_0` (the integrand is a.e. the constant `g_{n+1}/g_0` there — `Ι a b` excludes the
  left endpoint, so the only exceptional point is the right breakpoint, which is null).
* `herbrandPhiSeq_integral_unit` — the unit-interval value `∫_n^{n+1} = g_{n+1}/g_0`.
* `herbrandPhiSeq_natCast` / `herbrandPhiSeq_affine` / `herbrandPhiSeq_eq_affine_formula` —
  abstractly on a sequence `g`: the integer values, the affine step, and the closed form.
* `herbrandPhi_natCast` / `herbrandPhi_eq_affine_formula` — the instantiation on the ramification
  filtration (`ramificationOrders K A i = |G_i|`).

## Honesty / scope

The closed form **deepens `φ`** and is a clean prerequisite for `φ`-transitivity (it makes the
order-arithmetic across a tower explicit). **It is NOT transitivity itself**, which additionally
needs the quotient relationship `(G/H)_{φ(u)} = G_u H/H` relating `|(G/H)_j|` to `|G_i|` — the
genuinely multi-pass wall (Serre's Lemma 5 / the quotient half of Herbrand's theorem; verified
absent from Mathlib), not touched here.

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

/-! ## The closed form, abstractly -/

/-- Over any `[a, b] ⊆ [n, n+1]`, the integrand of `φ` is a.e. the constant `g_{n+1}/g_0`, so its
integral is `(b−a)·g_{n+1}/g_0`. (`Ι a b` is the *left-open* interval, so the only a.e.-exceptional
point is the right breakpoint `n+1`, which is null.) -/
theorem herbrandSeq_integral_sub_Icc (g : ℕ → ℝ) {n : ℕ} {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : b ≤ (n : ℝ) + 1) (hab : a ≤ b) :
    ∫ t in a..b, herbrandIntegrand g t = (b - a) * (g (n + 1) / g 0) := by
  have hae : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.uIoc a b → herbrandIntegrand g x = g (n + 1) / g 0 := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (↑n + 1 : ℝ) := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (↑n + 1 : ℝ))] with x hx
      simpa using hx
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hab] at hmem
    have hxn : (n : ℝ) < x := lt_of_le_of_lt ha hmem.1
    have hxn1 : x < (↑n + 1 : ℝ) := lt_of_le_of_ne (le_trans hmem.2 hb) hx
    have hfloor : ⌊x⌋₊ = n := Nat.floor_eq_on_Ico n x ⟨hxn.le, hxn1⟩
    have hx0 : ¬ x ≤ 0 := not_le.mpr (lt_of_le_of_lt (Nat.cast_nonneg n) hxn)
    simp only [herbrandIntegrand, herbrandIndex, if_neg hx0, hfloor]
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul]

/-- The unit-interval value `∫_n^{n+1} dt/(G_0:G_t) = g_{n+1}/g_0`. -/
theorem herbrandPhiSeq_integral_unit (g : ℕ → ℝ) (n : ℕ) :
    ∫ t in (n : ℝ)..((n : ℝ) + 1), herbrandIntegrand g t = g (n + 1) / g 0 := by
  rw [herbrandSeq_integral_sub_Icc g (le_refl _) (le_refl _) (by linarith)]; ring

/-- **Integer-point values**: `φ(n) = (g_1 + … + g_n)/g_0`. -/
theorem herbrandPhiSeq_natCast (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0) (n : ℕ) :
    herbrandPhiSeq g (n : ℝ) = (∑ i ∈ Finset.range n, g (i + 1)) / g 0 := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := n) (f := herbrandIntegrand g)
    (fun k _ => herbrandPhiSeq_intervalIntegrable g hg hg0 _ _)
  simp only [Nat.cast_zero] at hsum
  rw [herbrandPhiSeq, ← hsum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Nat.cast_succ]
  rw [herbrandPhiSeq_integral_unit g k]

/-- `φ` is **affine on `[n, n+1]`** with slope `g_{n+1}/g_0`:
`φ(u) = φ(n) + (u−n)·g_{n+1}/g_0`. -/
theorem herbrandPhiSeq_affine (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    {n : ℕ} {u : ℝ} (hu : u ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    herbrandPhiSeq g u = herbrandPhiSeq g (n : ℝ) + (u - (n : ℝ)) * (g (n + 1) / g 0) := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 (n : ℝ))
    (herbrandPhiSeq_intervalIntegrable g hg hg0 (n : ℝ) u)
  have hnu := herbrandSeq_integral_sub_Icc g (le_refl (n : ℝ)) hu.2 hu.1
  simp only [herbrandPhiSeq]
  rw [← hadd, hnu]

/-- **The explicit piecewise-linear formula** (Serre IV §3): for `u ∈ [n, n+1]`,
`φ(u) = (g_1 + … + g_n + (u−n)·g_{n+1})/g_0`. -/
theorem herbrandPhiSeq_eq_affine_formula (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    {n : ℕ} {u : ℝ} (hu : u ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    herbrandPhiSeq g u
      = ((∑ i ∈ Finset.range n, g (i + 1)) + (u - (n : ℝ)) * g (n + 1)) / g 0 := by
  rw [herbrandPhiSeq_affine g hg hg0 hu, herbrandPhiSeq_natCast g hg hg0]
  ring

/-! ## Instantiation on the ramification filtration -/

open ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- **`φ_{L/K}(n) = (|G_1| + … + |G_n|)/|G_0|`.** -/
theorem herbrandPhi_natCast [Finite (A.decompositionSubgroup K)] (n : ℕ) :
    herbrandPhi K A (n : ℝ)
      = (∑ i ∈ Finset.range n, ramificationOrders K A (i + 1)) / ramificationOrders K A 0 :=
  herbrandPhiSeq_natCast _ (ramificationOrders_antitone K A) (ramificationOrders_pos K A 0) n

/-- **The explicit formula** for the extension's Herbrand function: for `u ∈ [n, n+1]`,
`φ_{L/K}(u) = (|G_1| + … + |G_n| + (u−n)·|G_{n+1}|)/|G_0|`. -/
theorem herbrandPhi_eq_affine_formula [Finite (A.decompositionSubgroup K)] {n : ℕ} {u : ℝ}
    (hu : u ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    herbrandPhi K A u
      = ((∑ i ∈ Finset.range n, ramificationOrders K A (i + 1))
          + (u - (n : ℝ)) * ramificationOrders K A (n + 1)) / ramificationOrders K A 0 :=
  herbrandPhiSeq_eq_affine_formula _ (ramificationOrders_antitone K A)
    (ramificationOrders_pos K A 0) hu

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms herbrandSeq_integral_sub_Icc
#print axioms herbrandPhiSeq_integral_unit
#print axioms herbrandPhiSeq_natCast
#print axioms herbrandPhiSeq_affine
#print axioms herbrandPhiSeq_eq_affine_formula
#print axioms herbrandPhi_natCast
#print axioms herbrandPhi_eq_affine_formula

end Anabelian
