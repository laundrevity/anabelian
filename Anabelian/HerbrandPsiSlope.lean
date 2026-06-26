/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.HerbrandSlope
import Anabelian.UpperNumbering
import Mathlib

/-!
# The ascent: the slope of the inverse Herbrand function `ψ` (Pass 49)

The derivative of `ψ = φ⁻¹` (Serre, *Local Fields*, IV §3), the symmetric counterpart of Pass 47's
`φ'(u) = 1/(G_0 : G_u)`. By the **inverse function theorem**, where `ψ(v)` lands in an open interval
`(n, n+1)` the slope of `ψ` is the reciprocal of `φ`'s:

> **`herbrandPsi_hasDerivAt`** — if `ψ(v) ∈ (n, n+1)` then
> `ψ'(v) = |G_0|/|G_{n+1}| = (G_0 : G_{ψ(v)})`.

So `ψ' = (G_0 : G_u)` (the ramification *index*) exactly inverts `φ' = 1/(G_0 : G_u)`, completing
the derivative picture of the Herbrand pair.

## What is proved (all axiom-free)

* `herbrandPsiSeq_hasDerivAt` / `herbrandPsiSeq_hasDerivAt_neg` — abstractly (order sequence `g`):
  `HasDerivAt ψ (g_0/g_{n+1}) v` where `ψ(v) ∈ (n, n+1)` (via `HasDerivAt.of_local_left_inverse`,
  using Pass 47's `φ` slope, Pass 45's `ψ` continuity, and the inverse identity `φ ∘ ψ = id`), and
  `HasDerivAt ψ 1 v` for `v < 0` (where `ψ = id`).
* `herbrandPsiSeq_deriv` / `herbrandPsiSeq_deriv_neg` — the `deriv` form.
* `herbrandPsi_hasDerivAt` / `herbrandPsi_hasDerivAt_neg` and their `deriv` forms — the
  instantiation: `ψ'_{L/K}(v) = |G_0|/|G_{n+1}|` where `ψ(v) ∈ (n, n+1)`.

## Honesty / scope

The symmetric completion of `φ`'s derivative theory — a structural fact about `ψ`, strictly below
R1; recovers nothing from an abstract group. **Not `φ`-transitivity** (still the multi-pass wall —
the quotient relationship `(G/H)_{φ(u)} = G_u H/H`, absent from Mathlib). No new
`structure`/`class`. The
instantiation carries `[Finite (A.decompositionSubgroup K)]` (automatic at the finite level, gives
`|G_i| ≥ 1` so `φ` is a bijection and `ψ` exists), a standing finiteness, not a claimed-essential
hypothesis; no owed witness. D1 N/A; D2 N/A.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open MeasureTheory Filter Topology Set

namespace Anabelian

/-! ## The slope of `ψ`, abstractly -/

/-- **The slope of `ψ`**: where `ψ(v) ∈ (n, n+1)`, `ψ'(v) = g_0/g_{n+1} = (G_0 : G_{ψ(v)})` — the
reciprocal of `φ`'s slope, by the inverse function theorem. -/
theorem herbrandPsiSeq_hasDerivAt (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i)
    {n : ℕ} {v : ℝ} (hv : herbrandPsiSeq g v ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    HasDerivAt (herbrandPsiSeq g) (g 0 / g (n + 1)) v := by
  have hg0 : 0 < g 0 := lt_of_lt_of_le one_pos (hg1 0)
  have hφ : HasDerivAt (herbrandPhiSeq g) (g (n + 1) / g 0) (herbrandPsiSeq g v) :=
    herbrandPhiSeq_hasDerivAt_Ioo g hg hg0 hv
  have hcont : ContinuousAt (herbrandPsiSeq g) v :=
    (herbrandPsiSeq_continuous g hg hg1).continuousAt
  have hne : g (n + 1) / g 0 ≠ 0 :=
    ne_of_gt (div_pos (lt_of_lt_of_le one_pos (hg1 (n + 1))) hg0)
  have hfg : ∀ᶠ y in 𝓝 v, herbrandPhiSeq g (herbrandPsiSeq g y) = y :=
    Filter.Eventually.of_forall (herbrandPhiSeq_psiSeq g hg hg1)
  have hd := HasDerivAt.of_local_left_inverse hcont hφ hne hfg
  rwa [inv_div] at hd

/-- For `v < 0`, `ψ` has slope `1` (it is `id` there). -/
theorem herbrandPsiSeq_hasDerivAt_neg (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i)
    {v : ℝ} (hv : v < 0) : HasDerivAt (herbrandPsiSeq g) 1 v := by
  have heq : herbrandPsiSeq g =ᶠ[𝓝 v] id := by
    filter_upwards [isOpen_Iio.mem_nhds (show v ∈ Iio 0 from hv)] with y hy
    exact herbrandPsiSeq_eq_id g hg hg1 (le_of_lt (Set.mem_Iio.mp hy))
  exact (hasDerivAt_id v).congr_of_eventuallyEq heq

theorem herbrandPsiSeq_deriv (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i)
    {n : ℕ} {v : ℝ} (hv : herbrandPsiSeq g v ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    deriv (herbrandPsiSeq g) v = g 0 / g (n + 1) :=
  (herbrandPsiSeq_hasDerivAt g hg hg1 hv).deriv

theorem herbrandPsiSeq_deriv_neg (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i)
    {v : ℝ} (hv : v < 0) : deriv (herbrandPsiSeq g) v = 1 :=
  (herbrandPsiSeq_hasDerivAt_neg g hg hg1 hv).deriv

/-! ## Instantiation: `ψ'_{L/K}(v) = (G_0 : G_{ψ(v)})` -/

open ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- **The slope of `ψ`** of the extension: where `ψ(v) ∈ (n, n+1)`,
`ψ'_{L/K}(v) = |G_0|/|G_{n+1}| = (G_0 : G_{ψ(v)})`. -/
theorem herbrandPsi_hasDerivAt [Finite (A.decompositionSubgroup K)] {n : ℕ} {v : ℝ}
    (hv : herbrandPsi K A v ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    HasDerivAt (herbrandPsi K A)
      ((Nat.card (ramificationGroup K A 0) : ℝ) / Nat.card (ramificationGroup K A (n + 1))) v :=
  herbrandPsiSeq_hasDerivAt _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A) hv

/-- For `v < 0`, `ψ_{L/K}` has slope `1` (`ψ = id` there). -/
theorem herbrandPsi_hasDerivAt_neg [Finite (A.decompositionSubgroup K)] {v : ℝ} (hv : v < 0) :
    HasDerivAt (herbrandPsi K A) 1 v :=
  herbrandPsiSeq_hasDerivAt_neg _ (ramificationOrders_antitone K A)
    (ramificationOrders_one_le K A) hv

theorem herbrandPsi_deriv [Finite (A.decompositionSubgroup K)] {n : ℕ} {v : ℝ}
    (hv : herbrandPsi K A v ∈ Ioo (n : ℝ) ((n : ℝ) + 1)) :
    deriv (herbrandPsi K A) v
      = (Nat.card (ramificationGroup K A 0) : ℝ) / Nat.card (ramificationGroup K A (n + 1)) :=
  (herbrandPsi_hasDerivAt K A hv).deriv

theorem herbrandPsi_deriv_neg [Finite (A.decompositionSubgroup K)] {v : ℝ} (hv : v < 0) :
    deriv (herbrandPsi K A) v = 1 :=
  (herbrandPsi_hasDerivAt_neg K A hv).deriv

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms herbrandPsiSeq_hasDerivAt
#print axioms herbrandPsiSeq_hasDerivAt_neg
#print axioms herbrandPsiSeq_deriv
#print axioms herbrandPsiSeq_deriv_neg
#print axioms herbrandPsi_hasDerivAt
#print axioms herbrandPsi_hasDerivAt_neg
#print axioms herbrandPsi_deriv
#print axioms herbrandPsi_deriv_neg

end Anabelian
