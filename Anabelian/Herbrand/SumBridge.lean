/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Herbrand.Formula
import Anabelian.Ramification.LowerIndexCount
import Mathlib

/-!
# Toward Serre IV §3 Lemma 5: the `φ`-bridge `Σ_{k ≤ n} |G_k| = |G_0|·(φ(n) + 1)` (Pass 67)

Pass 66 evaluated the fiber sum as `Σ_{k<m} |G_k|` (an `ℕ∞`-count); the Herbrand `φ` side of
Lemma 5 speaks in `ℝ`. This pass is the bridge:

> **`Σ_{k ∈ range (n+1)} |G_k| = |G_0| · (φ(n) + 1)`** (`sum_ramificationOrders_range_succ`),

Pass 48's `herbrandPhi_natCast` (`φ(n) = (|G_1| + … + |G_n|)/|G_0|`) with the `k = 0` term
absorbed — plus the two cast forms connecting it to Pass 66's output: the `Nat.card`-cast
`ℝ`-form (`natCast_sum_natCard_eq`) and the `ℕ∞`-to-`ℕ` sum cast (`sum_natCard_enat_eq`).

With these, the Lemma-5 numerical chain is fully typed: Pass 63 + Pass 65 + Pass 66 give
`e'·i_{K'/K}(σ̄) = Σ_{k<j} |H_k|` in `ℕ∞`; casting down to `ℕ` and up to `ℝ` and applying
this bridge (at `H = Gal(L/K')`, `j = m+1`) gives
`e'·i_{K'/K}(σ̄) = |H_0|·(φ_{L/K'}(j−1) + 1)` — Serre's
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)` once `e' = |H_0|` is identified (the next brick).

## Honesty

Cast and sum bookkeeping over Passes 48/66 — **no reach toward R1–R3**. The `e' = |H_0|`
identification and Lemma 5 itself are NOT claimed. No new `structure`/`class`; no owed
witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [Finite (A.decompositionSubgroup K)]

/-- **The `φ`-bridge**: `Σ_{k ≤ n} |G_k| = |G_0| · (φ(n) + 1)` — Pass 48's
`φ(n) = (|G_1| + … + |G_n|)/|G_0|` with the `k = 0` term absorbed into the `+ 1`. -/
theorem sum_ramificationOrders_range_succ (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), ramificationOrders K A k
      = ramificationOrders K A 0 * (herbrandPhi K A (n : ℝ) + 1) := by
  have h0ne : ramificationOrders K A 0 ≠ 0 := ne_of_gt (ramificationOrders_pos K A 0)
  rw [Finset.sum_range_succ', herbrandPhi_natCast, mul_add, mul_one,
      mul_div_cancel₀ _ h0ne]

/-- The `Nat.card`-cast form (the shape Pass 66 produces, read in `ℝ`). -/
theorem natCast_sum_natCard_eq (n : ℕ) :
    ((∑ k ∈ Finset.range (n + 1), Nat.card (ramificationGroup K A k) : ℕ) : ℝ)
      = ramificationOrders K A 0 * (herbrandPhi K A (n : ℝ) + 1) := by
  rw [Nat.cast_sum]
  exact (Finset.sum_congr rfl fun k _ => rfl).trans
    (sum_ramificationOrders_range_succ K A n)

omit [Finite (A.decompositionSubgroup K)] in
/-- Pass 66's `ℕ∞` sum is the cast of the `ℕ` sum (each `Nat.card` is finite). -/
theorem sum_natCard_enat_eq (m : ℕ) :
    ∑ k ∈ Finset.range m, ((Nat.card (ramificationGroup K A k)) : ℕ∞)
      = ((∑ k ∈ Finset.range m, Nat.card (ramificationGroup K A k) : ℕ) : ℕ∞) :=
  (Nat.cast_sum _ _).symm

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms sum_ramificationOrders_range_succ
#print axioms natCast_sum_natCard_eq
#print axioms sum_natCard_enat_eq

end Anabelian
