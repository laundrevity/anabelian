/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Ramification.LowerIndex
import Mathlib

/-!
# Toward Serre IV §3 Lemma 5: the double count `Σ min(i(σ), m) = Σ_{k<m} |G_k|` (Pass 66)

Pass 65 reduced the fiber sum of Prop. 3 to `Σ_{h ∈ H} min(i_H(h), j)`; this pass evaluates
that shape: **for any extension's decomposition group,**

> **`Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|`** (`sum_min_lowerIndex_eq`).

The proof is a double count: `min(i(σ), m)` is the number of levels `k < m` that `σ` still
survives (`enat_min_coe_eq_sum`, a generic `ℕ∞` lemma), and "surviving level `k`" is exactly
membership in `G_k` — Pass 51's Lemma 1, `k < i(σ) ↔ σ ∈ G_k`. Swapping the sums counts each
level's survivors: `|G_k|`.

Applied to `H = Gal(L/K')` at the assembly: Pass 63 + Pass 65 + this pass give
`e'·i_{K'/K}(σ̄) = Σ_{k<j} |H_k|`, and Pass 48's `φ`-formula (`φ(n) = (|H_1|+…+|H_n|)/|H_0|`)
identifies the right side as `|H_0|·(φ_{L/K'}(j−1) + 1)` — the `ℕ∞`-to-`ℝ` bridge and that
identification are the next brick, yielding Serre's `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)`.

## Honesty

Counting for a given extension's filtration — **no reach toward R1–R3**. The `φ`-bridge and
Lemma 5 itself are NOT claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2
untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian


/-- Pointwise level-set decomposition in `ℕ∞`: `min x m` is the number of `k < m` with
`k < x`, as an indicator sum. (The counting engine of Serre IV §3's `Σ min` evaluation.) -/
theorem enat_min_coe_eq_sum (x : ℕ∞) (m : ℕ) :
    min x (m : ℕ∞) = ∑ k ∈ Finset.range m, (if (k : ℕ∞) < x then (1 : ℕ∞) else 0) := by
  classical
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rcases lt_or_ge (n : ℕ∞) x with hlt | hge
    · rw [if_pos hlt]
      have h1 : ((n : ℕ) : ℕ∞) + 1 ≤ x := ENat.add_one_le_iff (ENat.coe_ne_top n) |>.mpr hlt
      have h2 : min x ((n : ℕ) : ℕ∞) = (n : ℕ∞) := min_eq_right (le_of_lt hlt)
      have h3 : min x (((n + 1 : ℕ)) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by
        refine min_eq_right ?_
        push_cast
        exact h1
      rw [h2, h3]
      push_cast
      ring
    · rw [if_neg (not_lt.mpr hge)]
      have h2 : min x ((n : ℕ) : ℕ∞) = x := min_eq_left hge
      have h3 : min x (((n + 1 : ℕ)) : ℕ∞) = x := by
        refine min_eq_left (le_trans hge ?_)
        push_cast
        exact le_self_add
      rw [h2, h3, add_zero]

section Count

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [Fintype (A.decompositionSubgroup K)]

/-- **The double count** (Serre IV §3, inside Lemma 5's proof): for any extension's
decomposition group, `Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|` — decompose each `min` into level-set
indicators (`enat_min_coe_eq_sum`), swap the two sums, and recognize each level set as a
ramification group via Pass 51's Lemma 1 (`k < i(σ) ↔ σ ∈ G_k`). Applied to `H = Gal(L/K')`,
this turns Pass 65's `Σ_h min(i_H(h), j)` into `Σ_{k<j} |H_k|` — the numerator of the
Herbrand `φ` (Pass 48), up to the `k = 0` term. -/
theorem sum_min_lowerIndex_eq (m : ℕ) :
    ∑ σ : A.decompositionSubgroup K, min (lowerIndex K A σ) (m : ℕ∞)
      = ∑ k ∈ Finset.range m,
          ((Nat.card (ramificationGroup K A k)) : ℕ∞) := by
  classical
  simp_rw [enat_min_coe_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmem : ∀ σ : A.decompositionSubgroup K,
      ((k : ℕ∞) < lowerIndex K A σ) ↔ σ ∈ ramificationGroup K A k :=
    fun σ => (mem_ramificationGroup_iff_lt_lowerIndex K A).symm
  calc ∑ σ : A.decompositionSubgroup K,
        (if (k : ℕ∞) < lowerIndex K A σ then (1 : ℕ∞) else 0)
      = ∑ σ : A.decompositionSubgroup K,
        (if σ ∈ ramificationGroup K A k then (1 : ℕ∞) else 0) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [if_congr (hmem σ) rfl rfl]
    _ = ((Finset.univ.filter
          (fun σ => σ ∈ ramificationGroup K A k)).card : ℕ∞) :=
        Finset.sum_boole _ _
    _ = ((Nat.card (ramificationGroup K A k)) : ℕ∞) := by
        congr 1
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end Count


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms enat_min_coe_eq_sum
#print axioms sum_min_lowerIndex_eq

end Anabelian
