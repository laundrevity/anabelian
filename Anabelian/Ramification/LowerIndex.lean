/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Ramification.Filtration
import Anabelian.Ramification.Subgroup
import Mathlib

/-!
# The ascent: Serre's `i_G` function (IV §1 Lemma 1, abstract form) (Pass 51)

The quotient-ramification arithmetic — Serre IV §1 Prop. 3 (`i_{K'/K}(σ̄)` as a sum of the
`i_{L/K}` of the lifts) feeding IV §3 Lemma 5, `φ`-transitivity, and Herbrand's theorem — is
denominated in **Serre's `i_G` function**: `i_G(σ) = v_L(σx − x)` for a generator `x` of
`𝒪_L/𝒪_K`, with the defining property `σ ∈ G_i ⇔ i_G(σ) ≥ i + 1` (IV §1 Lemma 1). This pass
mints that currency at the project's abstract level (Pass 50 built the group-theoretic skeleton;
this is the first brick of the arithmetic on top of it).

The definition is **generator-free**: `lowerIndex K A σ = sup {n : ℕ | ∀ a ∈ A, σa − a ∈ 𝔪^n}`
in `ℕ∞` — the filtration side of Lemma 1 taken as the definition. Lemma 1's content thereby
splits: the equivalence with the ramification filtration is proved here
(`mem_ramificationGroup_iff_lt_lowerIndex`, no monogenicity needed), and the identification with
the concrete `v_L(σx − x)` — which *does* need a monogenic generator (the project's
`ExtensionMonogenic*` arc) — is deferred to the Prop.-3 pass that will consume it.

## What is proved (all axiom-free)

* `lowerIndex K A σ : ℕ∞` — the sup above; `⊤` iff `σ` lies in every `G_i`
  (`lowerIndex_eq_top_iff_forall`), hence `= ⊤ ↔ σ = 1` under Krull separation
  (`lowerIndex_eq_top_iff`, via Pass 23's `iInf_ramificationGroup_eq_bot`); `lowerIndex 1 = ⊤`.
* **`mem_ramificationGroup_iff_lt_lowerIndex`** — the headline (Serre IV §1 Lemma 1, abstract
  form): `σ ∈ G_i ↔ i < i_G(σ)`; Serre's inequality form `σ ∈ G_i ↔ i + 1 ≤ i_G(σ)`
  (`mem_ramificationGroup_iff_add_one_le_lowerIndex`).
* **The `i_G` calculus** (each a one-liner from Lemma 1 + the subgroup structure of the `G_i`):
  `lowerIndex_inv` (`i(σ⁻¹) = i(σ)`), `min_lowerIndex_le_lowerIndex_mul`
  (`i(στ) ≥ min (i(σ), i(τ))`), `lowerIndex_conj` (`i(τστ⁻¹) = i(σ)` — `i_G` is a class
  function, via Pass 23's normality).
* **`lowerIndex_decompositionRestrict`** — the second half of Serre IV §1 Prop. 2, which Pass 46
  didn't need: **`i_H = i_G` on `H`** for the tower `K ⊆ K' ⊆ L` — and the proof is `rfl`,
  because the lower theory is intrinsic to `A` and Pass 46's action agreement is definitional.
* `enat_le_of_forall_natCast_lt` / `enat_eq_of_forall_natCast_lt_iff` — the small `ℕ∞` interface
  (naturals are cofinal below any `x : ℕ∞`) the calculus runs on; kept public for the coming
  Prop.-3 arithmetic.

## Honesty

Structure of the Galois action of given fields — **no reach toward R1–R3**; nothing recovered
from an abstract group. Stated for a general `A : ValuationSubring L` like the Pass-23
filtration it characterizes. The separation hypothesis in `lowerIndex_eq_top_iff` is inherited
from Pass 23's `iInf_ramificationGroup_eq_bot` (same governance: it holds in the Noetherian /
finite-level case, provably fails at `𝒪[K̄]`; no claim that it is irremovable from this
conclusion). No new `structure`/`class` (`lowerIndex` is a `def` of a function into `ℕ∞`); no
owed witness; D1 N/A; D2 N/A.

**NOT here:** the sum formula `i_{K'/K}(σ̄) = (1/e') Σ i_{L/K}(s)` over lifts `s` of `σ̄` (Serre
IV §1 Prop. 3) — the real arithmetic wall, next; and the concrete `i_G(σ) = v_L(σx − x)` via
monogenicity, deferred to the pass that needs it.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian

/-- Naturals are cofinal below any `x : ℕ∞`: to prove `x ≤ y` it suffices that every natural
below `x` is below `y` (if `y < x` then `y` is a natural below `x` but not below itself). -/
theorem enat_le_of_forall_natCast_lt {x y : ℕ∞}
    (h : ∀ n : ℕ, (n : ℕ∞) < x → (n : ℕ∞) < y) : x ≤ y := by
  by_contra hxy
  push Not at hxy
  lift y to ℕ using hxy.ne_top
  exact absurd (h y hxy) (lt_irrefl _)

/-- Two extended naturals with the same naturals below them are equal. -/
theorem enat_eq_of_forall_natCast_lt_iff {x y : ℕ∞}
    (h : ∀ n : ℕ, ((n : ℕ∞) < x ↔ (n : ℕ∞) < y)) : x = y :=
  le_antisymm (enat_le_of_forall_natCast_lt fun n hn => (h n).mp hn)
    (enat_le_of_forall_natCast_lt fun n hn => (h n).mpr hn)

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- **Serre's `i_G` function** (Serre, *Local Fields*, IV §1), in generator-free form:
`i_G(σ) = sup {n | ∀ a ∈ A, σa − a ∈ 𝔪_A^n} ∈ ℕ∞`. Serre defines `i_G(σ) = v_L(σx − x)` for a
monogenic generator `x` of `𝒪_L/𝒪_K` and proves the equivalence with this sup (IV §1 Lemma 1);
here the sup is the definition, `mem_ramificationGroup_iff_lt_lowerIndex` is the (generator-free
half of) Lemma 1, and the identification with `v_L(σx − x)` is deferred to the monogenic setting
that needs it. The name follows the lower numbering it measures. -/
noncomputable def lowerIndex (σ : A.decompositionSubgroup K) : ℕ∞ :=
  ⨆ n ∈ {n : ℕ | ∀ a : ↥A, σ • a - a ∈ maximalIdeal ↥A ^ n}, (n : ℕ∞)

/-- The defining set of `lowerIndex` is downward closed (`𝔪^n ⊆ 𝔪^m` for `m ≤ n`). -/
theorem smul_sub_mem_pow_of_le {σ : A.decompositionSubgroup K} {m n : ℕ} (hmn : m ≤ n)
    (hn : ∀ a : ↥A, σ • a - a ∈ maximalIdeal ↥A ^ n) :
    ∀ a : ↥A, σ • a - a ∈ maximalIdeal ↥A ^ m :=
  fun a => Ideal.pow_le_pow_right hmn (hn a)

/-- **Serre IV §1 Lemma 1** (abstract form): membership in the ramification filtration is
measured by `i_G` — `σ ∈ G_i ↔ i < i_G(σ)`. Forward: `i + 1` is in the defining set, so the sup
exceeds `i`. Backward: some `n > i` is in the set, and the set is downward closed. -/
theorem mem_ramificationGroup_iff_lt_lowerIndex {i : ℕ} {σ : A.decompositionSubgroup K} :
    σ ∈ ramificationGroup K A i ↔ (i : ℕ∞) < lowerIndex K A σ := by
  rw [mem_ramificationGroup_iff]
  constructor
  · intro h
    have hle : ((i + 1 : ℕ) : ℕ∞) ≤ lowerIndex K A σ :=
      le_biSup (fun n : ℕ => (n : ℕ∞)) h
    exact lt_of_lt_of_le (Nat.cast_lt.mpr (Nat.lt_succ_self i)) hle
  · intro h
    obtain ⟨n, hn, hin⟩ := lt_biSup_iff.mp h
    exact smul_sub_mem_pow_of_le K A (Nat.cast_lt.mp hin) hn

/-- Serre's inequality form of Lemma 1: `σ ∈ G_i ↔ i_G(σ) ≥ i + 1`. -/
theorem mem_ramificationGroup_iff_add_one_le_lowerIndex {i : ℕ}
    {σ : A.decompositionSubgroup K} :
    σ ∈ ramificationGroup K A i ↔ (i : ℕ∞) + 1 ≤ lowerIndex K A σ := by
  rw [mem_ramificationGroup_iff_lt_lowerIndex, ENat.add_one_le_iff (ENat.coe_ne_top i)]

/-- `i_G(1) = ∞`: the identity lies in every ramification group. -/
theorem lowerIndex_one : lowerIndex K A 1 = ⊤ := by
  rw [ENat.eq_top_iff_forall_gt]
  intro m
  exact (mem_ramificationGroup_iff_lt_lowerIndex K A).mp
    (Subgroup.one_mem (ramificationGroup K A m))

/-- `i_G(σ) = ∞` iff `σ` lies in every ramification group. -/
theorem lowerIndex_eq_top_iff_forall {σ : A.decompositionSubgroup K} :
    lowerIndex K A σ = ⊤ ↔ ∀ i : ℕ, σ ∈ ramificationGroup K A i := by
  rw [ENat.eq_top_iff_forall_gt]
  exact forall_congr' fun i => (mem_ramificationGroup_iff_lt_lowerIndex K A).symm

/-- Under Krull separation (the finite-level situation, Pass 23), `i_G` detects the identity:
`i_G(σ) = ∞ ↔ σ = 1`. Serre's "`i_G(σ) = +∞` if and only if `σ = 1`" (IV §1). -/
theorem lowerIndex_eq_top_iff (h : (⨅ n : ℕ, maximalIdeal ↥A ^ n) = ⊥)
    {σ : A.decompositionSubgroup K} :
    lowerIndex K A σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro htop
    have hmem : σ ∈ ⨅ i : ℕ, ramificationGroup K A i :=
      Subgroup.mem_iInf.mpr ((lowerIndex_eq_top_iff_forall K A).mp htop)
    rw [iInf_ramificationGroup_eq_bot K A h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · rintro rfl
    exact lowerIndex_one K A

/-- `i_G(σ⁻¹) = i_G(σ)` — each `G_i` is a subgroup. -/
theorem lowerIndex_inv (σ : A.decompositionSubgroup K) :
    lowerIndex K A σ⁻¹ = lowerIndex K A σ := by
  refine enat_eq_of_forall_natCast_lt_iff fun n => ?_
  rw [← mem_ramificationGroup_iff_lt_lowerIndex, ← mem_ramificationGroup_iff_lt_lowerIndex,
      inv_mem_iff]

/-- `i_G(στ) ≥ min (i_G(σ), i_G(τ))` — each `G_i` is closed under multiplication. (Serre IV §1
Prop. 5's underlying inequality.) -/
theorem min_lowerIndex_le_lowerIndex_mul (σ τ : A.decompositionSubgroup K) :
    min (lowerIndex K A σ) (lowerIndex K A τ) ≤ lowerIndex K A (σ * τ) := by
  refine enat_le_of_forall_natCast_lt fun n hn => ?_
  rw [lt_min_iff] at hn
  rw [← mem_ramificationGroup_iff_lt_lowerIndex]
  exact mul_mem ((mem_ramificationGroup_iff_lt_lowerIndex K A).mpr hn.1)
    ((mem_ramificationGroup_iff_lt_lowerIndex K A).mpr hn.2)

/-- `i_G(τστ⁻¹) = i_G(σ)`: `i_G` is a class function on the decomposition group — each `G_i` is
normal (Pass 23, Serre IV §1 Prop. 1). -/
theorem lowerIndex_conj (σ τ : A.decompositionSubgroup K) :
    lowerIndex K A (τ * σ * τ⁻¹) = lowerIndex K A σ := by
  refine enat_eq_of_forall_natCast_lt_iff fun n => ?_
  rw [← mem_ramificationGroup_iff_lt_lowerIndex, ← mem_ramificationGroup_iff_lt_lowerIndex]
  constructor
  · intro h
    have h2 := (ramificationGroup_normal K A n).conj_mem _ h τ⁻¹
    simpa [mul_assoc] using h2
  · intro h
    exact (ramificationGroup_normal K A n).conj_mem σ h τ

section Tower

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable (A : ValuationSubring L)

/-- **The second half of Serre IV §1 Prop. 2** (the half Pass 46 didn't need): for the tower
`K ⊆ K' ⊆ L`, the `i` function of the subextension is the restriction of the ambient one —
`i_H = i_G` on `H = Gal(L/K')`. The proof is `rfl`: the defining condition is intrinsic to `A`,
and Pass 46's action agreement (`decompositionRestrict_smul`) is definitional. -/
theorem lowerIndex_decompositionRestrict (σ : A.decompositionSubgroup K') :
    lowerIndex K A (decompositionRestrict K K' A σ) = lowerIndex K' A σ := rfl

end Tower

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms enat_le_of_forall_natCast_lt
#print axioms enat_eq_of_forall_natCast_lt_iff
#print axioms lowerIndex
#print axioms smul_sub_mem_pow_of_le
#print axioms mem_ramificationGroup_iff_lt_lowerIndex
#print axioms mem_ramificationGroup_iff_add_one_le_lowerIndex
#print axioms lowerIndex_one
#print axioms lowerIndex_eq_top_iff_forall
#print axioms lowerIndex_eq_top_iff
#print axioms lowerIndex_inv
#print axioms min_lowerIndex_le_lowerIndex_mul
#print axioms lowerIndex_conj
#print axioms lowerIndex_decompositionRestrict

end Anabelian
