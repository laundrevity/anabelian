/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.RamificationFiltration
import Mathlib

/-!
# The ascent, rung 1: the Herbrand function `φ` (Pass 44)

The assembly (Pass 41) and the canonicity obligation (Pass 43) opened the **ascent** — Serre,
*Local Fields*, ch. IV §3: the Herbrand functions `φ`/`ψ` and the upper numbering. Mathlib has
**none of it** — its `RingTheory/Valuation/RamificationGroup.lean` defines only the inertia
subgroup `G_0` and carries a literal `TODO: Define higher ramification groups in lower numbering`;
`grep` for `herbrand`, `upperRamification`, `upperNumbering` over Mathlib returns zero hits. The
lower-numbering filtration `G_i` is the project's own (`Anabelian/RamificationFiltration.lean`,
Pass 23). This file builds the first piece of the ascent on it: the Herbrand function.

> **`herbrandPhi K A`** — Serre's `φ(u) = ∫_0^u dt/(G_0 : G_t)`, the piecewise-linear
> reparametrisation of the ramification filtration that converts lower into upper numbering.

We define it exactly as Serre does (the integral of the index reciprocal `1/(G_0 : G_t) = g_t/g_0`)
and prove its foundational properties. The construction is split into a reusable **analytic
engine** on an abstract decreasing order-sequence `g : ℕ → ℝ` (`g i = |G_i|`), then **instantiated**
on the real ramification orders — separating the analysis (Serre §3's lemmas are about the
function) from the ramification input (the filtration is decreasing, `ramificationGroup_antitone`).

## What is proved (all axiom-free)

The integrand `t ↦ g_{⌈t⌉}/g_0` is **antitone** (the filtration decreases), so it is interval
integrable (`Antitone.intervalIntegrable`) and the analysis is clean:

* `herbrandPhiSeq g` / `herbrandPhi K A` — the function `φ(u) = ∫_0^u dt/(G_0 : G_t)`.
* `herbrandPhi_zero` — `φ(0) = 0`.
* `herbrandPhi_strictMono` — `φ` is **strictly increasing** (the integrand is `> 0`, every `|G_i| ≥
  1`). With continuity, this is the precondition for the inverse `ψ = φ⁻¹` (the next rung).
* `herbrandPhi_monotone` — `Monotone φ` (corollary).
* `herbrandPhi_continuous` — `φ` is **continuous** (`continuous_primitive`).
* `herbrandPhi_eq_id` — `φ(u) = u` for `u ≤ 0` (Serre's normalisation on `[-1, 0]`; here on all of
  `(-∞, 0]`, where the acting group is `G_0` itself and the slope is `(G_0 : G_0)^{-1} = 1`).
* `herbrandPhi_le_self` — `φ(u) ≤ u` for `u ≥ 0` (the slopes `g_{⌈u⌉}/g_0 ≤ 1` are `≤ 1` because
  `G_t ≤ G_0`; the genuine ramification content distinguishing `φ` from the identity).

## Honesty

`φ` is a structural invariant of the Galois action of a given extension — a reparametrisation of
its ramification filtration — with **no reach toward R1–R3**; nothing is recovered from an abstract
group. The instantiation carries `[Finite (A.decompositionSubgroup K)]`: this is **automatic at the
intended finite level** (`A = 𝒪_L`, `L/K` finite — `decompositionSubgroup ⊆ L ≃ₐ[K] L`, finite),
and is what makes the orders `|G_i|` positive (without it Mathlib's `Nat.card` of an infinite group
is `0` and `φ` degenerates to `0`); it is a standing finiteness, not a claimed-essential hypothesis,
so no rule-2 come-apart / owed witness arises. No new `structure`/`class` (the objects are `def`s of
real functions); D1 N/A; D2 N/A (no spectral/normed structure — the file is real-analysis +
`ramificationGroup`-native).

**NOT yet built** (the ascent's remaining rungs, named for `ROADMAP.md`): the inverse `ψ = φ⁻¹`
(reachable now — `φ` is `StrictMono` + `Continuous`); the upper numbering `G^v = G_{ψ(v)}`;
Herbrand's theorem (quotient-compatibility of the upper numbering); concavity, the explicit
piecewise-linear formula, and the slope/derivative `φ'(u) = 1/(G_0 : G_u)`.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open MeasureTheory

namespace Anabelian

/-! ## The analytic engine: the Herbrand function of an abstract decreasing order-sequence -/

/-- Serre's index function: at "level" `t`, the relevant ramification group is `G_{herbrandIndex t}`
— `⌈t⌉` for `t > 0` and `G_0` for `t ≤ 0`. -/
noncomputable def herbrandIndex (t : ℝ) : ℕ := if t ≤ 0 then 0 else ⌊t⌋₊ + 1

theorem herbrandIndex_monotone : Monotone herbrandIndex := by
  intro s t hst
  simp only [herbrandIndex]
  split_ifs with hs ht ht
  · exact le_refl 0
  · exact Nat.zero_le _
  · exact absurd hst (not_le.mpr (lt_of_le_of_lt ht (not_le.mp hs)))
  · exact Nat.add_le_add_right (Nat.floor_mono hst) 1

/-- The integrand of Serre's Herbrand integral: `1/(G_0 : G_t) = g_{⌈t⌉}/g_0`, where `g i = |G_i|`
is the order sequence of the filtration. -/
noncomputable def herbrandIntegrand (g : ℕ → ℝ) (t : ℝ) : ℝ := g (herbrandIndex t) / g 0

theorem herbrandIntegrand_nonneg (g : ℕ → ℝ) (hgnn : ∀ i, 0 ≤ g i) (hg0 : 0 < g 0) (t : ℝ) :
    0 ≤ herbrandIntegrand g t :=
  div_nonneg (hgnn _) hg0.le

theorem herbrandIntegrand_pos (g : ℕ → ℝ) (hgpos : ∀ i, 0 < g i) (t : ℝ) :
    0 < herbrandIntegrand g t :=
  div_pos (hgpos _) (hgpos 0)

/-- The integrand is **antitone** — exactly because the filtration decreases (`g` antitone): the
acting group shrinks as the level rises, so its order, and hence the slope, drops. -/
theorem herbrandIntegrand_antitone (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0) :
    Antitone (herbrandIntegrand g) := by
  intro s t hst
  simp only [herbrandIntegrand, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hg (herbrandIndex_monotone hst)) (inv_nonneg.mpr hg0.le)

/-- **Serre's Herbrand function** of a decreasing sequence of group orders `g i = |G_i|`:
`φ(u) = ∫_0^u dt/(G_0 : G_t)`. -/
noncomputable def herbrandPhiSeq (g : ℕ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..u, herbrandIntegrand g t

/-- The integrand is interval integrable on every interval (it is antitone). -/
theorem herbrandPhiSeq_intervalIntegrable (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0)
    (a b : ℝ) : IntervalIntegrable (herbrandIntegrand g) volume a b :=
  (herbrandIntegrand_antitone g hg hg0).intervalIntegrable

theorem herbrandPhiSeq_zero (g : ℕ → ℝ) : herbrandPhiSeq g 0 = 0 := by
  simp only [herbrandPhiSeq, intervalIntegral.integral_same]

/-- `φ` is **monotone** (the integrand is `≥ 0`). -/
theorem herbrandPhiSeq_monotone (g : ℕ → ℝ) (hg : Antitone g) (hgnn : ∀ i, 0 ≤ g i)
    (hg0 : 0 < g 0) : Monotone (herbrandPhiSeq g) := by
  intro u v huv
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 u)
    (herbrandPhiSeq_intervalIntegrable g hg hg0 u v)
  have hnn : 0 ≤ ∫ t in u..v, herbrandIntegrand g t :=
    intervalIntegral.integral_nonneg huv (fun t _ => herbrandIntegrand_nonneg g hgnn hg0 t)
  simp only [herbrandPhiSeq]
  linarith [hadd, hnn]

/-- `φ` is **strictly increasing** (the integrand is `> 0`: every `|G_i| ≥ 1`). With continuity,
this is the precondition for the inverse `ψ = φ⁻¹`. -/
theorem herbrandPhiSeq_strictMono (g : ℕ → ℝ) (hg : Antitone g) (hgpos : ∀ i, 0 < g i) :
    StrictMono (herbrandPhiSeq g) := by
  intro u v huv
  have hg0 : 0 < g 0 := hgpos 0
  have hii := herbrandPhiSeq_intervalIntegrable g hg hg0 u v
  have hpos : 0 < ∫ t in u..v, herbrandIntegrand g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hii
      (fun t _ => herbrandIntegrand_pos g hgpos t) huv
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 u)
    (herbrandPhiSeq_intervalIntegrable g hg hg0 u v)
  simp only [herbrandPhiSeq]
  linarith [hadd, hpos]

/-- `φ(u) = u` for `u ≤ 0`: the acting group is `G_0` itself, so the slope `(G_0 : G_0)^{-1} = 1`.
(Serre's normalisation on `[-1, 0]`, here on all of `(-∞, 0]`.) -/
theorem herbrandPhiSeq_eq_id (g : ℕ → ℝ) (hg0 : 0 < g 0) {u : ℝ} (hu : u ≤ 0) :
    herbrandPhiSeq g u = u := by
  simp only [herbrandPhiSeq]
  have hcongr : Set.EqOn (herbrandIntegrand g) (fun _ => (1:ℝ)) (Set.uIcc 0 u) := by
    intro t ht
    rw [Set.uIcc_of_ge hu] at ht
    simp only [herbrandIntegrand, herbrandIndex, if_pos ht.2]
    exact div_self (ne_of_gt hg0)
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const]
  simp

/-- `φ` is **continuous** (`continuous_primitive` of an interval-integrable integrand). -/
theorem herbrandPhiSeq_continuous (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0) :
    Continuous (herbrandPhiSeq g) :=
  intervalIntegral.continuous_primitive (herbrandPhiSeq_intervalIntegrable g hg hg0) 0

/-- `φ(u) ≤ u` for `u ≥ 0`: every slope `g_{⌈t⌉}/g_0 ≤ 1` because `G_t ≤ G_0`. The genuine
ramification content separating `φ` from the identity. -/
theorem herbrandPhiSeq_le_id (g : ℕ → ℝ) (hg : Antitone g) (hg0 : 0 < g 0) {u : ℝ} (hu : 0 ≤ u) :
    herbrandPhiSeq g u ≤ u := by
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) u, herbrandIntegrand g t ≤ 1 := by
    intro t _
    simp only [herbrandIntegrand]
    rw [div_le_one hg0]
    exact hg (Nat.zero_le _)
  have h := intervalIntegral.integral_mono_on hu
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 u) intervalIntegrable_const hbound
  simp only [herbrandPhiSeq]
  rw [intervalIntegral.integral_const] at h
  simpa using h

/-! ## Instantiation on the lower-numbering ramification filtration -/

open ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- The order sequence `i ↦ |G_i|` of the ramification filtration, real-valued. -/
noncomputable def ramificationOrders (i : ℕ) : ℝ := Nat.card (ramificationGroup K A i)

/-- The orders decrease — the filtration is antitone (`ramificationGroup_antitone`) and order is
monotone under subgroup inclusion (`Subgroup.card_le_of_le`, the groups being finite). -/
theorem ramificationOrders_antitone [Finite (A.decompositionSubgroup K)] :
    Antitone (ramificationOrders K A) := by
  intro i j hij
  simp only [ramificationOrders]
  exact Nat.cast_le.mpr (Subgroup.card_le_of_le (ramificationGroup_antitone K A hij))

theorem ramificationOrders_nonneg (i : ℕ) : 0 ≤ ramificationOrders K A i :=
  Nat.cast_nonneg _

/-- Every order is positive: `G_i` is a nonempty finite group, so `|G_i| ≥ 1`. -/
theorem ramificationOrders_pos [Finite (A.decompositionSubgroup K)] (i : ℕ) :
    0 < ramificationOrders K A i :=
  Nat.cast_pos.mpr Nat.card_pos

/-- **The Herbrand function** `φ_{L/K}` of the extension (relative to the valuation subring `A` and
the lower-numbering filtration `G_i`): `φ(u) = ∫_0^u dt/(G_0 : G_t)` (Serre, *Local Fields*, IV §3).
-/
noncomputable def herbrandPhi : ℝ → ℝ := herbrandPhiSeq (ramificationOrders K A)

theorem herbrandPhi_zero : herbrandPhi K A 0 = 0 := herbrandPhiSeq_zero _

/-- **`φ` is strictly increasing** — the precondition (with continuity) for the inverse `ψ`. -/
theorem herbrandPhi_strictMono [Finite (A.decompositionSubgroup K)] :
    StrictMono (herbrandPhi K A) :=
  herbrandPhiSeq_strictMono _ (ramificationOrders_antitone K A) (ramificationOrders_pos K A)

theorem herbrandPhi_monotone [Finite (A.decompositionSubgroup K)] :
    Monotone (herbrandPhi K A) :=
  (herbrandPhi_strictMono K A).monotone

/-- `φ(u) = u` for `u ≤ 0`. -/
theorem herbrandPhi_eq_id [Finite (A.decompositionSubgroup K)] {u : ℝ} (hu : u ≤ 0) :
    herbrandPhi K A u = u :=
  herbrandPhiSeq_eq_id _ (ramificationOrders_pos K A 0) hu

/-- **`φ` is continuous**. -/
theorem herbrandPhi_continuous [Finite (A.decompositionSubgroup K)] :
    Continuous (herbrandPhi K A) :=
  herbrandPhiSeq_continuous _ (ramificationOrders_antitone K A) (ramificationOrders_pos K A 0)

/-- `φ(u) ≤ u` for `u ≥ 0` — the ramification content distinguishing `φ` from the identity. -/
theorem herbrandPhi_le_self [Finite (A.decompositionSubgroup K)] {u : ℝ} (hu : 0 ≤ u) :
    herbrandPhi K A u ≤ u :=
  herbrandPhiSeq_le_id _ (ramificationOrders_antitone K A) (ramificationOrders_pos K A 0) hu

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms herbrandIndex_monotone
#print axioms herbrandIntegrand_antitone
#print axioms herbrandPhiSeq
#print axioms herbrandPhiSeq_zero
#print axioms herbrandPhiSeq_monotone
#print axioms herbrandPhiSeq_strictMono
#print axioms herbrandPhiSeq_eq_id
#print axioms herbrandPhiSeq_continuous
#print axioms herbrandPhiSeq_le_id
#print axioms ramificationOrders_antitone
#print axioms ramificationOrders_pos
#print axioms herbrandPhi
#print axioms herbrandPhi_zero
#print axioms herbrandPhi_strictMono
#print axioms herbrandPhi_monotone
#print axioms herbrandPhi_eq_id
#print axioms herbrandPhi_continuous
#print axioms herbrandPhi_le_self

end Anabelian
