/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.HerbrandFunction
import Mathlib

/-!
# The ascent, rung 2: the inverse Herbrand function `ψ` and the upper numbering (Pass 45)

Pass 44 built the Herbrand function `φ` (`Anabelian/HerbrandFunction.lean`) and proved it strictly
monotone and continuous. This file inverts it and defines the upper numbering — Serre, *Local
Fields*, ch. IV §3, continued.

> **`ψ = φ⁻¹`** (`herbrandPsi`) and **`G^v(L/K) = G_{⌈ψ(v)⌉}`** (`upperRamificationGroup`).

The upper numbering is the indexing of the ramification filtration that is **compatible with passage
to quotients** `Gal(L/K) ↠ Gal(M/K)` (Herbrand's theorem) — the form that ultimately glues up
towers. Here we construct it and prove its elementary properties; its defining
quotient-compatibility (Herbrand's theorem proper) is the next, harder rung.

## What is proved (all axiom-free)

* **`φ` is surjective** (`herbrandPhiSeq_surjective`): `φ` is continuous, `→ -∞` at `-∞` (it is `id`
  there) and `→ +∞` at `+∞` (since `φ(u) ≥ u/g_0`, the orders being `≥ 1`), hence onto `ℝ`
  (`Continuous.surjective`). With strict monotonicity it is a homeomorphism `ℝ ≃ ℝ`.
* **`ψ = φ⁻¹`** (`herbrandPsi`, via `Function.invFun`), with the inverse identities
  `herbrandPhi_psi` (`φ(ψ v) = v`) and `herbrandPsi_phi` (`ψ(φ u) = u`), and `ψ` **strictly
  monotone** (`herbrandPsi_strictMono`), **continuous** (`herbrandPsi_continuous`, via the
  order-iso → homeomorphism of `StrictMono.orderIsoOfSurjective`), `ψ(0)=0`, `ψ=id` on `(-∞,0]`.
* **The upper numbering** `G^v` (`upperRamificationGroup`) with: `G^0 = G_0`
  (`upperRamificationGroup_zero` — inertia, since `ψ(0)=0`), **antitone in `v`**
  (`upperRamificationGroup_antitone`), and **eventually `⊥`**
  (`upperRamificationGroup_eventually_bot` — under the lower numbering's separation hypothesis,
  via `ψ(φ i) = i`).

As with `φ`, `ψ` is built as a reusable analytic engine `herbrandPsiSeq` on an abstract sequence of
orders `g i = |G_i|` (with `1 ≤ g i`), then instantiated on the real ramification orders.

## Honesty

`ψ` and `G^v` are structural invariants of a given extension's ramification filtration — **no reach
toward R1–R3**; nothing is recovered from an abstract group. The instantiation carries
`[Finite (A.decompositionSubgroup K)]` (automatic at the intended finite level `A = 𝒪_L`, `L/K`
finite; it gives `|G_i| ≥ 1`, needed for surjectivity and for `ψ` to exist), a standing finiteness,
**not** a claimed-essential hypothesis — no rule-2 come-apart / owed witness.
`upperRamificationGroup` is a `def` of a `Subgroup`-valued function; it is **not vacuous**
(`G^0 = G_0`, antitone, eventually
`⊥` are proved constraints), but its full justification — **quotient-compatibility (Herbrand's
theorem)** — is the next rung, not claimed here. No new `structure`/`class`; D1 N/A; D2 N/A.

**NOT yet built:** Herbrand's theorem `(G/H)^v = G^v H/H`; `φ`-transitivity `φ_{L/K} = φ_{M/K} ∘
φ_{L/M}`; the lower-numbering subgroup compatibility `H_u = H ∩ G_u` (a prerequisite for both);
Hasse–Arf.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open MeasureTheory Filter Topology

namespace Anabelian

/-! ## The analytic engine: inverting `φ` of an abstract order-sequence -/

/-- Lower bound `φ(u) ≥ u/g_0` for `u ≥ 0`: every order is `≥ 1`, so the integrand is `≥ 1/g_0`. -/
theorem herbrandPhiSeq_div_le (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) {u : ℝ}
    (hu : 0 ≤ u) : u / g 0 ≤ herbrandPhiSeq g u := by
  have hg0 : 0 < g 0 := lt_of_lt_of_le one_pos (hg1 0)
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) u, (1 / g 0) ≤ herbrandIntegrand g t := by
    intro t _
    simp only [herbrandIntegrand]
    gcongr
    exact hg1 _
  have h := intervalIntegral.integral_mono_on hu intervalIntegrable_const
    (herbrandPhiSeq_intervalIntegrable g hg hg0 0 u) hbound
  simp only [herbrandPhiSeq]
  rw [intervalIntegral.integral_const] at h
  simpa using h

/-- **`φ` is surjective** onto `ℝ`: continuous, `→ +∞` at `+∞` (it dominates `u/g_0`) and `→ -∞` at
`-∞` (it is `id` there). -/
theorem herbrandPhiSeq_surjective (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) :
    Function.Surjective (herbrandPhiSeq g) := by
  have hg0 : 0 < g 0 := lt_of_lt_of_le one_pos (hg1 0)
  refine (herbrandPhiSeq_continuous g hg hg0).surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const hg0)
    exact eventually_atTop.mpr ⟨0, fun u hu => herbrandPhiSeq_div_le g hg hg1 hu⟩
  · refine tendsto_id.congr' (eventually_atBot.mpr ⟨0, fun u hu => ?_⟩)
    exact (herbrandPhiSeq_eq_id g hg0 hu).symm

/-- **The inverse Herbrand function** `ψ = φ⁻¹`. -/
noncomputable def herbrandPsiSeq (g : ℕ → ℝ) : ℝ → ℝ := Function.invFun (herbrandPhiSeq g)

theorem herbrandPhiSeq_psiSeq (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) (v : ℝ) :
    herbrandPhiSeq g (herbrandPsiSeq g v) = v :=
  Function.rightInverse_invFun (herbrandPhiSeq_surjective g hg hg1) v

theorem herbrandPsiSeq_phiSeq (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) (u : ℝ) :
    herbrandPsiSeq g (herbrandPhiSeq g u) = u :=
  Function.leftInverse_invFun
    (herbrandPhiSeq_strictMono g hg (fun i => lt_of_lt_of_le one_pos (hg1 i))).injective u

theorem herbrandPsiSeq_zero (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) :
    herbrandPsiSeq g 0 = 0 := by
  have := herbrandPsiSeq_phiSeq g hg hg1 0
  rwa [herbrandPhiSeq_zero] at this

/-- `ψ` is **strictly increasing** (it inverts the strictly-increasing `φ`). -/
theorem herbrandPsiSeq_strictMono (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) :
    StrictMono (herbrandPsiSeq g) := by
  have hφ := herbrandPhiSeq_strictMono g hg (fun i => lt_of_lt_of_le one_pos (hg1 i))
  intro v w hvw
  have h : herbrandPhiSeq g (herbrandPsiSeq g v) < herbrandPhiSeq g (herbrandPsiSeq g w) := by
    rw [herbrandPhiSeq_psiSeq g hg hg1, herbrandPhiSeq_psiSeq g hg hg1]; exact hvw
  exact hφ.lt_iff_lt.mp h

theorem herbrandPsiSeq_eq_id (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) {v : ℝ}
    (hv : v ≤ 0) : herbrandPsiSeq g v = v := by
  have hg0 : 0 < g 0 := lt_of_lt_of_le one_pos (hg1 0)
  have := herbrandPsiSeq_phiSeq g hg hg1 v
  rwa [herbrandPhiSeq_eq_id g hg0 hv] at this

/-- `ψ` is **continuous**: `φ` is a strictly-monotone surjection, hence an order isomorphism
(`StrictMono.orderIsoOfSurjective`), hence a homeomorphism — and `ψ` is its inverse. -/
theorem herbrandPsiSeq_continuous (g : ℕ → ℝ) (hg : Antitone g) (hg1 : ∀ i, 1 ≤ g i) :
    Continuous (herbrandPsiSeq g) := by
  have hφmono := herbrandPhiSeq_strictMono g hg (fun i => lt_of_lt_of_le one_pos (hg1 i))
  have hsurj := herbrandPhiSeq_surjective g hg hg1
  have hψe : herbrandPsiSeq g = ⇑(hφmono.orderIsoOfSurjective (herbrandPhiSeq g) hsurj).symm := by
    funext v
    apply hφmono.injective
    rw [herbrandPhiSeq_psiSeq g hg hg1 v]
    exact (StrictMono.orderIsoOfSurjective_self_symm_apply (herbrandPhiSeq g) hφmono hsurj v).symm
  rw [hψe]
  exact (hφmono.orderIsoOfSurjective (herbrandPhiSeq g) hsurj).symm.toHomeomorph.continuous

/-! ## Instantiation on the ramification filtration, and the upper numbering -/

open ValuationSubring IsLocalRing

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- Every ramification order is `≥ 1` (`G_i` is a nonempty finite group). -/
theorem ramificationOrders_one_le [Finite (A.decompositionSubgroup K)] (i : ℕ) :
    1 ≤ ramificationOrders K A i :=
  Nat.one_le_cast.mpr Nat.card_pos

/-- **The inverse Herbrand function** `ψ_{L/K} = φ⁻¹` of the extension. -/
noncomputable def herbrandPsi : ℝ → ℝ := herbrandPsiSeq (ramificationOrders K A)

theorem herbrandPhi_psi [Finite (A.decompositionSubgroup K)] (v : ℝ) :
    herbrandPhi K A (herbrandPsi K A v) = v :=
  herbrandPhiSeq_psiSeq _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A) v

theorem herbrandPsi_phi [Finite (A.decompositionSubgroup K)] (u : ℝ) :
    herbrandPsi K A (herbrandPhi K A u) = u :=
  herbrandPsiSeq_phiSeq _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A) u

theorem herbrandPsi_zero [Finite (A.decompositionSubgroup K)] : herbrandPsi K A 0 = 0 :=
  herbrandPsiSeq_zero _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A)

theorem herbrandPsi_strictMono [Finite (A.decompositionSubgroup K)] :
    StrictMono (herbrandPsi K A) :=
  herbrandPsiSeq_strictMono _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A)

theorem herbrandPsi_continuous [Finite (A.decompositionSubgroup K)] :
    Continuous (herbrandPsi K A) :=
  herbrandPsiSeq_continuous _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A)

theorem herbrandPsi_eq_id [Finite (A.decompositionSubgroup K)] {v : ℝ} (hv : v ≤ 0) :
    herbrandPsi K A v = v :=
  herbrandPsiSeq_eq_id _ (ramificationOrders_antitone K A) (ramificationOrders_one_le K A) hv

/-- **The upper-numbering ramification group** `G^v(L/K) = G_{⌈ψ(v)⌉}` (Serre, *Local Fields*,
IV §3): the lower-numbering filtration reindexed through `ψ`. -/
noncomputable def upperRamificationGroup (v : ℝ) : Subgroup (A.decompositionSubgroup K) :=
  ramificationGroup K A ⌈herbrandPsi K A v⌉₊

/-- `G^0 = G_0` (the inertia subgroup), since `ψ(0) = 0`. -/
theorem upperRamificationGroup_zero [Finite (A.decompositionSubgroup K)] :
    upperRamificationGroup K A 0 = ramificationGroup K A 0 := by
  unfold upperRamificationGroup
  rw [herbrandPsi_zero K A, Nat.ceil_zero]

/-- The upper numbering is **antitone** in `v` (`ψ` monotone, `⌈·⌉₊` monotone, the filtration
antitone). -/
theorem upperRamificationGroup_antitone [Finite (A.decompositionSubgroup K)] :
    Antitone (upperRamificationGroup K A) := fun _ _ hvw =>
  ramificationGroup_antitone K A (Nat.ceil_mono ((herbrandPsi_strictMono K A).monotone hvw))

/-- The upper numbering is **eventually `⊥`** (under the lower-numbering separation hypothesis):
some `G_i = ⊥`, and `G^{φ(i)} = G_{⌈ψ(φ i)⌉} = G_i` since `ψ(φ i) = i`. -/
theorem upperRamificationGroup_eventually_bot [Finite (A.decompositionSubgroup K)]
    (h : (⨅ n : ℕ, maximalIdeal ↥A ^ n) = ⊥) :
    ∃ v, upperRamificationGroup K A v = ⊥ := by
  obtain ⟨i, hi⟩ := exists_ramificationGroup_eq_bot K A h
  refine ⟨herbrandPhi K A i, ?_⟩
  unfold upperRamificationGroup
  rw [herbrandPsi_phi K A (i : ℝ), Nat.ceil_natCast]
  exact hi

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms herbrandPhiSeq_div_le
#print axioms herbrandPhiSeq_surjective
#print axioms herbrandPsiSeq
#print axioms herbrandPhiSeq_psiSeq
#print axioms herbrandPsiSeq_phiSeq
#print axioms herbrandPsiSeq_zero
#print axioms herbrandPsiSeq_strictMono
#print axioms herbrandPsiSeq_eq_id
#print axioms herbrandPsiSeq_continuous
#print axioms ramificationOrders_one_le
#print axioms herbrandPsi
#print axioms herbrandPhi_psi
#print axioms herbrandPsi_phi
#print axioms herbrandPsi_zero
#print axioms herbrandPsi_strictMono
#print axioms herbrandPsi_continuous
#print axioms herbrandPsi_eq_id
#print axioms upperRamificationGroup
#print axioms upperRamificationGroup_zero
#print axioms upperRamificationGroup_antitone
#print axioms upperRamificationGroup_eventually_bot

end Anabelian
