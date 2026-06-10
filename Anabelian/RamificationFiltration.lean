/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueReduction
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Rung L2, the opening: higher ramification groups in lower numbering (Pass 23)

Mathlib's `RingTheory/Valuation/RamificationGroup.lean` — the setting of Pass 4 — carries a literal
`TODO: Define higher ramification groups in lower numbering`. This file does so (at project level),
on the **corrected architecture** fixed by Pass 22: lower numbering is defined for a valuation
subring `A` of `L/K` and is *non-vacuous exactly when the powers of `𝔪_A` separate* — true at
finite level (DVRs, Krull), provably false for `𝒪[K̄]` (the Pass-22 idempotency). The filtration is
therefore developed *abstractly with the separation hypothesis explicit*, and the hypothesis is
discharged in the Noetherian (= field-or-DVR, the finite-level) case.

## Definitions and results (Serre, *Local Fields*, ch. IV §1; all axiom-free)

For `A : ValuationSubring L` with the `Gal(L/K)`-decomposition-group action of Mathlib's
`RamificationGroup.lean`:

* `Anabelian.ramificationGroup K A i` — **the `i`-th ramification group in lower numbering**:
  `G_i = {σ ∈ decompositionSubgroup | ∀ a ∈ A, σa − a ∈ 𝔪_A^(i+1)}` (`Ideal.inertia` of
  `𝔪_A^(i+1)`, the same device as Pass 21's `galoisInertia`, at the right level). ℕ-indexed with
  `G_0` = inertia; Serre's `G_{−1}` is the ambient decomposition group itself.
* `Anabelian.mem_ramificationGroup_iff` — the defining membership, unfolded.
* `Anabelian.smul_mem_maximalIdeal_pow` — the **crux**: the decomposition action preserves
  `𝔪_A^n` (each `σ` is a ring automorphism of the local `A`, so fixes `𝔪_A` setwise, hence its
  powers — via `Ideal.map_pow` + `map_isMaximal_of_equiv` + local uniqueness).
* `Anabelian.ramificationGroup_antitone` — `G_j ≤ G_i` for `i ≤ j`.
* `Anabelian.ramificationGroup_zero` — **`G_0` is the inertia subgroup**, literally Mathlib's
  `ValuationSubring.inertiaSubgroup` (the kernel of the residue action) — tying the filtration to
  the Pass-4 API via `residue_smul` and the pointwise characterization `mem_inertiaSubgroup_iff`.
* `Anabelian.ramificationGroup_normal` — each `G_i` is **normal in the decomposition group**
  (Serre IV §1 Prop. 1): conjugation transports the inertia condition along
  `smul_mem_maximalIdeal_pow`.
* `Anabelian.iInf_ramificationGroup_eq_bot` — **separation**: if `⨅ n, 𝔪_A^n = ⊥` (Krull
  intersection), then `⨅ i, G_i = ⊥`. A `σ` in every `G_i` fixes `A` pointwise, hence fixes `L`
  (for `l ∉ A`, `l⁻¹ ∈ A` — the valuation-subring dichotomy), hence `σ = 1`.
* `Anabelian.iInf_ramificationGroup_eq_bot_of_isNoetherianRing` — the hypothesis **discharged in
  the Noetherian case** via Mathlib's Krull intersection theorem
  (`Ideal.iInf_pow_eq_bot_of_isLocalRing`). A Noetherian valuation ring is a field or a DVR — this
  is exactly the finite-level (`𝒪_L` for finite `L/K`) case the corrected L2 architecture targets.
* `Anabelian.exists_notMem_ramificationGroup` — the per-element escape: under separation, every
  `σ ≠ 1` leaves some `G_i`.

## Non-vacuity, honestly (the Pass-22 contrast)

The separation hypothesis is stated explicitly because Pass 22 *proved* it fails in the
infinite-level case: for `A`-like `𝒪[K̄]` the maximal ideal is idempotent
(`maximalIdeal_galoisIntegers_sq`), the powers do not separate, and the filtration provably
collapses (`inertia_maximalIdeal_pow_collapse`). The two regimes — collapsing (idempotent `𝔪`,
divisible value group) and separating (DVR, Krull) — are now *both proved*, which is what makes
the hypothesis-parametrized statement the right abstract shape. (No claim is made that the Krull
hypothesis is irremovable from the *conclusion* `⨅ G_i = ⊥` — that would require a constructed
`A` with non-separating powers *and* a nontrivial inertia element, which is not attempted here.)

What this pass does **not** yet provide, logged in `ROADMAP.md` (L2):
* a concrete properly-decreasing chain (`G_0 ≠ G_1` for an explicitly ramified extension) — the
  come-apart exhibit that the definition eventually deserves;
* eventual triviality `∃ i, G_i = ⊥` for finite decomposition groups (the `⨅ = ⊥` +
  antitone-in-a-finite-group epsilon);
* the tame quotient `G_0/G_1 ↪ 𝓀^×`, wild `G_1` pro-`p`, Herbrand `φ`/`ψ`, upper numbering;
* the local-field instantiation `A = 𝒪_L`, `L/K` finite — blocked on the (verified absent)
  finite-extension `IsNonarchimedeanLocalField` instances.

**Not reconstruction.** Structure of the Galois action of given fields; no reach toward R1–R3.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged. No new `structure`/`class` (the filtration is a `Subgroup`-valued `def`).
D1 N/A; D2 N/A (no spectral structure; the file is `ValuationSubring`-native).
-/

open scoped Pointwise

namespace Anabelian

open ValuationSubring IsLocalRing

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- **The `i`-th ramification group in lower numbering** (Serre, *Local Fields*, IV §1):
`G_i = {σ ∈ decompositionSubgroup K A | ∀ a : A, σ a − a ∈ 𝔪_A^(i+1)}`, as `Ideal.inertia` of
`𝔪_A^(i+1)` under Mathlib's decomposition-group action on `A`. ℕ-indexed: `G_0` is the inertia
subgroup (`ramificationGroup_zero`); Serre's `G_{−1}` is the ambient decomposition group. This
fills (at project level) the `TODO: Define higher ramification groups in lower numbering` of
`Mathlib/RingTheory/Valuation/RamificationGroup.lean`. -/
noncomputable def ramificationGroup (i : ℕ) : Subgroup (A.decompositionSubgroup K) :=
  (maximalIdeal ↥A ^ (i + 1)).inertia (A.decompositionSubgroup K)

/-- Membership in `G_i`, unfolded: `σ` moves every integer by an element of `𝔪_A^(i+1)`. -/
theorem mem_ramificationGroup_iff {i : ℕ} (σ : A.decompositionSubgroup K) :
    σ ∈ ramificationGroup K A i ↔
      ∀ a : ↥A, σ • a - a ∈ maximalIdeal ↥A ^ (i + 1) :=
  AddSubgroup.mem_inertia

/-- **The crux:** the decomposition action preserves every power of the maximal ideal. Each `τ`
acts on `A` as a ring automorphism, which fixes the (unique) maximal ideal setwise
(`map_isMaximal_of_equiv` + `eq_maximalIdeal`), hence fixes its powers (`Ideal.map_pow`). -/
theorem smul_mem_maximalIdeal_pow (τ : A.decompositionSubgroup K) {n : ℕ} {x : ↥A}
    (hx : x ∈ maximalIdeal ↥A ^ n) : τ • x ∈ maximalIdeal ↥A ^ n := by
  set e := MulSemiringAction.toRingAut (A.decompositionSubgroup K) ↥A τ with he
  have hmax : (maximalIdeal ↥A).map e = maximalIdeal ↥A := eq_maximalIdeal inferInstance
  have hmem : e x ∈ (maximalIdeal ↥A ^ n).map e := Ideal.mem_map_of_mem _ hx
  rwa [Ideal.map_pow, hmax] at hmem

/-- The ramification filtration is **antitone**: `G_j ≤ G_i` for `i ≤ j`
(`𝔪_A^(j+1) ≤ 𝔪_A^(i+1)`). -/
theorem ramificationGroup_antitone : Antitone (ramificationGroup K A) := by
  intro i j hij σ hσ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  intro a
  exact Ideal.pow_le_pow_right (by omega) (hσ a)

/-- **`G_0` is the inertia subgroup** — literally Mathlib's `ValuationSubring.inertiaSubgroup`
(the kernel of the residue-field action, Pass 4's object): moving every integer by an element of
`𝔪_A` is the same as acting trivially on the residue field. Ties the filtration's base to the
Pass-4 API (`mem_inertiaSubgroup_iff`) via `residue_smul`. -/
theorem ramificationGroup_zero :
    ramificationGroup K A 0 = A.inertiaSubgroup K := by
  have hres : ∀ u v : ↥A, residue ↥A u = residue ↥A v ↔ u - v ∈ maximalIdeal ↥A :=
    fun u v => Ideal.Quotient.mk_eq_mk_iff_sub_mem u v
  ext σ
  rw [mem_ramificationGroup_iff, mem_inertiaSubgroup_iff]
  constructor
  · intro h x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : residue ↥A (σ • a) = residue ↥A a := (hres _ _).mpr (by simpa using h a)
    calc MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField ↥A) σ
          (Ideal.Quotient.mk _ a)
        = residue ↥A (σ • a) := rfl
      _ = residue ↥A a := h1
  · intro h a
    have h1 : residue ↥A (σ • a) = residue ↥A a := h (residue ↥A a)
    simpa using (hres _ _).mp h1

/-- Each ramification group is **normal in the decomposition group** (Serre IV §1 Prop. 1):
conjugating the inertia condition transports along `smul_mem_maximalIdeal_pow`. -/
instance ramificationGroup_normal (i : ℕ) : (ramificationGroup K A i).Normal := by
  constructor
  intro σ hσ τ
  rw [mem_ramificationGroup_iff] at hσ ⊢
  intro a
  have key : (τ * σ * τ⁻¹) • a - a = τ • (σ • (τ⁻¹ • a) - τ⁻¹ • a) := by
    rw [mul_smul, mul_smul, smul_sub, smul_inv_smul]
  rw [key]
  exact smul_mem_maximalIdeal_pow K A τ (hσ _)

/-- **Separation**: if the powers of `𝔪_A` separate (`⨅ n, 𝔪_A^n = ⊥`, the Krull-intersection
property), the ramification filtration separates: `⨅ i, G_i = ⊥`. A `σ` lying in every `G_i`
fixes `A` pointwise, hence fixes all of `L` (for `l ∉ A` use `l⁻¹ ∈ A` — the valuation-subring
dichotomy `mem_or_inv_mem`), hence is the identity. The hypothesis is exactly what the Pass-22
degeneracy shows can fail (idempotent `𝔪[K̄]`); it holds in the Noetherian case below. -/
theorem iInf_ramificationGroup_eq_bot (h : (⨅ n : ℕ, maximalIdeal ↥A ^ n) = ⊥) :
    (⨅ i : ℕ, ramificationGroup K A i) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  have hfix : ∀ a : ↥A, σ • a = a := by
    intro a
    have hmem : σ • a - a ∈ (⨅ n : ℕ, maximalIdeal ↥A ^ n) := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ m =>
        have hm := (Subgroup.mem_iInf.mp hσ) m
        rw [mem_ramificationGroup_iff] at hm
        exact hm a
    rw [h] at hmem
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hmem)
  have hfixL : ∀ l : L, (σ : L ≃ₐ[K] L) l = l := by
    intro l
    rcases A.mem_or_inv_mem l with hl | hl
    · exact congrArg Subtype.val (hfix ⟨l, hl⟩)
    · have h2 : (σ : L ≃ₐ[K] L) l⁻¹ = l⁻¹ := congrArg Subtype.val (hfix ⟨l⁻¹, hl⟩)
      rw [map_inv₀] at h2
      exact inv_injective h2
  apply Subtype.ext
  apply AlgEquiv.ext
  intro l
  exact hfixL l

/-- Separation in the **Noetherian** case — the Krull hypothesis discharged by Mathlib's Krull
intersection theorem. A Noetherian valuation ring is a field or a DVR: this is exactly the
finite-level case (`A = 𝒪_L`, `L/K` finite) of the corrected L2 architecture, where the
filtration genuinely separates — in proved contrast to the Pass-22 collapse at `𝒪[K̄]`. -/
theorem iInf_ramificationGroup_eq_bot_of_isNoetherianRing [IsNoetherianRing ↥A] :
    (⨅ i : ℕ, ramificationGroup K A i) = ⊥ :=
  iInf_ramificationGroup_eq_bot K A
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top')

/-- Per-element escape: under separation, every `σ ≠ 1` in the decomposition group leaves some
ramification group. (The eventual triviality `∃ i, G_i = ⊥` for *finite* decomposition groups is
the next epsilon — `ROADMAP.md`.) -/
theorem exists_notMem_ramificationGroup (h : (⨅ n : ℕ, maximalIdeal ↥A ^ n) = ⊥)
    {σ : A.decompositionSubgroup K} (hσ : σ ≠ 1) :
    ∃ i, σ ∉ ramificationGroup K A i := by
  by_contra hc
  have hall : ∀ i, σ ∈ ramificationGroup K A i := fun i =>
    not_not.mp fun hni => hc ⟨i, hni⟩
  exact hσ ((Subgroup.eq_bot_iff_forall _).mp (iInf_ramificationGroup_eq_bot K A h) σ
    (Subgroup.mem_iInf.mpr hall))

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms ramificationGroup
#print axioms mem_ramificationGroup_iff
#print axioms smul_mem_maximalIdeal_pow
#print axioms ramificationGroup_antitone
#print axioms ramificationGroup_zero
#print axioms ramificationGroup_normal
#print axioms iInf_ramificationGroup_eq_bot
#print axioms iInf_ramificationGroup_eq_bot_of_isNoetherianRing
#print axioms exists_notMem_ramificationGroup

end Anabelian
