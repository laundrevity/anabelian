/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Ramification.TameInjectivity
import Anabelian.Ramification.LowerIndex
import Anabelian.Extension.Monogenic
import Anabelian.Extension.Uniformizer
import Mathlib

/-!
# The ascent: the concrete `i_G` — `i_G(σ) = v_L(σx − x)` (Serre IV §1 Lemma 1) (Pass 53)

Pass 51 defined Serre's `i_G` generator-free (`lowerIndex K A σ = sup {n | ∀ a, σa − a ∈ 𝔪^n}`)
and proved the filtration characterization. This pass supplies the **concrete half of Lemma 1**:
under the monogenicity package, the universally-quantified condition collapses to the single
generator, and `i_G(σ)` **is the valuation `v_L(σx − x)`** — Mathlib's `addVal` on the DVR
`𝒪_L`. This is the exact form Serre IV §1 Prop. 3 (the `i_{K'/K}` sum formula, the next wall)
computes with.

The engine already existed: Pass 25's `smul_sub_dvd_of_mem_closure` — `σ` fixes `A₀` pointwise
⟹ `(σx − x) ∣ (σa − a)` for every `a ∈ closure (A₀ ∪ {x})` (Serre's telescoping) — and its
detection corollary `mem_ramificationGroup_of_smul_uniformizer_sub_mem`. What was missing is
assembled here: the **iff** (the `⟹` direction is instantiation at `a := x`), the resulting
**set-level collapse** of `lowerIndex`'s defining condition, and the **`addVal` identification**
through a small DVR bridge (`x ∈ 𝔪^n ↔ n ≤ addVal x`) that Mathlib does not state.

The monogenicity package is carried exactly as Passes 25/27/28 carried it — **named hypothesis
binders** `(hgen : Subring.closure (↑A₀ ∪ {x}) = ⊤)` + `(hfix : ∀ a ∈ A₀, σ • a = a)` — with
`hfix` **free at `𝒪_L`** for `A₀ = range (𝒪_K → 𝒪_L)` (Pass 32's
`smul_extensionAlgebraMap_range_eq`), and `hgen` the classical monogenicity of local fields
(Serre III §6 Prop. 12), **not yet discharged in-project** (an honest named boundary, same
status as in Passes 25–28; its discharge is separate future work, NOT assumed).

## What is proved (all axiom-free)

* `mem_maximalIdeal_pow_iff_le_addVal` — the DVR bridge: `x ∈ 𝔪^n ↔ (n : ℕ∞) ≤ addVal R x`
  (`𝔪^n = (ϖ^n)`, `addVal_le_iff_dvd`, `addVal (ϖ^n) = n`).
* `forall_smul_sub_mem_iff_generator` — the one-generator collapse:
  `(∀ a, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n` (`⟸` is Pass 25's detection; `⟹` is `a := x`).
* `mem_ramificationGroup_iff_smul_generator_sub_mem` — Lemma 1, generator form:
  `σ ∈ G_i ↔ σx − x ∈ 𝔪^(i+1)`.
* **`lowerIndex_eq_addVal`** — the headline: `i_G(σ) = addVal (σx − x) = v_L(σx − x)` on any
  DVR valuation subring, under the package.
* `lowerIndex_extensionIntegers_eq_addVal` — at `𝒪_L` (`L/K` finite separable over a
  nonarchimedean local field): `hfix` discharged by Pass 32, the DVR instance by Pass 35's
  `isDiscreteValuationRing_extensionIntegers`; only `hgen` remains a named binder.

## Honesty

Structure of the Galois action of given fields — **no reach toward R1–R3**; nothing recovered
from an abstract group. The monogenicity hypothesis `hgen` is a **named binder**, exactly the
Pass-25/27/28 discipline: it is *not* claimed discharged, *not* axiomatized (nothing enters the
kernel — `#print axioms` below is standard-only), and its in-project discharge (Serre III §6:
local fields with separable residue extension are monogenic) is named future work in
`ROADMAP.md`'s L2 rung. No load-bearing-hypothesis *claim* is made for `hgen`/`hfix` (they are
sufficient conditions; necessity is not asserted) — no owed witness. No new `structure`/`class`;
D1 N/A; D2 stays inside Pass 29's proofs (only `IsIntegral`-level API consumed here).

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

/-- **The DVR bridge**: membership in the `n`-th power of the maximal ideal is `n ≤ addVal`.
(`𝔪 = (ϖ)` for an irreducible `ϖ`, so `𝔪^n = (ϖ^n)`, and `ϖ^n ∣ x ↔ addVal (ϖ^n) ≤ addVal x`
with `addVal (ϖ^n) = n`.) Mathlib has the ingredients but not this statement. -/
theorem mem_maximalIdeal_pow_iff_le_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {x : R} {n : ℕ} :
    x ∈ maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal R x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      ← IsDiscreteValuationRing.addVal_le_iff_dvd, hϖ.addVal_pow]

section Abstract

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable {A₀ : Subring ↥A}

/-- **The one-generator collapse** (Serre IV §1, the step behind Lemma 1): under the
monogenicity package (`hgen`, `hfix`), the universally-quantified ramification condition
collapses to the generator — `(∀ a, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n`. `⟹` is `a := x`; `⟸` is
Pass 25's detection (`smul_sub_dvd_of_mem_closure` telescoping). -/
theorem forall_smul_sub_mem_iff_generator {x : ↥A}
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {x}) = ⊤)
    {σ : A.decompositionSubgroup K} (hfix : ∀ a ∈ A₀, σ • a = a) (n : ℕ) :
    (∀ a : ↥A, σ • a - a ∈ maximalIdeal ↥A ^ n) ↔ σ • x - x ∈ maximalIdeal ↥A ^ n := by
  constructor
  · intro h
    exact h x
  · intro h
    cases n with
    | zero => intro a; simp
    | succ i =>
      have hmem := mem_ramificationGroup_of_smul_uniformizer_sub_mem K hgen hfix h
      rw [mem_ramificationGroup_iff] at hmem
      exact hmem

/-- **Serre IV §1 Lemma 1, generator form**: `σ ∈ G_i ↔ σx − x ∈ 𝔪^(i+1)` — the filtration is
detected on the single generator. (Upgrades Pass 25's one-directional detection to an iff.) -/
theorem mem_ramificationGroup_iff_smul_generator_sub_mem {x : ↥A}
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {x}) = ⊤)
    {σ : A.decompositionSubgroup K} (hfix : ∀ a ∈ A₀, σ • a = a) {i : ℕ} :
    σ ∈ ramificationGroup K A i ↔ σ • x - x ∈ maximalIdeal ↥A ^ (i + 1) := by
  rw [mem_ramificationGroup_iff]
  exact forall_smul_sub_mem_iff_generator K A hgen hfix (i + 1)

/-- **The concrete `i_G`** (the headline): on a DVR valuation subring, under the monogenicity
package, `i_G(σ) = v_L(σx − x)` — Pass 51's generator-free `lowerIndex` is Mathlib's `addVal`
of the generator displacement. The form Serre IV §1 Prop. 3 computes with. -/
theorem lowerIndex_eq_addVal [IsDiscreteValuationRing ↥A] {x : ↥A}
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {x}) = ⊤)
    {σ : A.decompositionSubgroup K} (hfix : ∀ a ∈ A₀, σ • a = a) :
    lowerIndex K A σ = IsDiscreteValuationRing.addVal ↥A (σ • x - x) := by
  refine enat_eq_of_forall_natCast_lt_iff fun n => ?_
  rw [← mem_ramificationGroup_iff_lt_lowerIndex,
      mem_ramificationGroup_iff_smul_generator_sub_mem K A hgen hfix,
      mem_maximalIdeal_pow_iff_le_addVal]
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top n)]
  norm_cast

end Abstract

section Instantiate

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The concrete `i_G` at `𝒪_L` (`L/K` finite separable over a nonarchimedean local field):
`i_G(σ) = v_L(σx − x)` for any ring generator `x` of `𝒪_L` over `𝒪_K`. The `hfix` half of the
package is free (Pass 32: decomposition elements fix the base image pointwise); the DVR
structure is Pass 35's instance; `hgen` — the classical monogenicity of local fields (Serre III
§6 Prop. 12) — remains a **named hypothesis** (the Pass-25/27/28 discipline), its in-project
discharge being separate future work. -/
theorem lowerIndex_extensionIntegers_eq_addVal [Algebra.IsSeparable K L]
    {x : ↥(extensionIntegers K L)}
    (hgen : Subring.closure
        (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}) = ⊤)
    (σ : (extensionIntegers K L).decompositionSubgroup K) :
    lowerIndex K (extensionIntegers K L) σ
      = IsDiscreteValuationRing.addVal ↥(extensionIntegers K L) (σ • x - x) :=
  lowerIndex_eq_addVal K (extensionIntegers K L) hgen
    (fun a ha => smul_extensionAlgebraMap_range_eq K L σ a ha)

end Instantiate

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms mem_maximalIdeal_pow_iff_le_addVal
#print axioms forall_smul_sub_mem_iff_generator
#print axioms mem_ramificationGroup_iff_smul_generator_sub_mem
#print axioms lowerIndex_eq_addVal
#print axioms lowerIndex_extensionIntegers_eq_addVal

end Anabelian
