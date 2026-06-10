/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.InertiaFixedIntegers
import Anabelian.TameInjectivity

/-!
# The descent, rung 6 (second half): the engine generalized; the GENERAL kernel theorem (Pass 34)

The Pass-32 engine, re-examined: its Nakayama spine never used the specific base
`A₀ = range(𝒪[K])` — only that the generated subring `S` *contains* the base image (so `S` is an
`𝒪[K]`-submodule) and that the digit residues come from `A₀`. So it generalizes verbatim:

* **`closure_subring_union_uniformizer_eq_top`** — for ANY subring `A₀` containing the base
  image: residues covered by `A₀` ⟹ `Subring.closure (A₀ ∪ {π}) = ⊤` (the `he` input is
  Pass 33's unconditional lemma).
* **`ker_tameCharacter_of_inertiaFixed_cover`** — the **general-case kernel theorem**: for ANY
  finite separable `L/K` and any uniformizer, if the inertia-fixed integers cover the residue
  field (`hresid` — classically: `L/L₀` is totally ramified, ALWAYS true), then
  **`ker θ₀ = G₁`**.

After this pass, the general case of Serre IV §2 Prop. 7 (level 0) on actual local fields hangs
on exactly **one named classical lemma** — `hresid`, the residue-coverage by inertia-fixed
elements — whose proof (the finite-level keystone surjectivity `G/G₀ ↠ Gal(𝓀_L/𝓀[K])` + finite
Galois descent of residues) is the block's next rung.

## Honesty

`hresid` is a named hypothesis with a precise classical proof path, NOT claimed irremovable (a
constructive input — no rule-2 obligation); the totally-ramified case (Pass 33) is its
`A₀ = range` specialization, where coverage came from `hsurj`. No new `structure`/`class`; no
owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The monogenicity engine, generalized** (Pass 32's proof, base abstracted): for any subring
`A₀` of `𝒪_L` containing the base image, if residues are covered by `A₀` and some `𝔪_L`-power
falls into `(ι 𝔪[K])·𝒪_L`, then `A₀` and a uniformizer generate `𝒪_L`. -/
theorem closure_subring_union_uniformizer_eq_top [Algebra.IsSeparable K L]
    (A₀ : Subring ↥(extensionIntegers K L))
    (hbase : ∀ c : ↥𝒪[K], extensionAlgebraMap K L c ∈ A₀)
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π})
    (hres : ∀ x : ↥(extensionIntegers K L),
      ∃ a ∈ A₀, x - a ∈ maximalIdeal ↥(extensionIntegers K L))
    (e : ℕ) (he : (maximalIdeal ↥(extensionIntegers K L)) ^ e ≤
      Ideal.map (extensionAlgebraMap K L) (maximalIdeal ↥𝒪[K])) :
    Subring.closure ((A₀ : Set ↥(extensionIntegers K L)) ∪ {π}) = ⊤ := by
  set S := Subring.closure ((A₀ : Set ↥(extensionIntegers K L)) ∪ {π}) with hS
  have hπS : π ∈ S := Subring.subset_closure (Or.inr rfl)
  have hA₀S : ∀ a ∈ A₀, a ∈ S := fun a ha => Subring.subset_closure (Or.inl ha)
  have hιS : ∀ c : ↥𝒪[K], extensionAlgebraMap K L c ∈ S :=
    fun c => hA₀S _ (hbase c)
  have hπm : π ∈ maximalIdeal ↥(extensionIntegers K L) := by
    rw [hspan]; exact Ideal.mem_span_singleton_self π
  let N : Submodule ↥𝒪[K] ↥(extensionIntegers K L) :=
    { carrier := S
      add_mem' := fun ha hb => S.add_mem ha hb
      zero_mem' := S.zero_mem
      smul_mem' := fun c x hx => by
        have h1 : c • x = extensionAlgebraMap K L c * x := by
          rw [Algebra.smul_def]; rfl
        rw [SetLike.mem_coe, h1]
        exact S.mul_mem (hιS c) hx }
  have claim : ∀ n : ℕ, ∀ x : ↥(extensionIntegers K L),
      ∃ s ∈ S, x - s ∈ (maximalIdeal ↥(extensionIntegers K L)) ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      refine ⟨0, S.zero_mem, ?_⟩
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      intro x
      obtain ⟨a, haA, ha⟩ := hres x
      rw [hspan, Ideal.mem_span_singleton] at ha
      obtain ⟨y, hy⟩ := ha
      obtain ⟨s, hsS, hs⟩ := ih y
      refine ⟨a + π * s, S.add_mem (hA₀S a haA) (S.mul_mem hπS hsS), ?_⟩
      have h2 : x - (a + π * s) = (y - s) * π := by
        linear_combination hy
      rw [h2, pow_succ]
      exact Ideal.mul_mem_mul hs hπm
  have hbridge : ∀ z, z ∈ Ideal.map (extensionAlgebraMap K L) (maximalIdeal ↥𝒪[K]) →
      z ∈ (maximalIdeal ↥𝒪[K]) • (⊤ : Submodule ↥𝒪[K] ↥(extensionIntegers K L)) := by
    intro z hz
    have hz' : z ∈ Ideal.span ((extensionAlgebraMap K L : ↥𝒪[K] → ↥(extensionIntegers K L)) ''
        (maximalIdeal ↥𝒪[K])) := hz
    clear hz
    induction hz' using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, hm, rfl⟩ := hw
      have h3 : extensionAlgebraMap K L m = m • (1 : ↥(extensionIntegers K L)) := by
        rw [Algebra.smul_def, mul_one]; rfl
      rw [h3]
      exact Submodule.smul_mem_smul hm Submodule.mem_top
    | zero => exact Submodule.zero_mem _
    | add a b _ _ iha ihb => exact Submodule.add_mem _ iha ihb
    | smul r w _ ihw =>
      rw [smul_eq_mul]
      refine Submodule.smul_induction_on ihw ?_ ?_
      · intro m hm n _
        have h4 : r * (m • n) = m • (r * n) := mul_smul_comm m r n
        rw [h4]
        exact Submodule.smul_mem_smul hm Submodule.mem_top
      · intro a b ha hb
        rw [mul_add]
        exact Submodule.add_mem _ ha hb
  have htop : (⊤ : Submodule ↥𝒪[K] ↥(extensionIntegers K L)) ≤
      N ⊔ (maximalIdeal ↥𝒪[K]) • ⊤ := by
    intro x _
    obtain ⟨s, hsS, hsm⟩ := claim e x
    have h5 : x = s + (x - s) := by ring
    rw [h5]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hsS)
      (Submodule.mem_sup_right (hbridge _ (he hsm)))
  have hNak : (⊤ : Submodule ↥𝒪[K] ↥(extensionIntegers K L)) ≤ N :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp inferInstance)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) htop
  refine (Subring.eq_top_iff' S).mpr (fun x => ?_)
  exact hNak Submodule.mem_top

/-- **The general kernel theorem**: for ANY finite separable extension of nonarchimedean local
fields and any uniformizer of `𝒪_L`, if the inertia-fixed integers cover the residue field
(`hresid` — classically always true: `L/L₀` is totally ramified), then `ker θ₀ = G₁`. The
general case of Serre IV §2 Prop. 7 (level 0) now hangs on exactly this one named lemma. -/
theorem ker_tameCharacter_of_inertiaFixed_cover [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hresid : ∀ x : ↥(extensionIntegers K L),
      ∃ a ∈ inertiaFixedIntegers K L, x - a ∈ maximalIdeal ↥(extensionIntegers K L)) :
    (tameCharacter K π hspan hπ0).ker
      = (ramificationGroup K (extensionIntegers K L) 1).subgroupOf
          (ramificationGroup K (extensionIntegers K L) 0) := by
  obtain ⟨e, he⟩ := exists_pow_maximalIdeal_le_map K L
  exact ker_tameCharacter K π hspan hπ0
    (closure_subring_union_uniformizer_eq_top K L (inertiaFixedIntegers K L)
      (extensionAlgebraMap_mem_inertiaFixedIntegers K L) π hspan hresid e he)
    (fun σ a ha => smul_inertiaFixedIntegers_eq K L σ a ha)

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms closure_subring_union_uniformizer_eq_top
#print axioms ker_tameCharacter_of_inertiaFixed_cover

end Anabelian
