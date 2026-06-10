/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.TameInjectivity
import Anabelian.RamificationExhibit

/-!
# Rung L2: the additive characters `θ_i : G_i →* 𝓀⁺` for `i ≥ 1` (Pass 27)

Pass 24 built the level-0 (multiplicative) tame character `θ₀ : G₀ →* 𝓀ˣ`; Pass 25 made it an
embedding under monogenicity. This file builds the higher levels (Serre, *Local Fields*, IV §2,
Prop. 7 for `i ≥ 1`): for `σ ∈ G_i` write `σπ − π = π^(i+1)·a_σ` (the **additive coefficient**);
then

> `θ_i(σ) := a_σ mod 𝔪` is a homomorphism `G_i →* 𝓀⁺` (`i ≥ 1`) with `G_{i+1} ≤ ker θ_i`,
> hence `G_i/G_{i+1} →* 𝓀⁺` — an **embedding** under the Pass-25 monogenicity hypothesis
> (`ker θ_i = G_{i+1}` via the detection lemma, which already covers all `i`).

The cocycle is `a_{στ} = a_σ + (1 + π^i a_σ)^(i+1)·σ(a_τ)`; it straightens to additivity because
**(i)** `σ ∈ G₀` fixes residues (Pass 24's lemma, via antitonicity) and **(ii)** `1 + π^i a_σ ≡ 1
mod 𝔪` — which *uses `i ≥ 1`*. At `i = 0` the second input fails and the recipe is genuinely not
additive: this file **proves that failure** (`additiveCoeff_residue_not_additive_at_zero`) on the
Pass-26 exhibit (`k = ℚ`, `σ : X ↦ −X`: `a_{σσ} = 0` but `res a_σ + res a_σ = −4 ≠ 0`) — the
extended-rule-2 witness that the `1 ≤ i` hypothesis is load-bearing, discharged in-pass rather
than tracked. (At `i = 0` the *multiplicative* structure takes over: Pass 24.)

## What is proved (all axiom-free)

* `additiveCoeff` (all `i`) — `σπ − π = π^(i+1)·a_σ`, with `additiveCoeff_spec`/`_unique`/`_one`.
* `smul_uniformizer_eq_mul` — `σπ = π(1 + π^i a_σ)`.
* `additiveCharacter (hi : 1 ≤ i) : G_i →* Multiplicative 𝓀` — the homomorphism (the pass's
  heart: the cocycle computation + the two straightening inputs).
* `additiveCharacter_eq_one` — `G_{i+1} ≤ ker θ_i`; `additiveQuotientHom : G_i/G_{i+1} →* 𝓀⁺`.
* `ker_additiveCharacter` / `additiveQuotientHom_injective` / `additiveQuotient_mul_comm` —
  under the Pass-25 monogenicity hypothesis: `ker θ_i = G_{i+1}`, the quotient **embeds in
  `𝓀⁺`**, hence is **abelian**.
* `additiveCoeff_residue_not_additive_at_zero` — **the `i = 0` failure witness** (rule-2).

## Honesty

The monogenicity hypothesis is used exactly as in Pass 25 (named binders, not claimed
irremovable — no new obligation). The `1 ≤ i` hypothesis on `additiveCharacter` IS claimed
load-bearing, and the claim is **discharged in this pass** by the constructed `i = 0`
counterexample above (no owed witness left open). NOT attempted: the **uniformizer-twist law**
`res(w)^i·res(a'_σ) = res(a_σ)` — drafted and mathematically routine, but its statement hits a
reproducible `whnf` divergence elaborating `additiveCoeff` at the composite uniformizer
`π * ↑w` (not fixed by heartbeats up to 800k, coercion ascription, or `subst`-elimination;
root cause unisolated — logged in NOTES); its better, twist-free formulation targets
`𝔪^i/𝔪^(i+1)` and is the named future form. Also not attempted: wild `G₁` pro-`p` (needs
`char 𝓀 = p` inputs); the local-field instantiation. No new `structure`/`class`; D1 N/A;
D2 N/A (`ValuationSubring`-native; the witness lives in the Pass-26 concrete file's types).
Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open scoped Pointwise

namespace Anabelian

open ValuationSubring IsLocalRing

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}
  {A₀ : Subring ↥A}

/-! ### The additive coefficient `a_σ`, defined for every level -/

theorem exists_smul_uniformizer_sub_eq (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    {i : ℕ} {σ : A.decompositionSubgroup K} (hσ : σ ∈ ramificationGroup K A i) :
    ∃ a : ↥A, σ • π - π = π ^ (i + 1) * a := by
  have h := (mem_ramificationGroup_iff K A σ).mp hσ π
  rw [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc⟩

/-- The **additive coefficient** of `σ ∈ G_i`: the unique `a_σ` with `σπ − π = π^(i+1)·a_σ`. -/
noncomputable def additiveCoeff (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) {i : ℕ}
    (σ : ↥(ramificationGroup K A i)) : ↥A :=
  (exists_smul_uniformizer_sub_eq K π hspan σ.2).choose

theorem additiveCoeff_spec (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) {i : ℕ}
    (σ : ↥(ramificationGroup K A i)) :
    σ.1 • π - π = π ^ (i + 1) * additiveCoeff K π hspan σ :=
  (exists_smul_uniformizer_sub_eq K π hspan σ.2).choose_spec

theorem additiveCoeff_unique (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) {i : ℕ} {σ : ↥(ramificationGroup K A i)} {a : ↥A}
    (ha : σ.1 • π - π = π ^ (i + 1) * a) :
    additiveCoeff K π hspan σ = a := by
  have h2 : π ^ (i + 1) * additiveCoeff K π hspan σ = π ^ (i + 1) * a := by
    rw [← additiveCoeff_spec K π hspan σ, ha]
  exact mul_left_cancel₀ (pow_ne_zero _ hπ0) h2

theorem additiveCoeff_one (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) {i : ℕ} :
    additiveCoeff K π hspan (1 : ↥(ramificationGroup K A i)) = 0 :=
  additiveCoeff_unique K π hspan hπ0 (by
    rw [show ((1 : ↥(ramificationGroup K A i)) : A.decompositionSubgroup K) = 1 from rfl,
      one_smul, sub_self, mul_zero])

/-- `σπ = π·(1 + π^i·a_σ)`. -/
theorem smul_uniformizer_eq_mul (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) {i : ℕ}
    (σ : ↥(ramificationGroup K A i)) :
    σ.1 • π = π * (1 + π ^ i * additiveCoeff K π hspan σ) := by
  linear_combination additiveCoeff_spec K π hspan σ

/-- For `i ≥ 1`, `1 + π^i·a ≡ 1 mod 𝔪` — the straightening input that *needs* `i ≥ 1`. -/
theorem residue_one_add_pow_mul (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    {i : ℕ} (hi : 1 ≤ i) (a : ↥A) :
    residue ↥A (1 + π ^ i * a) = 1 := by
  have hπm : π ∈ maximalIdeal ↥A := by
    rw [hspan]; exact Ideal.mem_span_singleton_self π
  have hmem : π ^ i * a ∈ maximalIdeal ↥A := by
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hi).symm⟩
    have h : π ^ (j + 1) * a = π * (π ^ j * a) := by ring
    rw [h]
    exact Ideal.mul_mem_right _ _ hπm
  have h0 : residue ↥A (π ^ i * a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_add, map_one, h0, add_zero]

/-! ### The additive character `θ_i`, `i ≥ 1` -/

/-- **The additive character** `θ_i : G_i →* 𝓀⁺` (Serre IV §2, `i ≥ 1`): `σ ↦ a_σ mod 𝔪`.
The cocycle `a_{στ} = a_σ + (1 + π^i a_σ)^(i+1)·σ(a_τ)` straightens because inertia fixes
residues (Pass 24) and `1 + π^i a_σ ≡ 1 mod 𝔪` (this is where `1 ≤ i` bites — the `i = 0`
failure is *proved* below). -/
noncomputable def additiveCharacter (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    ↥(ramificationGroup K A i) →* Multiplicative (ResidueField ↥A) where
  toFun σ := Multiplicative.ofAdd (residue ↥A (additiveCoeff K π hspan σ))
  map_one' := by
    rw [additiveCoeff_one K π hspan hπ0, map_zero, ofAdd_zero]
  map_mul' σ τ := by
    have hkey : (σ * τ).1 • π - π = π ^ (i + 1) *
        (additiveCoeff K π hspan σ +
          (1 + π ^ i * additiveCoeff K π hspan σ) ^ (i + 1) *
            (σ.1 • additiveCoeff K π hspan τ)) := by
      have hτ := additiveCoeff_spec K π hspan τ
      have hσ := additiveCoeff_spec K π hspan σ
      have hu := smul_uniformizer_eq_mul K π hspan σ
      have h1 : σ.1 • (τ.1 • π - π) =
          (σ.1 • π) ^ (i + 1) * (σ.1 • additiveCoeff K π hspan τ) := by
        rw [hτ, smul_mul', smul_pow']
      have h2 : (σ * τ).1 • π - π = σ.1 • (τ.1 • π - π) + (σ.1 • π - π) := by
        rw [show ((σ * τ).1 : A.decompositionSubgroup K) = σ.1 * τ.1 from rfl, mul_smul,
          smul_sub]
        ring
      rw [h2, h1, hσ, hu, mul_pow]
      ring
    have hco := additiveCoeff_unique K π hspan hπ0 hkey
    have hres1 : residue ↥A ((1 + π ^ i * additiveCoeff K π hspan σ) ^ (i + 1)) = 1 := by
      rw [map_pow, residue_one_add_pow_mul π hspan hi, one_pow]
    have hres2 : residue ↥A (σ.1 • additiveCoeff K π hspan τ)
        = residue ↥A (additiveCoeff K π hspan τ) :=
      residue_smul_eq_of_mem_ramificationGroup_zero K
        (ramificationGroup_antitone K A (Nat.zero_le i) σ.2) _
    change Multiplicative.ofAdd (residue ↥A (additiveCoeff K π hspan (σ * τ))) = _
    rw [hco, map_add, map_mul, hres1, hres2, one_mul, ofAdd_add]

/-- **`G_{i+1}` lies in the kernel of `θ_i`**. -/
theorem additiveCharacter_eq_one (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) {i : ℕ} (hi : 1 ≤ i) (σ : ↥(ramificationGroup K A i))
    (hσ : σ.1 ∈ ramificationGroup K A (i + 1)) :
    additiveCharacter K π hspan hπ0 hi σ = 1 := by
  have h := (mem_ramificationGroup_iff K A σ.1).mp hσ π
  rw [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hcoeff : additiveCoeff K π hspan σ = π * c :=
    additiveCoeff_unique K π hspan hπ0 (by rw [hc]; ring)
  change Multiplicative.ofAdd (residue ↥A (additiveCoeff K π hspan σ)) = 1
  rw [hcoeff]
  exact ofAdd_eq_one.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (by
    rw [hspan]
    exact Ideal.mem_span_singleton.mpr ⟨c, rfl⟩))

/-- The induced map on the quotient, `G_i/G_{i+1} →* 𝓀⁺`. -/
noncomputable def additiveQuotientHom (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) {i : ℕ} (hi : 1 ≤ i) :
    (↥(ramificationGroup K A i) ⧸
      ((ramificationGroup K A (i + 1)).subgroupOf (ramificationGroup K A i))) →*
      Multiplicative (ResidueField ↥A) :=
  QuotientGroup.lift _ (additiveCharacter K π hspan hπ0 hi) fun σ hσ =>
    additiveCharacter_eq_one K π hspan hπ0 hi σ (Subgroup.mem_subgroupOf.mp hσ)

/-- **`ker θ_i = G_{i+1}`** under the Pass-25 monogenicity hypothesis (the detection lemma
covers all `i`, as promised). -/
theorem ker_additiveCharacter (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    {i : ℕ} (hi : 1 ≤ i)
    (hfix : ∀ σ : ↥(ramificationGroup K A i), ∀ a ∈ A₀, σ.1 • a = a) :
    (additiveCharacter K π hspan hπ0 hi).ker
      = (ramificationGroup K A (i + 1)).subgroupOf (ramificationGroup K A i) := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hσ
    have h0 : residue ↥A (additiveCoeff K π hspan σ) = 0 := ofAdd_eq_one.mp hσ
    have hm : additiveCoeff K π hspan σ ∈ maximalIdeal ↥A :=
      Ideal.Quotient.eq_zero_iff_mem.mp h0
    rw [hspan, Ideal.mem_span_singleton] at hm
    obtain ⟨b, hb⟩ := hm
    have hππ : σ.1 • π - π ∈ maximalIdeal ↥A ^ (i + 1 + 1) := by
      rw [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      refine ⟨b, ?_⟩
      rw [additiveCoeff_spec K π hspan σ, hb]
      ring
    exact mem_ramificationGroup_of_smul_uniformizer_sub_mem K hgen (hfix σ) hππ
  · exact additiveCharacter_eq_one K π hspan hπ0 hi σ

/-- **The additive embedding**: under monogenicity, `G_i/G_{i+1} ↪ 𝓀⁺` (`i ≥ 1`). -/
theorem additiveQuotientHom_injective (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    {i : ℕ} (hi : 1 ≤ i)
    (hfix : ∀ σ : ↥(ramificationGroup K A i), ∀ a ∈ A₀, σ.1 • a = a) :
    Function.Injective (additiveQuotientHom K π hspan hπ0 hi) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have h : (additiveQuotientHom K π hspan hπ0 hi).ker
      = Subgroup.map (QuotientGroup.mk' _) (additiveCharacter K π hspan hπ0 hi).ker :=
    QuotientGroup.ker_lift _ _ _
  rw [h, ker_additiveCharacter K π hspan hπ0 hgen hi hfix, QuotientGroup.map_mk'_self]

/-- Corollary: under monogenicity, the higher quotients `G_i/G_{i+1}` are **commutative**. -/
theorem additiveQuotient_mul_comm (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    {i : ℕ} (hi : 1 ≤ i)
    (hfix : ∀ σ : ↥(ramificationGroup K A i), ∀ a ∈ A₀, σ.1 • a = a)
    (x y : ↥(ramificationGroup K A i) ⧸
      ((ramificationGroup K A (i + 1)).subgroupOf (ramificationGroup K A i))) :
    x * y = y * x := by
  have hinj := additiveQuotientHom_injective K π hspan hπ0 hgen hi hfix
  apply hinj
  rw [map_mul, map_mul, mul_comm]

/-! ### The `i = 0` failure witness (extended rule-2, discharged in-pass) -/

/-- **The `1 ≤ i` hypothesis of `additiveCharacter` is load-bearing — constructed witness.**
At `i = 0` the additive recipe `σ ↦ res(a_σ)` is NOT a homomorphism: on the Pass-26 exhibit
(`ℚ⸨X⸩`, `σ : X ↦ −X`) we have `σ² = 1` so `a_{σ·σ} = 0`, while `res(a_σ) + res(a_σ) = −4 ≠ 0`.
(At level 0 the multiplicative tame character is the correct structure — Pass 24.) -/
theorem additiveCoeff_residue_not_additive_at_zero :
    ¬ ∀ σ τ : ↥(ramificationGroup ℚ (laurentIntegers ℚ) 0),
      residue ↥(laurentIntegers ℚ) (additiveCoeff ℚ (laurentUniformizer ℚ)
          (maximalIdeal_laurentIntegers_eq_span ℚ) (σ * τ))
        = residue ↥(laurentIntegers ℚ) (additiveCoeff ℚ (laurentUniformizer ℚ)
            (maximalIdeal_laurentIntegers_eq_span ℚ) σ)
          + residue ↥(laurentIntegers ℚ) (additiveCoeff ℚ (laurentUniformizer ℚ)
              (maximalIdeal_laurentIntegers_eq_span ℚ) τ) := by
  intro hall
  set hspanQ := maximalIdeal_laurentIntegers_eq_span ℚ
  have hπ0Q := laurentUniformizer_ne_zero ℚ
  set σ0 : ↥(ramificationGroup ℚ (laurentIntegers ℚ) 0) :=
    ⟨laurentNegXDecomp ℚ, laurentNegXDecomp_mem_ramificationGroup_zero ℚ⟩ with hσ0
  -- σ₀² = 1
  have hinvol : σ0 * σ0 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change laurentNegXAlgEquiv ℚ * laurentNegXAlgEquiv ℚ = 1
    nth_rewrite 2 [← inv_laurentNegXAlgEquiv ℚ]
    exact mul_inv_cancel _
  -- a_{σ₀} = −2
  have hσπ : σ0.1 • laurentUniformizer ℚ - laurentUniformizer ℚ
      = laurentUniformizer ℚ ^ (0 + 1) * (-2) := by
    have h1 : σ0.1 • laurentUniformizer ℚ
        = laurentUniformizer ℚ * ↑(-1 : (↥(laurentIntegers ℚ))ˣ) :=
      laurentNegXDecomp_smul_uniformizer ℚ
    have h2 : ((↑(-1 : (↥(laurentIntegers ℚ))ˣ)) : ↥(laurentIntegers ℚ)) = -1 := by
      rw [Units.val_neg, Units.val_one]
    rw [h1, h2, pow_one]
    ring
  have ha : additiveCoeff ℚ (laurentUniformizer ℚ) hspanQ σ0 = -2 :=
    additiveCoeff_unique ℚ _ hspanQ hπ0Q hσπ
  -- a_{σ₀·σ₀} = 0
  have h1 : additiveCoeff ℚ (laurentUniformizer ℚ) hspanQ (σ0 * σ0) = 0 := by
    rw [hinvol]
    exact additiveCoeff_one ℚ _ hspanQ hπ0Q
  -- the would-be additivity at σ₀, σ₀ gives 0 = res(−4)
  have h2 := hall σ0 σ0
  rw [h1, ha, map_zero, ← map_add] at h2
  -- h2 : 0 = residue (−2 + −2); normalize the argument to −4
  have h3 : ((-2 : ↥(laurentIntegers ℚ)) + -2) = -4 := by norm_num
  rw [h3] at h2
  -- so −4 ∈ 𝔪, i.e. 4 ∈ 𝔪 — but 4 is a unit of A (nonzero constant coefficient)
  have hm : (-4 : ↥(laurentIntegers ℚ)) ∈ maximalIdeal ↥(laurentIntegers ℚ) :=
    Ideal.Quotient.eq_zero_iff_mem.mp h2.symm
  have hm4 : (4 : ↥(laurentIntegers ℚ)) ∈ maximalIdeal ↥(laurentIntegers ℚ) := by
    have h5 := neg_mem hm
    norm_num at h5
    exact h5
  have hunit : IsUnit (4 : ↥(laurentIntegers ℚ)) := by
    refine isUnit_of_constantCoeff_ne_zero ℚ (g := (4 : PowerSeries ℚ)) ?_ ?_
    · change ((4 : ↥(laurentIntegers ℚ)) : LaurentSeries ℚ)
        = ((4 : PowerSeries ℚ) : LaurentSeries ℚ)
      have hl : ((4 : ↥(laurentIntegers ℚ)) : LaurentSeries ℚ) = (4 : LaurentSeries ℚ) := by
        norm_cast
      have hr : ((4 : PowerSeries ℚ) : LaurentSeries ℚ) = (4 : LaurentSeries ℚ) :=
        map_ofNat _ 4
      rw [hl, hr]
    · rw [map_ofNat]
      norm_num
  exact (IsLocalRing.mem_maximalIdeal _).mp hm4 hunit

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms additiveCoeff
#print axioms additiveCharacter
#print axioms additiveCharacter_eq_one
#print axioms additiveQuotientHom
#print axioms ker_additiveCharacter
#print axioms additiveQuotientHom_injective
#print axioms additiveQuotient_mul_comm
#print axioms additiveCoeff_residue_not_additive_at_zero

end Anabelian
