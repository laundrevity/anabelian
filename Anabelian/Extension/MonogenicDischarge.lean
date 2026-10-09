/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Extension.MonogenicGeneral
import Anabelian.Extension.RamificationData
import Anabelian.Extension.Uniformizer
import Anabelian.Extension.ResidueFinite
import Anabelian.Ramification.LowerIndexGenerator
import Mathlib

/-!
# The monogenicity discharge: `𝒪_L = 𝒪_K[x]` (Serre III §6 Prop. 12, finite-residue case)
# (Pass 54)

Pass 53's concrete `i_G` carried one named hypothesis: `hgen` — a single ring generator of
`𝒪_L` over `𝒪_K`. **This pass discharges it**: for every finite separable `L/K` over a
nonarchimedean local field,

> `∃ x, Subring.closure (range (𝒪_K → 𝒪_L) ∪ {x}) = ⊤` — **`𝒪_L` is monogenic over `𝒪_K`**.

Serre's Prop. 12 (III §6) requires a separable residue extension; here the residue fields are
**finite** (Pass 36), which permits a route with no minimal-polynomial or Taylor machinery:

1. Take `x₀` lifting a **cyclic generator** `g` of `𝓀_L^×` (finite ⟹ cyclic). Every residue
   is `0` or a power of `g`, so `𝒪_K[x₀]` covers the residue field.
2. The polynomial `f = X^n − 1` with `n = |𝓀_L^×|` kills `g` (`g^n = 1`, Lagrange), and its
   "derivative coefficient" `n` is a **unit** of `𝒪_L`: `(n : 𝓀_L) = |𝓀_L| − 1 = −1 ≠ 0`
   (the cardinality vanishes in its own characteristic). So `y₀ := x₀^n − 1 ∈ 𝔪`.
3. If `y₀ ∉ 𝔪²`, it is a **uniformizer lying in `𝒪_K[x₀]`**. If `y₀ ∈ 𝔪²`, correct
   `x := x₀(1 + π₀)`: the binomial tail `(1+π₀)^n = 1 + nπ₀ + π₀²a` gives
   `x^n − 1 = y₀ + (x₀^n·n)·π₀ + (x₀^n·a)·π₀²` with `x₀^n·n` a unit — so `x^n − 1 ∈ 𝔪 ∖ 𝔪²`
   (Serre's `x + π` correction, in multiplicative form, with `f' ` replaced by the explicit
   unit `n·x₀^n`).
4. Pass 32's generation engine (`closure_subring_union_uniformizer_eq_top`, with the `he`
   input unconditional by Pass 33) then gives `Subring.closure (𝒪_K[x] ∪ {x^n − 1}) = ⊤`; the
   uniformizer already lies in the subring, so `𝒪_K[x] = ⊤`.

## What is proved (all axiom-free)

* `exists_pow_one_add_eq` — the binomial tail `(1+t)^m = 1 + mt + t²a` (any commutative ring).
* `maximalIdeal_eq_span_of_mem_of_notMem_sq` — DVR brick: an element of `𝔪 ∖ 𝔪²` spans `𝔪`
  (via Pass 53's `addVal` bridge).
* `closure_union_singleton_eq_top` — the assembly: a lift of a residue generator plus a
  uniformizer *inside* `𝒪_K[x]` generate `𝒪_L`.
* **`exists_generator_extensionIntegers`** — the headline: **`𝒪_L` is monogenic over `𝒪_K`**;
  Pass 53's `hgen` is a theorem.
* **`exists_generator_lowerIndex_eq_addVal`** — the payoff: **unconditionally**, there is an
  `x` with `i_G(σ) = v_L(σx − x)` for every `σ` — the concrete `i_G` at `𝒪_L` with no
  remaining hypotheses.

## Honesty

Structure of the Galois action of given fields — **no reach toward R1–R3**. This discharges
the `hgen` of Pass 53's `i_G` theory (and of any future Prop.-3 work). It does **not**
discharge the `(hgen, hfix)` package of the Pass-25/27/28 *character* theorems: those need an
*inertia-fixed* generating subring (`σ • a = a` for `σ ∈ G_0`), which `𝒪_K[x]` is not — that
route was closed separately by Passes 32–34 via `inertiaFixedIntegers`. No new
`structure`/`class`; no owed witness (nothing here claims a hypothesis load-bearing); D1 N/A;
D2 stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

/-- The binomial tail, explicit: `(1+t)^m = 1 + mt + t²·a` for some `a` — the two-term
truncation that replaces the Taylor expansion in Serre's correction argument. -/
theorem exists_pow_one_add_eq {R : Type*} [CommRing R] (t : R) :
    ∀ m : ℕ, ∃ a : R, (1 + t) ^ m = 1 + (m : R) * t + t ^ 2 * a := by
  intro m
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨a * t + a + (k : R), ?_⟩
    rw [pow_succ, ha]
    push_cast
    ring

/-- **An element of `𝔪 ∖ 𝔪²` spans `𝔪`** in a DVR: its `addVal` is exactly `1` (Pass 53's
bridge), so it is a unit multiple of any irreducible, hence irreducible, hence a uniformizer. -/
theorem maximalIdeal_eq_span_of_mem_of_notMem_sq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (h1 : π ∈ maximalIdeal R)
    (h2 : π ∉ maximalIdeal R ^ 2) : maximalIdeal R = Ideal.span {π} := by
  have hv1 : ((1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal R π :=
    mem_maximalIdeal_pow_iff_le_addVal.mp (by simpa using h1)
  have hv2 : ¬ ((2 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal R π :=
    fun hle => h2 (mem_maximalIdeal_pow_iff_le_addVal.mpr hle)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [IsDiscreteValuationRing.addVal_zero] at hv2
    exact hv2 le_top
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hϖ
  have hval : IsDiscreteValuationRing.addVal R π = n := by
    rw [hu]
    exact IsDiscreteValuationRing.addVal_def' u hϖ n
  rw [hval] at hv1 hv2
  have hn1 : n = 1 := by
    have ha : 1 ≤ n := by exact_mod_cast hv1
    have hb : ¬ 2 ≤ n := fun hc => hv2 (by exact_mod_cast hc)
    omega
  subst hn1
  have hirr : Irreducible π := by
    rw [hu, pow_one]
    exact Associated.irreducible ⟨u, mul_comm ϖ ↑u⟩ hϖ
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hirr

section Main

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The assembly**: if `x` lifts a multiplicative generator of the residue field (every
residue is `0` or a power of `residue x`) and `𝒪_K[x]` contains an element of `𝔪 ∖ 𝔪²`, then
`𝒪_K[x] = 𝒪_L`. Pass 32's generation engine, applied to `A₀ = 𝒪_K[x]` with the uniformizer
already inside the subring. -/
theorem closure_union_singleton_eq_top [Algebra.IsSeparable K L]
    (x : ↥(extensionIntegers K L))
    (hcov : ∀ y : ResidueField ↥(extensionIntegers K L),
      y = 0 ∨ ∃ k : ℕ, y = (residue ↥(extensionIntegers K L) x) ^ k)
    (π : ↥(extensionIntegers K L))
    (hπA : π ∈ Subring.closure
      (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}))
    (h1 : π ∈ maximalIdeal ↥(extensionIntegers K L))
    (h2 : π ∉ maximalIdeal ↥(extensionIntegers K L) ^ 2) :
    Subring.closure
      (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}) = ⊤ := by
  set A₀ := Subring.closure
    (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}) with hA₀
  have hbase : ∀ c : ↥𝒪[K], extensionAlgebraMap K L c ∈ A₀ :=
    fun c => Subring.subset_closure (Or.inl ⟨c, rfl⟩)
  have hxA : x ∈ A₀ := Subring.subset_closure (Or.inr rfl)
  have hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π} :=
    maximalIdeal_eq_span_of_mem_of_notMem_sq h1 h2
  have hres : ∀ z : ↥(extensionIntegers K L),
      ∃ a ∈ A₀, z - a ∈ maximalIdeal ↥(extensionIntegers K L) := by
    intro z
    rcases hcov (residue ↥(extensionIntegers K L) z) with h0 | ⟨k, hk⟩
    · refine ⟨0, A₀.zero_mem, ?_⟩
      rw [sub_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp h0
    · refine ⟨x ^ k, pow_mem hxA k, ?_⟩
      have hk2 : residue ↥(extensionIntegers K L) z
          = residue ↥(extensionIntegers K L) (x ^ k) := by
        rw [hk, map_pow]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem z (x ^ k)).mp hk2
  obtain ⟨e, he⟩ := exists_pow_maximalIdeal_le_map K L
  have htop := closure_subring_union_uniformizer_eq_top K L A₀ hbase π hspan hres e he
  have hcollapse : ((A₀ : Set ↥(extensionIntegers K L)) ∪ {π}) = A₀ :=
    Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hπA)
  rw [hcollapse, Subring.closure_eq] at htop
  exact htop

/-- **`𝒪_L` is monogenic over `𝒪_K`** (Serre, *Local Fields*, III §6 Prop. 12, finite-residue
case): for every finite separable `L/K` over a nonarchimedean local field there is a single
`x` with `Subring.closure (range (𝒪_K → 𝒪_L) ∪ {x}) = ⊤`. This **discharges the `hgen`
hypothesis** of Pass 53's concrete-`i_G` theory. Lift a cyclic generator of `𝓀_L^×`; the
element `x^n − 1` (`n = |𝓀_L^×|`) is a uniformizer in `𝒪_K[x]` after at most one correction
`x ↦ x(1 + π₀)`, the correction controlled by the unit `n·xⁿ` (`(n : 𝓀_L) = −1`). -/
theorem exists_generator_extensionIntegers [Algebra.IsSeparable K L] :
    ∃ x : ↥(extensionIntegers K L),
      Subring.closure
        (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {x}) = ⊤ := by
  classical
  set R := ↥(extensionIntegers K L) with hR
  have hfin : Finite (ResidueField R) := finite_residueField_extensionIntegers K L
  have := Fintype.ofFinite (ResidueField R)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ResidueField R)ˣ)
  obtain ⟨x₀, hx₀⟩ := Ideal.Quotient.mk_surjective ((g : ResidueField R))
  have hx₀res : residue R x₀ = (g : ResidueField R) := hx₀
  set n := Nat.card (ResidueField R)ˣ with hn
  have hgn : g ^ n = 1 := pow_card_eq_one'
  have hcardn : ((n : ℕ) : ResidueField R) = -1 := by
    have h1 : n = Nat.card (ResidueField R) - 1 := Nat.card_units (ResidueField R)
    have h2 : 1 ≤ Nat.card (ResidueField R) := Nat.card_pos
    have h3 : ((Nat.card (ResidueField R) : ℕ) : ResidueField R) = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero (ResidueField R)
    rw [h1, Nat.cast_sub h2, h3, Nat.cast_one, zero_sub]
  have hcov_g : ∀ y : ResidueField R, y = 0 ∨ ∃ k : ℕ, y = (g : ResidueField R) ^ k := by
    intro y
    by_cases hy : y = 0
    · exact Or.inl hy
    · right
      have hyu : IsUnit y := isUnit_iff_ne_zero.mpr hy
      have hmem : hyu.unit ∈ Subgroup.zpowers g := hg hyu.unit
      obtain ⟨k, hk⟩ :=
        (isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers.mpr hmem
      refine ⟨k, ?_⟩
      have h5 := congrArg (Units.val) hk
      simpa using h5.symm
  have hx₀u : IsUnit x₀ := by
    by_contra hnu
    have hmem : x₀ ∈ maximalIdeal R := (mem_maximalIdeal x₀).mpr hnu
    have h6 : residue R x₀ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hx₀res] at h6
    exact Units.ne_zero g h6
  have hy₀mem : x₀ ^ n - 1 ∈ maximalIdeal R := by
    have hres0 : residue R (x₀ ^ n - 1) = 0 := by
      rw [map_sub, map_pow, hx₀res, map_one, ← Units.val_pow_eq_pow_val, hgn,
          Units.val_one, sub_self]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hres0
  obtain ⟨π₀, hspan₀, hπ₀0⟩ := exists_uniformizer_extensionIntegers K L
  have hπ₀m : π₀ ∈ maximalIdeal R := by
    rw [hspan₀]; exact Ideal.mem_span_singleton_self π₀
  have hπ₀irr : Irreducible π₀ :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π₀).mpr hspan₀
  have hπ₀sq : π₀ ∉ maximalIdeal R ^ 2 := by
    intro hmem
    have h7 := mem_maximalIdeal_pow_iff_le_addVal.mp hmem
    rw [IsDiscreteValuationRing.addVal_uniformizer hπ₀irr] at h7
    have h8 : (2 : ℕ) ≤ 1 := by exact_mod_cast h7
    omega
  by_cases hcase : x₀ ^ n - 1 ∈ maximalIdeal R ^ 2
  · -- deep case: correct to x := x₀(1 + π₀); the binomial tail shifts the depth to exactly 1
    set x := x₀ * (1 + π₀) with hx
    have hxres : residue R x = (g : ResidueField R) := by
      have hπ₀res : residue R π₀ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hπ₀m
      rw [hx, map_mul, map_add, map_one, hπ₀res, add_zero, mul_one, hx₀res]
    obtain ⟨a, ha⟩ := exists_pow_one_add_eq π₀ n
    have hkey : x ^ n - 1
        = (x₀ ^ n - 1) + x₀ ^ n * (n : R) * π₀ + x₀ ^ n * a * π₀ ^ 2 := by
      rw [hx, mul_pow, ha]
      ring
    have hunit : IsUnit (x₀ ^ n * ((n : ℕ) : R)) := by
      refine (hx₀u.pow n).mul ?_
      by_contra hnu
      have hmem : ((n : ℕ) : R) ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hnu
      have h9 : residue R ((n : ℕ) : R) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_natCast, hcardn] at h9
      exact (neg_ne_zero.mpr one_ne_zero) h9
    have hymem : x ^ n - 1 ∈ maximalIdeal R := by
      rw [hkey]
      refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · exact (Ideal.pow_le_self two_ne_zero) hcase
      · exact Ideal.mul_mem_left _ _ hπ₀m
      · exact Ideal.mul_mem_left _ _ ((Ideal.pow_le_self two_ne_zero)
          (Ideal.pow_mem_pow hπ₀m 2))
    have hysq : x ^ n - 1 ∉ maximalIdeal R ^ 2 := by
      intro hy2
      have hterm : x₀ ^ n * (n : R) * π₀ ∈ maximalIdeal R ^ 2 := by
        have h10 : x₀ ^ n * (n : R) * π₀
            = (x ^ n - 1) - (x₀ ^ n - 1) - x₀ ^ n * a * π₀ ^ 2 := by
          rw [hkey]; ring
        rw [h10]
        refine Ideal.sub_mem _ (Ideal.sub_mem _ hy2 hcase) ?_
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hπ₀m 2)
      obtain ⟨v, hv⟩ := hunit
      have hπ₀2 : π₀ ∈ maximalIdeal R ^ 2 := by
        have h11 : π₀ = ↑v⁻¹ * (x₀ ^ n * (n : R) * π₀) := by
          rw [← mul_assoc, ← mul_assoc]
          rw [show (↑v⁻¹ * x₀ ^ n * (n : R) : R) = ↑v⁻¹ * (x₀ ^ n * (n : R)) by ring,
              ← hv, Units.inv_mul, one_mul]
        rw [h11]
        exact Ideal.mul_mem_left _ _ hterm
      exact hπ₀sq hπ₀2
    have hxA : x ∈ Subring.closure
        (((extensionAlgebraMap K L).range : Set R) ∪ {x}) :=
      Subring.subset_closure (Or.inr rfl)
    exact ⟨x, closure_union_singleton_eq_top K L x (by rw [hxres]; exact hcov_g)
      (x ^ n - 1) (Subring.sub_mem _ (pow_mem hxA n) (Subring.one_mem _)) hymem hysq⟩
  · -- shallow case: x₀ works as is
    have hxA : x₀ ∈ Subring.closure
        (((extensionAlgebraMap K L).range : Set R) ∪ {x₀}) :=
      Subring.subset_closure (Or.inr rfl)
    exact ⟨x₀, closure_union_singleton_eq_top K L x₀ (by rw [hx₀res]; exact hcov_g)
      (x₀ ^ n - 1) (Subring.sub_mem _ (pow_mem hxA n) (Subring.one_mem _)) hy₀mem hcase⟩

/-- **The unconditional concrete `i_G`** (the payoff): for every finite separable `L/K` over a
nonarchimedean local field there is a generator `x` of `𝒪_L/𝒪_K` with
`i_G(σ) = v_L(σx − x)` for **every** `σ` — Pass 53's `lowerIndex_extensionIntegers_eq_addVal`
with its last named hypothesis discharged. -/
theorem exists_generator_lowerIndex_eq_addVal [Algebra.IsSeparable K L] :
    ∃ x : ↥(extensionIntegers K L),
      ∀ σ : (extensionIntegers K L).decompositionSubgroup K,
        lowerIndex K (extensionIntegers K L) σ
          = IsDiscreteValuationRing.addVal ↥(extensionIntegers K L) (σ • x - x) := by
  obtain ⟨x, hx⟩ := exists_generator_extensionIntegers K L
  exact ⟨x, fun σ => lowerIndex_extensionIntegers_eq_addVal K L hx σ⟩

end Main

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms exists_pow_one_add_eq
#print axioms maximalIdeal_eq_span_of_mem_of_notMem_sq
#print axioms closure_union_singleton_eq_top
#print axioms exists_generator_extensionIntegers
#print axioms exists_generator_lowerIndex_eq_addVal

end Anabelian
