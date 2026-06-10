/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.TameCharacter
import Mathlib.RingTheory.LaurentSeries

/-!
# Rung L2: the come-apart exhibit — `G₀ ≠ G₁` for an explicit valued field (Pass 26)

The ramification filtration owes its definition a *constructed witness* that the groups genuinely
come apart: Pass 22 proved the absolute-level filtration **collapses** (`G_i = G_0` at idempotent
`𝔪[K̄]`), and Pass 23 built the finite-level theory abstractly; this file exhibits the separating
regime **concretely**. In the Laurent-series field `L = k⸨X⸩` (`char k ≠ 2`, i.e. `(2 : k) ≠ 0`)
with its `X`-adic valuation subring `A ≅ k⟦X⟧` and the `k`-algebra involution

> `σ : f(X) ↦ f(−X)`,

we prove: `σ` stabilizes `A` (so lives in the decomposition subgroup), `σ ∈ G₀` (constant
coefficients are untouched, so residues are fixed), and `σ ∉ G₁` — hence

> **`ramificationGroup k A 0 ≠ ramificationGroup k A 1`.**

The exclusion `σ ∉ G₁` is detected by **Pass 24's tame character**: `σ(X) = −X` gives
`tameUnit σ = −1`, so `θ₀(σ) = −1 ≠ 1` in `𝓀ˣ` (this is where `(2 : k) ≠ 0` bites), while
Pass 24's `tameCharacter_eq_one` says `G₁ ≤ ker θ₀`. The exhibit thus *exercises* the
Pass-24/25 structure: the tame character is exactly the invariant that sees the jump. A fully
closed witness (no hypotheses, no variables) is provided at `k = ℚ`.

This is the classical tame quadratic picture (`k⸨X⸩/k⸨X²⸩`, `e = 2`, `p ∤ e`): we take `K = k`
(the constants) rather than constructing the subfield `k⸨X²⸩`, which only *enlarges* the ambient
group `L ≃ₐ[K] L` — the membership facts `σ ∈ G₀ \ G₁` are identical, and the filtration is
defined per `(K, A)` for any base. The classical quadratic statement is the restriction of this
exhibit to `⟨σ⟩`.

## What is proved (all axiom-free)

* `laurentNegXAlgEquiv` — the involution `f(X) ↦ f(−X)` of `k⸨X⸩` as a `k`-algebra equivalence,
  lifted from `PowerSeries.evalNegHom` along the localization `k⸨X⸩ = k⟦X⟧[X⁻¹]`.
* `laurentIntegers k` — `A = {v ≤ 1} : ValuationSubring k⸨X⸩` (Mathlib's `X`-adic `Valued`
  instance), membership = "is a power series" (`val_le_one_iff_eq_coe`).
* `laurentNegX_mem_decompositionSubgroup` — `σ` stabilizes `A`.
* `maximalIdeal_laurentIntegers_eq_span` — **`𝔪_A = (π)`**, `π = X` (with
  `laurentUniformizer_ne_zero`): the uniformizer package the tame character consumes.
* `laurentNegXDecomp_mem_ramificationGroup_zero` — **`σ ∈ G₀`**.
* `laurentNegXDecomp_notMem_ramificationGroup_one` — **`σ ∉ G₁`** (`(2 : k) ≠ 0`), via
  `tameUnit_unique` + `tameCharacter_eq_one`.
* `laurentRamificationGroup_zero_ne_one` — **`G₀ ≠ G₁`** for `(k, k⸨X⸩, A)`.
* `ramificationGroup_zero_ne_one_rat` — the **fully closed witness** at `k = ℚ`.

## Honesty

This pass *discharges* a long-logged obligation (the "come-apart exhibit the definition
deserves", `ROADMAP.md` since Pass 23) rather than incurring any: the witness is constructed, not
asserted. No claim is made about the rest of the filtration of the (large) ambient decomposition
group — e.g. `G₁ ≠ ⊥` here (wild automorphisms like `X ↦ X + X²` live in it); the classical
`G₀ ⊃ G₁ = ⊥` chain for the *quadratic subextension* needs the subfield `k⸨X²⸩` and is not
attempted. No new `structure`/`class`; no owed witness; D1 N/A; **D2 N/A** (the `Valued`
structure on `k⸨X⸩` is Mathlib's own canonical instance on a concrete type — no second structure
imposed anywhere, nothing leaks into the abstract files). Recovers nothing from an abstract
group; R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open scoped Pointwise

namespace Anabelian

open ValuationSubring IsLocalRing LaurentSeries

variable (k : Type*) [Field k]

/-! ### The involution `f(X) ↦ f(−X)` of `k⸨X⸩` -/

/-- `evalNegHom` is an involution of `k⟦X⟧`. -/
theorem evalNegHom_evalNegHom (f : PowerSeries k) :
    PowerSeries.evalNegHom (PowerSeries.evalNegHom f) = f := by
  change PowerSeries.rescale (-1 : k) (PowerSeries.rescale (-1 : k) f) = f
  rw [PowerSeries.rescale_rescale, neg_one_mul, neg_neg, PowerSeries.rescale_one,
    RingHom.id_apply]

/-- `evalNegHom` fixes constant coefficients. -/
theorem constantCoeff_evalNegHom (f : PowerSeries k) :
    PowerSeries.constantCoeff (PowerSeries.evalNegHom f) = PowerSeries.constantCoeff f := by
  change PowerSeries.constantCoeff (PowerSeries.rescale (-1 : k) f) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale]
  simp

/-- `evalNegHom` fixes constants. -/
theorem evalNegHom_C (c : k) :
    PowerSeries.evalNegHom (PowerSeries.C c) = PowerSeries.C c := by
  change PowerSeries.rescale (-1 : k) (PowerSeries.C c) = _
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

/-- The composite `k⟦X⟧ → k⟦X⟧ → k⸨X⸩`, sending `f(X)` to the Laurent series `f(−X)`. -/
noncomputable def laurentNegXAux : PowerSeries k →+* LaurentSeries k :=
  (algebraMap (PowerSeries k) (LaurentSeries k)).comp PowerSeries.evalNegHom

theorem laurentNegXAux_isUnit (y : Submonoid.powers (PowerSeries.X : PowerSeries k)) :
    IsUnit (laurentNegXAux k y) := by
  obtain ⟨n, hn⟩ := y.2
  have h1 : laurentNegXAux k y =
      (algebraMap (PowerSeries k) (LaurentSeries k) (-PowerSeries.X)) ^ n := by
    change (algebraMap (PowerSeries k) (LaurentSeries k)) (PowerSeries.evalNegHom y.1) = _
    rw [← hn, map_pow, PowerSeries.evalNegHom_X, map_pow]
  rw [h1]
  refine IsUnit.pow n (isUnit_iff_ne_zero.mpr ?_)
  rw [map_neg, neg_ne_zero, LaurentSeries.coe_algebraMap, HahnSeries.ofPowerSeries_X]
  exact HahnSeries.single_ne_zero one_ne_zero

/-- The ring endomorphism `f(X) ↦ f(−X)` of `k⸨X⸩`, lifted from `evalNegHom` along the
localization `k⸨X⸩ = k⟦X⟧[X⁻¹]`. -/
noncomputable def laurentNegXHom : LaurentSeries k →+* LaurentSeries k :=
  IsLocalization.lift (M := Submonoid.powers (PowerSeries.X : PowerSeries k))
    (laurentNegXAux_isUnit k)

/-- `laurentNegXHom` on (the image of) a power series is `evalNegHom`. -/
theorem laurentNegXHom_algebraMap (f : PowerSeries k) :
    laurentNegXHom k (algebraMap (PowerSeries k) (LaurentSeries k) f) =
      algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.evalNegHom f) :=
  IsLocalization.lift_eq _ f

theorem laurentNegXHom_laurentNegXHom (f : LaurentSeries k) :
    laurentNegXHom k (laurentNegXHom k f) = f := by
  have h : (laurentNegXHom k).comp (laurentNegXHom k) = RingHom.id (LaurentSeries k) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries k)) ?_
    ext g
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      laurentNegXHom_algebraMap, evalNegHom_evalNegHom]
  exact DFunLike.congr_fun h f

/-- The involution `f(X) ↦ f(−X)` as a `k`-algebra equivalence of `k⸨X⸩`. -/
noncomputable def laurentNegXAlgEquiv : LaurentSeries k ≃ₐ[k] LaurentSeries k :=
  AlgEquiv.ofRingEquiv
    (f := { laurentNegXHom k with
            invFun := laurentNegXHom k
            left_inv := laurentNegXHom_laurentNegXHom k
            right_inv := laurentNegXHom_laurentNegXHom k })
    (fun c => by
      have hC : algebraMap k (LaurentSeries k) c =
          algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.C c) := by
        rw [HahnSeries.algebraMap_apply', LaurentSeries.coe_algebraMap,
          PowerSeries.algebraMap_apply]
        simp
      change laurentNegXHom k (algebraMap k (LaurentSeries k) c) = algebraMap k (LaurentSeries k) c
      rw [hC, laurentNegXHom_algebraMap, evalNegHom_C])

@[simp] theorem laurentNegXAlgEquiv_apply (f : LaurentSeries k) :
    laurentNegXAlgEquiv k f = laurentNegXHom k f := rfl

/-- The `↑`-form of the power-series compatibility. -/
theorem laurentNegXAlgEquiv_coe (g : PowerSeries k) :
    laurentNegXAlgEquiv k (g : LaurentSeries k) =
      ((PowerSeries.evalNegHom g : PowerSeries k) : LaurentSeries k) := by
  have h1 : ∀ p : PowerSeries k, (p : LaurentSeries k) =
      algebraMap (PowerSeries k) (LaurentSeries k) p := by
    intro p
    rw [LaurentSeries.coe_algebraMap]
  rw [laurentNegXAlgEquiv_apply, h1 g, h1 (PowerSeries.evalNegHom g),
    laurentNegXHom_algebraMap]

/-- `σ` is an involution. -/
theorem laurentNegXAlgEquiv_laurentNegXAlgEquiv (f : LaurentSeries k) :
    laurentNegXAlgEquiv k (laurentNegXAlgEquiv k f) = f :=
  laurentNegXHom_laurentNegXHom k f

/-! ### The valuation subring `A = k⟦X⟧ ⊆ k⸨X⸩` and its uniformizer -/

/-- The `X`-adic valuation subring of `k⸨X⸩` (Mathlib's `Valued` instance): the unit ball
`{v ≤ 1}`, whose members are exactly the power series. -/
noncomputable def laurentIntegers : ValuationSubring (LaurentSeries k) :=
  (Valued.v : Valuation (LaurentSeries k) (WithZero (Multiplicative ℤ))).valuationSubring

theorem mem_laurentIntegers_iff (f : LaurentSeries k) :
    f ∈ laurentIntegers k ↔ ∃ g : PowerSeries k, (g : LaurentSeries k) = f := by
  rw [laurentIntegers, Valuation.mem_valuationSubring_iff,
    ← LaurentSeries.val_le_one_iff_eq_coe]

/-- The coe of a power series lies in `A`. -/
theorem coe_mem_laurentIntegers (g : PowerSeries k) :
    (g : LaurentSeries k) ∈ laurentIntegers k :=
  (mem_laurentIntegers_iff k _).mpr ⟨g, rfl⟩

/-- The uniformizer `π = X` of `A`. -/
noncomputable def laurentUniformizer : ↥(laurentIntegers k) :=
  ⟨((PowerSeries.X : PowerSeries k) : LaurentSeries k),
    coe_mem_laurentIntegers k PowerSeries.X⟩

theorem coe_laurentUniformizer :
    ((laurentUniformizer k : ↥(laurentIntegers k)) : LaurentSeries k) =
      ((PowerSeries.X : PowerSeries k) : LaurentSeries k) := rfl

theorem laurentUniformizer_ne_zero : laurentUniformizer k ≠ 0 := by
  intro h
  have h1 : ((PowerSeries.X : PowerSeries k) : LaurentSeries k) = 0 := by
    have h2 := congrArg Subtype.val h
    rw [coe_laurentUniformizer, ZeroMemClass.coe_zero] at h2
    exact h2
  exact PowerSeries.X_ne_zero
    (HahnSeries.ofPowerSeries_injective (by rw [h1, map_zero]))

/-- Any element of `A` whose power series has zero constant coefficient lies in `(π)`. -/
theorem mem_span_laurentUniformizer {x : ↥(laurentIntegers k)} {g : PowerSeries k}
    (hx : (x : LaurentSeries k) = (g : LaurentSeries k))
    (h0 : PowerSeries.constantCoeff g = 0) :
    x ∈ Ideal.span {laurentUniformizer k} := by
  obtain ⟨h, hh⟩ := PowerSeries.X_dvd_iff.mpr h0
  rw [Ideal.mem_span_singleton]
  refine ⟨⟨(h : LaurentSeries k), coe_mem_laurentIntegers k h⟩, ?_⟩
  apply Subtype.ext
  change (x : LaurentSeries k) =
    ((PowerSeries.X : PowerSeries k) : LaurentSeries k) * ((h : PowerSeries k) : LaurentSeries k)
  rw [hx, hh, map_mul]

/-- An element of `A` whose power series has *nonzero* constant coefficient is a unit of `A`. -/
theorem isUnit_of_constantCoeff_ne_zero {x : ↥(laurentIntegers k)} {g : PowerSeries k}
    (hx : (x : LaurentSeries k) = (g : LaurentSeries k))
    (h0 : PowerSeries.constantCoeff g ≠ 0) : IsUnit x := by
  have hg : IsUnit g := PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h0)
  obtain ⟨u, hu⟩ := hg
  refine isUnit_iff_exists.mpr
    ⟨⟨((u⁻¹ : (PowerSeries k)ˣ) : PowerSeries k), coe_mem_laurentIntegers k _⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (x : LaurentSeries k) * (((u⁻¹ : (PowerSeries k)ˣ) : PowerSeries k) : LaurentSeries k)
      = 1
    rw [hx, ← map_mul, ← hu, Units.mul_inv, map_one]
  · apply Subtype.ext
    change (((u⁻¹ : (PowerSeries k)ˣ) : PowerSeries k) : LaurentSeries k) * (x : LaurentSeries k)
      = 1
    rw [hx, ← map_mul, ← hu, Units.inv_mul, map_one]

/-- **The uniformizer equation `𝔪_A = (π)`** — the package the tame character consumes. -/
theorem maximalIdeal_laurentIntegers_eq_span :
    maximalIdeal ↥(laurentIntegers k) = Ideal.span {laurentUniformizer k} := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := (mem_laurentIntegers_iff k (x : LaurentSeries k)).mp x.2
    by_cases h0 : PowerSeries.constantCoeff g = 0
    · exact mem_span_laurentUniformizer k hg.symm h0
    · exact absurd (isUnit_of_constantCoeff_ne_zero k hg.symm h0)
        ((IsLocalRing.mem_maximalIdeal x).mp hx)
  · intro hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hx
    rw [IsLocalRing.mem_maximalIdeal, hc]
    intro hu
    have hπ : IsUnit (laurentUniformizer k) := isUnit_of_mul_isUnit_left hu
    obtain ⟨y, hy1, _⟩ := isUnit_iff_exists.mp hπ
    obtain ⟨h, hh⟩ := (mem_laurentIntegers_iff k (y : LaurentSeries k)).mp y.2
    have h2 : ((laurentUniformizer k : ↥(laurentIntegers k)) : LaurentSeries k) *
        ((y : ↥(laurentIntegers k)) : LaurentSeries k) = 1 := by
      have h2' := congrArg Subtype.val hy1
      simpa using h2'
    rw [coe_laurentUniformizer, ← hh] at h2
    have h1 : ((PowerSeries.X * h : PowerSeries k) : LaurentSeries k) =
        ((1 : PowerSeries k) : LaurentSeries k) := by
      rw [map_mul, map_one]
      exact h2
    have h2'' : (PowerSeries.X * h : PowerSeries k) = 1 :=
      HahnSeries.ofPowerSeries_injective h1
    have h3 : IsUnit (PowerSeries.X : PowerSeries k) :=
      isUnit_iff_exists.mpr ⟨h, h2'', by rw [mul_comm]; exact h2''⟩
    have h4 := PowerSeries.isUnit_constantCoeff _ h3
    rw [PowerSeries.constantCoeff_X] at h4
    exact not_isUnit_zero h4

/-! ### `σ` is in the decomposition subgroup -/

/-- `σ` maps `A` into `A`. -/
theorem laurentNegXAlgEquiv_mem (f : LaurentSeries k) (hf : f ∈ laurentIntegers k) :
    laurentNegXAlgEquiv k f ∈ laurentIntegers k := by
  obtain ⟨g, hg⟩ := (mem_laurentIntegers_iff k f).mp hf
  rw [← hg, laurentNegXAlgEquiv_coe]
  exact coe_mem_laurentIntegers k _

/-- `σ⁻¹ = σ` in `Aut(L/k)`. -/
theorem inv_laurentNegXAlgEquiv :
    (laurentNegXAlgEquiv k)⁻¹ = laurentNegXAlgEquiv k :=
  inv_eq_of_mul_eq_one_right (AlgEquiv.ext fun f => by
    rw [AlgEquiv.mul_apply, laurentNegXAlgEquiv_laurentNegXAlgEquiv, AlgEquiv.one_apply])

/-- **`σ` lies in the decomposition subgroup** (it stabilizes `A`). -/
theorem laurentNegX_mem_decompositionSubgroup :
    laurentNegXAlgEquiv k ∈ (laurentIntegers k).decompositionSubgroup k := by
  rw [MulAction.mem_stabilizer_iff]
  ext f
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, inv_laurentNegXAlgEquiv]
  change laurentNegXAlgEquiv k f ∈ laurentIntegers k ↔ f ∈ laurentIntegers k
  constructor
  · intro hf
    have h1 := laurentNegXAlgEquiv_mem k _ hf
    rwa [laurentNegXAlgEquiv_laurentNegXAlgEquiv] at h1
  · exact laurentNegXAlgEquiv_mem k f

/-- `σ` as an element of the decomposition subgroup. -/
noncomputable def laurentNegXDecomp : ↥((laurentIntegers k).decompositionSubgroup k) :=
  ⟨laurentNegXAlgEquiv k, laurentNegX_mem_decompositionSubgroup k⟩

/-- The coe bridge: the action of the decomposition subgroup on `↥A`, read in `L`. -/
theorem coe_laurentNegXDecomp_smul (a : ↥(laurentIntegers k)) :
    ((laurentNegXDecomp k • a : ↥(laurentIntegers k)) : LaurentSeries k) =
      laurentNegXAlgEquiv k (a : LaurentSeries k) := rfl

/-! ### `σ ∈ G₀` and `σ ∉ G₁` -/

/-- **`σ` lies in `G₀`**: it moves every integer by something with zero constant coefficient. -/
theorem laurentNegXDecomp_mem_ramificationGroup_zero :
    laurentNegXDecomp k ∈ ramificationGroup k (laurentIntegers k) 0 := by
  rw [mem_ramificationGroup_iff]
  intro a
  rw [zero_add, pow_one, maximalIdeal_laurentIntegers_eq_span]
  obtain ⟨g, hg⟩ := (mem_laurentIntegers_iff k (a : LaurentSeries k)).mp a.2
  refine mem_span_laurentUniformizer k
    (g := PowerSeries.evalNegHom g - g) ?_ ?_
  · change ((laurentNegXDecomp k • a : ↥(laurentIntegers k)) : LaurentSeries k)
        - (a : LaurentSeries k) = _
    rw [coe_laurentNegXDecomp_smul, ← hg, laurentNegXAlgEquiv_coe, map_sub]
  · rw [map_sub, constantCoeff_evalNegHom, sub_self]

/-- `σ • π = π * (−1)`: the tame unit of `σ` is `−1`. -/
theorem laurentNegXDecomp_smul_uniformizer :
    laurentNegXDecomp k • laurentUniformizer k =
      laurentUniformizer k * ↑(-1 : (↥(laurentIntegers k))ˣ) := by
  apply Subtype.ext
  rw [coe_laurentNegXDecomp_smul, coe_laurentUniformizer, laurentNegXAlgEquiv_coe,
    PowerSeries.evalNegHom_X, map_neg]
  have h1 : ((↑(-1 : (↥(laurentIntegers k))ˣ) : ↥(laurentIntegers k)) : LaurentSeries k)
      = -1 := by
    rw [Units.val_neg, Units.val_one]
    rfl
  change _ = ((laurentUniformizer k : ↥(laurentIntegers k)) : LaurentSeries k) *
    ((↑(-1 : (↥(laurentIntegers k))ˣ) : ↥(laurentIntegers k)) : LaurentSeries k)
  rw [h1, coe_laurentUniformizer, mul_neg_one]

/-- **`σ` does not lie in `G₁`** when `(2 : k) ≠ 0`: by Pass 24's `tameCharacter_eq_one`,
membership in `G₁` would force `θ₀(σ) = 1`; but `θ₀(σ) = −1` (the tame unit is `−1`), and
`−1 = 1` in the residue field would push down to `2 = 0` in `k`. -/
theorem laurentNegXDecomp_notMem_ramificationGroup_one (h2 : (2 : k) ≠ 0) :
    laurentNegXDecomp k ∉ ramificationGroup k (laurentIntegers k) 1 := by
  intro hmem
  have hspan := maximalIdeal_laurentIntegers_eq_span k
  have hπ0 := laurentUniformizer_ne_zero k
  -- the tame unit of σ is −1
  have hu : tameUnit k (laurentUniformizer k) hspan (laurentNegXDecomp k) = -1 :=
    tameUnit_unique k (laurentUniformizer k) hspan hπ0
      (laurentNegXDecomp_smul_uniformizer k)
  -- G₁-membership forces θ₀(σ) = 1
  have h1 : tameCharacter k (laurentUniformizer k) hspan hπ0
      ⟨laurentNegXDecomp k, laurentNegXDecomp_mem_ramificationGroup_zero k⟩ = 1 :=
    tameCharacter_eq_one k (laurentUniformizer k) hspan hπ0
      ⟨laurentNegXDecomp k, laurentNegXDecomp_mem_ramificationGroup_zero k⟩ hmem
  -- unpack: residue (−1) = 1 in 𝓀 (the defeq step validated in Pass 25)
  have h1' : Units.map (residue ↥(laurentIntegers k)).toMonoidHom
      (tameUnit k (laurentUniformizer k) hspan (laurentNegXDecomp k)) = 1 := h1
  have h3 : residue ↥(laurentIntegers k)
      ↑(tameUnit k (laurentUniformizer k) hspan (laurentNegXDecomp k)) = 1 := by
    have h4 := congrArg Units.val h1'
    simpa using h4
  rw [hu] at h3
  have h3' : residue ↥(laurentIntegers k) (-1 : ↥(laurentIntegers k)) = 1 := by
    rwa [Units.val_neg, Units.val_one] at h3
  -- −1 = 1 in 𝓀 means −1 − 1 = −2 ∈ 𝔪 = (π)
  have h5 : ((-1 : ↥(laurentIntegers k)) - 1) ∈ maximalIdeal ↥(laurentIntegers k) := by
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ?_
    change residue ↥(laurentIntegers k) (-1) = residue ↥(laurentIntegers k) 1
    rw [map_one, h3']
  rw [maximalIdeal_laurentIntegers_eq_span] at h5
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h5
  obtain ⟨h, hh⟩ := (mem_laurentIntegers_iff k (c : LaurentSeries k)).mp c.2
  -- push down to power series: −1 − 1 = X * h forces 0 = −2 in k at the constant coefficient
  have h7' := congrArg Subtype.val hc
  push_cast at h7'
  rw [coe_laurentUniformizer, ← hh] at h7'
  have h6 : (((-1 : PowerSeries k) - 1 : PowerSeries k) : LaurentSeries k) =
      ((PowerSeries.X * h : PowerSeries k) : LaurentSeries k) := by
    rw [map_sub, map_neg, map_one, map_mul]
    exact h7'
  have h8 : ((-1 : PowerSeries k) - 1 : PowerSeries k) = PowerSeries.X * h :=
    HahnSeries.ofPowerSeries_injective h6
  have h9 := congrArg PowerSeries.constantCoeff h8
  rw [map_sub, map_neg, map_one, map_mul, PowerSeries.constantCoeff_X, zero_mul] at h9
  -- h9 : (−1 − 1 : k) = 0, i.e. 2 = 0
  apply h2
  have h10 : (2 : k) = -((-1 : k) - 1) := by ring
  rw [h10, h9, neg_zero]

/-! ### The exhibit -/

/-- **The come-apart exhibit**: for the `X`-adic valuation subring of `k⸨X⸩` (`(2 : k) ≠ 0`),
the ramification filtration genuinely decreases at the first step. -/
theorem laurentRamificationGroup_zero_ne_one (h2 : (2 : k) ≠ 0) :
    ramificationGroup k (laurentIntegers k) 0 ≠ ramificationGroup k (laurentIntegers k) 1 :=
  fun h => laurentNegXDecomp_notMem_ramificationGroup_one k h2
    (h ▸ laurentNegXDecomp_mem_ramificationGroup_zero k)

/-- The fully closed witness, no hypotheses and no variables: over `ℚ⸨X⸩`,
**`G₀ ≠ G₁`**. -/
theorem ramificationGroup_zero_ne_one_rat :
    ramificationGroup ℚ (laurentIntegers ℚ) 0 ≠ ramificationGroup ℚ (laurentIntegers ℚ) 1 :=
  laurentRamificationGroup_zero_ne_one ℚ (by norm_num)

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms laurentNegXAlgEquiv
#print axioms maximalIdeal_laurentIntegers_eq_span
#print axioms laurentNegX_mem_decompositionSubgroup
#print axioms laurentNegXDecomp_mem_ramificationGroup_zero
#print axioms laurentNegXDecomp_notMem_ramificationGroup_one
#print axioms laurentRamificationGroup_zero_ne_one
#print axioms ramificationGroup_zero_ne_one_rat

end Anabelian
