/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.RamificationFiltration
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Rung L2: the tame character `θ₀ : G₀ →* 𝓀ˣ` — homomorphism and kernel (Pass 24)

The first structurally rich theorem of the ramification filtration (Serre, *Local Fields*, IV §2,
Prop. 7's map at level 0): for a uniformizer `π` (a generator of the maximal ideal,
`𝔪_A = (π)` — supplied by any DVR, `irreducible_iff_uniformizer`), every inertia element `σ ∈ G_0`
moves `π` by a unit, `σ(π) = π·u_σ`, and

> `θ₀(σ) := u_σ mod 𝔪` defines a **group homomorphism** `G_0 →* 𝓀ˣ` with **`G_1` in its kernel**,
> hence an induced map `G_0/G_1 →* 𝓀ˣ` — and `θ₀` is **independent of the chosen uniformizer**.

## What is proved (all axiom-free)

* `Anabelian.smulUnit` — the action of a decomposition element on a unit, as a unit (the
  `MulDistribMulAction` units-instance does not synthesize here, so it is constructed directly).
* `Anabelian.exists_smul_uniformizer_eq` / `tameUnit` / `tameUnit_spec` / `tameUnit_unique` —
  `σ(π) = π·u_σ` with `u_σ` a (unique) unit: `σ` preserves `𝔪 = (π)` in both directions
  (`smul_mem_maximalIdeal_pow`), so `π ∣ σπ ∣ π` and `associated_of_dvd_dvd` produces the unit.
* `Anabelian.residue_smul_eq_of_mem_ramificationGroup_zero` — inertia elements fix residue
  classes (the `G_0`-membership condition, read mod `𝔪`).
* `Anabelian.tameCharacter` — **`θ₀ : G_0 →* 𝓀ˣ` is a homomorphism.** The cocycle computation
  `(στ)(π) = π · u_σ · σ(u_τ)` would only give a *crossed* homomorphism in general; it is an
  honest homomorphism **because `σ ∈ G_0`**: inertia acts trivially on residues, so
  `σ(u_τ) ≡ u_τ mod 𝔪`. (This is why `θ₀` is defined on `G_0` and not on the full decomposition
  group.)
* `Anabelian.tameCharacter_eq_one` — **`G_1 ≤ ker θ₀`**: for `σ ∈ G_1`, `σπ − π = π(u_σ − 1) ∈ 𝔪²
  = (π²)`, and cancelling `π` gives `u_σ ≡ 1 mod 𝔪`.
* `Anabelian.tameQuotientHom` — the induced `G_0/G_1 →* 𝓀ˣ` (`QuotientGroup.lift`; `G_1` is
  normal in the decomposition group by Pass 23, hence in `G_0`).
* `Anabelian.tameCharacter_eq_of_span_eq` — **uniformizer-independence**: for `π' = πw` (`w` a
  unit), `u'_σ = w⁻¹·u_σ·σ(w)` and `σ(w) ≡ w mod 𝔪` (inertia again), so the residues agree.
  `θ₀` is canonical, deserving its definite article.

## Honesty: the half NOT proved (deliberately)

**Injectivity of the induced `G_0/G_1 →* 𝓀ˣ`** — i.e. `ker θ₀ = G_1`, the full classical
embedding (with its corollaries: `G_0/G_1` abelian, cyclic when finite) — is **not** attempted.
Classically it needs more than this file's setting provides: `σ ∈ G_i` must be *detected on the
single element `π`* (`v(σπ − π) ≥ i+1 ⟹ σ ∈ G_i`), which holds when `𝒪_L` is monogenic over the
inertia-fixed subring (Serre IV §1 Prop. 5 — from completeness/total ramification via Eisenstein),
not for a bare valuation subring with principal maximal ideal. Scoped out up front (the Pass-22
lesson: under-promise); logged in `ROADMAP.md` as the next L2 rung, together with wild `G_1`
pro-`p`.

**Not reconstruction.** Galois-action structure of given fields; no reach toward R1–R3.

**No new owed witness.** The hypotheses (`𝔪 = (π)`, `π ≠ 0`) are *used constructively* to build
the map, not claimed-essential-for-a-theorem; no rule-2 obligation. No new `structure`/`class`.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged. D1 N/A; D2 N/A (`ValuationSubring`-native).
-/

open scoped Pointwise

namespace Anabelian

open ValuationSubring IsLocalRing

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}

/-- The image of a unit of `A` under a decomposition element, as a unit (the action is by ring
automorphisms, which preserve units; constructed directly since the generic units-action instance
does not synthesize for this action). -/
def smulUnit (σ : A.decompositionSubgroup K) (u : (↥A)ˣ) : (↥A)ˣ where
  val := σ • ↑u
  inv := σ • ↑u⁻¹
  val_inv := by rw [← smul_mul']; simp
  inv_val := by rw [← smul_mul']; simp

@[simp] theorem smulUnit_val (σ : A.decompositionSubgroup K) (u : (↥A)ˣ) :
    (↑(smulUnit K σ u) : ↥A) = σ • ↑u := rfl

/-- Every decomposition element moves a uniformizer by a unit: `σ • π = π * u`. (`σ` preserves
`𝔪 = (π)` in both directions, so `π ∣ σπ` and `σπ ∣ π`.) -/
theorem exists_smul_uniformizer_eq (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (σ : A.decompositionSubgroup K) :
    ∃ u : (↥A)ˣ, σ • π = π * ↑u := by
  have hmem : π ∈ maximalIdeal ↥A := by
    rw [hspan]; exact Ideal.mem_span_singleton_self π
  have h1 : π ∣ σ • π := by
    have := smul_mem_maximalIdeal_pow K A σ (n := 1) (by simpa using hmem)
    rw [pow_one, hspan, Ideal.mem_span_singleton] at this
    exact this
  have h2 : σ • π ∣ π := by
    have hinv := smul_mem_maximalIdeal_pow K A σ⁻¹ (n := 1) (by simpa using hmem)
    rw [pow_one, hspan, Ideal.mem_span_singleton] at hinv
    obtain ⟨c, hc⟩ := hinv
    refine ⟨σ • c, ?_⟩
    have := congrArg (σ • ·) hc
    simpa [smul_mul'] using this
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd h1 h2
  exact ⟨u, hu.symm⟩

/-- The unit by which `σ` moves the uniformizer `π`: `σ • π = π * tameUnit σ`. -/
noncomputable def tameUnit (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (σ : A.decompositionSubgroup K) : (↥A)ˣ :=
  (exists_smul_uniformizer_eq K π hspan σ).choose

theorem tameUnit_spec (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (σ : A.decompositionSubgroup K) :
    σ • π = π * ↑(tameUnit K π hspan σ) :=
  (exists_smul_uniformizer_eq K π hspan σ).choose_spec

theorem tameUnit_unique (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    {σ : A.decompositionSubgroup K} {u : (↥A)ˣ}
    (hu : σ • π = π * ↑u) : tameUnit K π hspan σ = u := by
  have h := tameUnit_spec K π hspan σ
  rw [hu] at h
  exact Units.ext (mul_left_cancel₀ hπ0 h.symm)

/-- Inertia elements fix residue classes: the `G_0`-membership condition read mod `𝔪`. -/
theorem residue_smul_eq_of_mem_ramificationGroup_zero
    {σ : A.decompositionSubgroup K} (hσ : σ ∈ ramificationGroup K A 0) (a : ↥A) :
    residue ↥A (σ • a) = residue ↥A a := by
  have h := (mem_ramificationGroup_iff K A σ).mp hσ a
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by simpa using h)

/-- **The tame character** `θ₀ : G₀ →* 𝓀ˣ` (Serre IV §2): `σ ↦ (σπ/π) mod 𝔪`. Multiplicativity
is where inertia bites: `(στ)π = π · u_σ · σ(u_τ)`, a crossed-homomorphism cocycle in general,
becomes an honest homomorphism because `σ ∈ G_0` fixes residues (`σ(u_τ) ≡ u_τ mod 𝔪`).
Independent of the uniformizer (`tameCharacter_eq_of_span_eq`); kills `G_1`
(`tameCharacter_eq_one`). -/
noncomputable def tameCharacter (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) : ↥(ramificationGroup K A 0) →* (ResidueField ↥A)ˣ where
  toFun σ := Units.map (residue ↥A).toMonoidHom (tameUnit K π hspan σ.1)
  map_one' := by
    have h1 : (1 : A.decompositionSubgroup K) • π = π * ↑(1 : (↥A)ˣ) := by simp
    rw [show ((1 : ↥(ramificationGroup K A 0)) : A.decompositionSubgroup K) = 1 from rfl,
      tameUnit_unique K π hspan hπ0 h1]
    simp
  map_mul' σ τ := by
    have hcomp : (σ.1 * τ.1) • π =
        π * ↑(tameUnit K π hspan σ.1 * smulUnit K σ.1 (tameUnit K π hspan τ.1)) := by
      rw [mul_smul, tameUnit_spec K π hspan τ.1, smul_mul', tameUnit_spec K π hspan σ.1,
        Units.val_mul, smulUnit_val]
      ring
    rw [show ((σ * τ : ↥(ramificationGroup K A 0)) : A.decompositionSubgroup K)
        = σ.1 * τ.1 from rfl, tameUnit_unique K π hspan hπ0 hcomp]
    rw [map_mul]
    congr 1
    apply Units.ext
    show residue ↥A ↑(smulUnit K σ.1 (tameUnit K π hspan τ.1))
        = residue ↥A ↑(tameUnit K π hspan τ.1)
    rw [smulUnit_val]
    exact residue_smul_eq_of_mem_ramificationGroup_zero K σ.2 _

/-- **`G₁` lies in the kernel of the tame character**: for `σ ∈ G_1`,
`σπ − π = π(u_σ − 1) ∈ 𝔪² = (π²)`, and cancelling `π` gives `u_σ ≡ 1 mod 𝔪`. -/
theorem tameCharacter_eq_one (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) (σ : ↥(ramificationGroup K A 0))
    (hσ : σ.1 ∈ ramificationGroup K A 1) :
    tameCharacter K π hspan hπ0 σ = 1 := by
  have h := (mem_ramificationGroup_iff K A σ.1).mp hσ π
  rw [tameUnit_spec K π hspan σ.1, hspan, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at h
  obtain ⟨r, hr⟩ := h
  have hu1 : (↑(tameUnit K π hspan σ.1) : ↥A) - 1 = π * r := by
    have h2 : π * (↑(tameUnit K π hspan σ.1) - 1) = π * (π * r) := by
      rw [mul_sub, mul_one, hr]
      ring
    exact mul_left_cancel₀ hπ0 h2
  apply Units.ext
  show residue ↥A ↑(tameUnit K π hspan σ.1) = 1
  have hsub : residue ↥A ↑(tameUnit K π hspan σ.1) = residue ↥A 1 :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (by rw [hu1, hspan]; exact Ideal.mem_span_singleton.mpr ⟨r, rfl⟩)
  simpa using hsub

/-- The induced homomorphism on the tame quotient, `G₀/G₁ →* 𝓀ˣ`. Its injectivity — the full
classical embedding, giving `G_0/G_1` abelian/cyclic — needs the monogenicity input and is the
next L2 rung (`ROADMAP.md`), not claimed here. -/
noncomputable def tameQuotientHom (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) :
    (↥(ramificationGroup K A 0) ⧸
      ((ramificationGroup K A 1).subgroupOf (ramificationGroup K A 0))) →*
      (ResidueField ↥A)ˣ :=
  QuotientGroup.lift _ (tameCharacter K π hspan hπ0) fun σ hσ =>
    tameCharacter_eq_one K π hspan hπ0 σ (Subgroup.mem_subgroupOf.mp hσ)

/-- **Uniformizer-independence**: the tame character does not depend on the choice of generator
of `𝔪` — for `π' = πw` (`w` a unit), `u'_σ = w⁻¹ · u_σ · σ(w)` and inertia gives
`σ(w) ≡ w mod 𝔪`, so the residues agree. `θ₀` is canonical. -/
theorem tameCharacter_eq_of_span_eq (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π})
    (hπ0 : π ≠ 0) (π' : ↥A) (hspan' : maximalIdeal ↥A = Ideal.span {π'}) (hπ0' : π' ≠ 0) :
    tameCharacter K π hspan hπ0 = tameCharacter K π' hspan' hπ0' := by
  have hassoc : Associated π π' :=
    Ideal.span_singleton_eq_span_singleton.mp (hspan.symm.trans hspan')
  obtain ⟨w, hw⟩ := hassoc
  refine MonoidHom.ext fun σ => Units.ext ?_
  have hu' : σ.1 • π' = π' * ↑(w⁻¹ * tameUnit K π hspan σ.1 * smulUnit K σ.1 w) := by
    rw [← hw, smul_mul', tameUnit_spec K π hspan σ.1]
    rw [Units.val_mul, Units.val_mul, smulUnit_val]
    have hwinv : (↑w : ↥A) * ↑w⁻¹ = 1 := by simp
    calc π * ↑(tameUnit K π hspan σ.1) * (σ.1 • ↑w)
        = π * (↑w * ↑w⁻¹) * ↑(tameUnit K π hspan σ.1) * (σ.1 • ↑w) := by rw [hwinv]; ring
      _ = π * ↑w * (↑w⁻¹ * ↑(tameUnit K π hspan σ.1) * (σ.1 • ↑w)) := by ring
  show residue ↥A ↑(tameUnit K π hspan σ.1) = residue ↥A ↑(tameUnit K π' hspan' σ.1)
  rw [tameUnit_unique K π' hspan' hπ0' hu', Units.val_mul, Units.val_mul, smulUnit_val,
    map_mul, map_mul, residue_smul_eq_of_mem_ramificationGroup_zero K σ.2 (w : ↥A)]
  have hwres : residue ↥A ↑w⁻¹ * residue ↥A ↑w = 1 := by
    rw [← map_mul]; simp
  calc residue ↥A ↑(tameUnit K π hspan σ.1)
      = residue ↥A ↑(tameUnit K π hspan σ.1) * (residue ↥A ↑w⁻¹ * residue ↥A ↑w) := by
        rw [hwres, mul_one]
    _ = residue ↥A ↑w⁻¹ * residue ↥A ↑(tameUnit K π hspan σ.1) * residue ↥A ↑w := by ring

/-- The tame character in the DVR case, from any irreducible element (every irreducible of a DVR
is a uniformizer, `irreducible_iff_uniformizer`). The natural entry point for the eventual
local-field instantiation `A = 𝒪_L`. -/
noncomputable def tameCharacterOfIrreducible [IsDiscreteValuationRing ↥A]
    (π : ↥A) (hπ : Irreducible π) :
    ↥(ramificationGroup K A 0) →* (ResidueField ↥A)ˣ :=
  tameCharacter K π ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ) hπ.ne_zero

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms smulUnit
#print axioms exists_smul_uniformizer_eq
#print axioms tameUnit_spec
#print axioms tameUnit_unique
#print axioms residue_smul_eq_of_mem_ramificationGroup_zero
#print axioms tameCharacter
#print axioms tameCharacter_eq_one
#print axioms tameQuotientHom
#print axioms tameCharacter_eq_of_span_eq
#print axioms tameCharacterOfIrreducible

end Anabelian
