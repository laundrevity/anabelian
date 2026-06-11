/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic
import Anabelian.ExtensionResidueFinite
import Anabelian.InertiaCharpoly

/-!
# The descent finale: inertia-fixed integers cover the residue field (Pass 36)

`hresid` — the one lemma the general kernel theorem (Pass 34) awaited — and with it the
**unconditional** kernel theorem. The assembly is elementary (no Hensel, no Lucas, no
completeness), from the Pass-35 bricks:

* **`map_residue_inertiaFixedIntegers_eq_top`** — the residue image `F` of the inertia-fixed
  integers is ALL of `𝓀_L`. For any `b̄ ∈ 𝓀_L`, every coefficient of `(X − b̄)^{|G₀|}` lies in
  `F` (Pass 35). Writing `|G₀| = p^e·m` with `p ∤ m` (`p` the residue characteristic): the
  freshman's dream and `Polynomial.expand` identify the `X^{p^e(m−1)}`-coefficient as
  `−(b̄^{p^e})·m`; since `p ∤ m`, `m ≠ 0` in `𝓀_L` and `m^{q−1} = 1`, so multiplying by
  `m^{q−2} ∈ F` gives `b̄^{p^e} ∈ F`. The `p^e`-power map is the iterated Frobenius — injective,
  hence surjective on the finite `𝓀_L` — so `F = 𝓀_L`.
* **`inertiaFixedIntegers_residue_cover`** — `hresid` itself: every `x ∈ 𝒪_L` is congruent
  mod `𝔪_L` to an inertia-fixed integer.
* **`ker_tameCharacter_extensionIntegers_general`** — the finale: `ker θ₀ = G₁` for ANY finite
  separable extension of nonarchimedean local fields, unconditionally (Pass 34's reduction +
  `hresid`). Serre IV §2 Prop. 7 (level 0), general case: **the descent closes.**

Two design deviations from the Pass-35 plan, both simplifications: no cyclic generator of
`𝓀_Lˣ` is needed (surjectivity of the iterated Frobenius replaces the generator transport),
and no subfield structure on `F` is needed (`m⁻¹ = m^{q−2}` keeps everything in
subring-membership arithmetic).

## Honesty

`hresid` is here a theorem, not a hypothesis, for any finite separable `L/K` with `K`
nonarchimedean local — with `[Finite G₀]` and `[Algebra.IsSeparable K L]` exactly where
consumed (`Finite`, not `Fintype`: the statements never mention a cardinality, so the
linter-correct hypothesis is the proposition, with `Fintype.ofFinite` local to the proof).
Classically the content is "`L/L₀` is totally ramified" (Serre I §7); it is proved
directly, without constructing `L₀`. The kernel theorem's remaining inputs (`π`, `hspan`,
`hπ0`) are the uniformizer package, discharged for `𝒪_L` in Pass 30. No new
`structure`/`class`; no owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group;
R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing Polynomial

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The residue image of the inertia-fixed integers is everything**: every element of `𝓀_L`
is the residue of an inertia-fixed integer. The Pass-35 orbit-polynomial bricks, the freshman's
dream at `|G₀| = p^e·m`, and surjectivity of the iterated Frobenius assemble into `F = 𝓀_L`. -/
theorem map_residue_inertiaFixedIntegers_eq_top [Algebra.IsSeparable K L]
    [Finite ↥(ramificationGroup K (extensionIntegers K L) 0)] :
    (inertiaFixedIntegers K L).map (residue ↥(extensionIntegers K L)) = ⊤ := by
  haveI hfin : Finite (ResidueField ↥(extensionIntegers K L)) :=
    finite_residueField_extensionIntegers K L
  haveI := Fintype.ofFinite (ResidueField ↥(extensionIntegers K L))
  haveI hPrime : Fact (ringChar (ResidueField ↥(extensionIntegers K L))).Prime :=
    ⟨CharP.char_is_prime (ResidueField ↥(extensionIntegers K L))
      (ringChar (ResidueField ↥(extensionIntegers K L)))⟩
  haveI : Nonempty ↥(ramificationGroup K (extensionIntegers K L) 0) := ⟨1⟩
  haveI := Fintype.ofFinite ↥(ramificationGroup K (extensionIntegers K L) 0)
  obtain ⟨e, m, hpm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Fintype.card_ne_zero (α := ↥(ramificationGroup K (extensionIntegers K L) 0)))
    (ringChar (ResidueField ↥(extensionIntegers K L))) hPrime.out.ne_one
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (fun h => hpm (h ▸ dvd_zero _))
  rw [Subring.eq_top_iff']
  intro ξ
  -- realize ξ as a `p^e`-th power of a residue: iterated Frobenius is injective, hence
  -- surjective on the finite `𝓀_L`, and the residue map is surjective
  obtain ⟨η, hη⟩ := Finite.injective_iff_surjective.mp
    (RingHom.injective (iterateFrobenius (ResidueField ↥(extensionIntegers K L))
      (ringChar (ResidueField ↥(extensionIntegers K L))) e)) ξ
  rw [iterateFrobenius_def] at hη
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective η
  have hb' : residue ↥(extensionIntegers K L) b = η := hb
  -- every coefficient of `(X − b̄)^{|G₀|}` is in the image `F` (the Pass-35 bricks)
  have hcoe : ∀ k : ℕ,
      ((X - C (residue ↥(extensionIntegers K L) b))
          ^ Fintype.card ↥(ramificationGroup K (extensionIntegers K L) 0)).coeff k
        ∈ (inertiaFixedIntegers K L).map (residue ↥(extensionIntegers K L)) := by
    intro k
    exact Subring.mem_map.mpr
      ⟨(MulSemiringAction.charpoly
          ↥(ramificationGroup K (extensionIntegers K L) 0) b).coeff k,
        coeff_inertiaCharpoly_mem K L b k,
        by rw [← Polynomial.coeff_map, map_residue_inertiaCharpoly K L b]⟩
  -- the freshman's dream extracts `−(b̄^{p^e})·m` at the `X^{p^e(m−1)}`-coefficient
  have key : ((X - C (residue ↥(extensionIntegers K L) b))
        ^ Fintype.card ↥(ramificationGroup K (extensionIntegers K L) 0)).coeff
          (ringChar (ResidueField ↥(extensionIntegers K L)) ^ e * (m - 1))
      = -(residue ↥(extensionIntegers K L) b
            ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e)
          * (m : ResidueField ↥(extensionIntegers K L)) := by
    rw [hcard, pow_mul,
      sub_pow_expChar_pow_of_commute (ringChar (ResidueField ↥(extensionIntegers K L))) e
        (Commute.all _ _),
      ← C_pow,
      show (X : (ResidueField ↥(extensionIntegers K L))[X])
            ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e
          - C (residue ↥(extensionIntegers K L) b
              ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e)
        = expand (ResidueField ↥(extensionIntegers K L))
            (ringChar (ResidueField ↥(extensionIntegers K L)) ^ e)
            (X - C (residue ↥(extensionIntegers K L) b
              ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e))
        from by rw [map_sub, expand_X, expand_C],
      ← map_pow,
      coeff_expand (expChar_pow_pos (ResidueField ↥(extensionIntegers K L))
        (ringChar (ResidueField ↥(extensionIntegers K L))) e),
      if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (expChar_pow_pos (ResidueField ↥(extensionIntegers K L))
        (ringChar (ResidueField ↥(extensionIntegers K L))) e),
      sub_eq_add_neg, ← map_neg, coeff_X_add_C_pow,
      Nat.sub_sub_self hm1, pow_one, Nat.choose_symm hm1, Nat.choose_one_right]
  have hcF := hcoe (ringChar (ResidueField ↥(extensionIntegers K L)) ^ e * (m - 1))
  rw [key] at hcF
  -- strip the sign, then divide out `m` by `m^{q−2}` (all inside `F`)
  have hmul : residue ↥(extensionIntegers K L) b
        ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e
        * (m : ResidueField ↥(extensionIntegers K L))
      ∈ (inertiaFixedIntegers K L).map (residue ↥(extensionIntegers K L)) := by
    have h2 := ((inertiaFixedIntegers K L).map
      (residue ↥(extensionIntegers K L))).neg_mem hcF
    rwa [neg_mul, neg_neg] at h2
  have hm0 : (m : ResidueField ↥(extensionIntegers K L)) ≠ 0 := fun h =>
    hpm ((CharP.cast_eq_zero_iff (ResidueField ↥(extensionIntegers K L))
      (ringChar (ResidueField ↥(extensionIntegers K L))) m).mp h)
  have hq1 : (m : ResidueField ↥(extensionIntegers K L))
        ^ (Fintype.card (ResidueField ↥(extensionIntegers K L)) - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hm0
  have hmem : residue ↥(extensionIntegers K L) b
        ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e
      ∈ (inertiaFixedIntegers K L).map (residue ↥(extensionIntegers K L)) := by
    have hrepr : residue ↥(extensionIntegers K L) b
          ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e
        = (m : ResidueField ↥(extensionIntegers K L))
              ^ (Fintype.card (ResidueField ↥(extensionIntegers K L)) - 2)
            * (residue ↥(extensionIntegers K L) b
                ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e
              * (m : ResidueField ↥(extensionIntegers K L))) := by
      rw [mul_comm (residue ↥(extensionIntegers K L) b
            ^ ringChar (ResidueField ↥(extensionIntegers K L)) ^ e)
          (m : ResidueField ↥(extensionIntegers K L)),
        ← mul_assoc, ← pow_succ,
        show Fintype.card (ResidueField ↥(extensionIntegers K L)) - 2 + 1
            = Fintype.card (ResidueField ↥(extensionIntegers K L)) - 1 from by
          have := Fintype.one_lt_card (α := ResidueField ↥(extensionIntegers K L))
          omega,
        hq1, one_mul]
    rw [hrepr]
    exact Subring.mul_mem _ (Subring.pow_mem _ (natCast_mem _ m) _) hmul
  rw [← hη, ← hb']
  exact hmem

/-- **`hresid` is a theorem**: every `x ∈ 𝒪_L` is congruent mod `𝔪_L` to an inertia-fixed
integer — the inertia-fixed integers cover the residue field. -/
theorem inertiaFixedIntegers_residue_cover [Algebra.IsSeparable K L]
    [Finite ↥(ramificationGroup K (extensionIntegers K L) 0)]
    (x : ↥(extensionIntegers K L)) :
    ∃ a ∈ inertiaFixedIntegers K L, x - a ∈ maximalIdeal ↥(extensionIntegers K L) := by
  have hξ : residue ↥(extensionIntegers K L) x
      ∈ (inertiaFixedIntegers K L).map (residue ↥(extensionIntegers K L)) := by
    rw [map_residue_inertiaFixedIntegers_eq_top K L]
    exact Subring.mem_top _
  obtain ⟨a, ha, hax⟩ := Subring.mem_map.mp hξ
  exact ⟨a, ha, (Ideal.Quotient.mk_eq_mk_iff_sub_mem x a).mp hax.symm⟩

/-- **The unconditional general kernel theorem — the descent closes**: for ANY finite separable
extension of nonarchimedean local fields and any uniformizer of `𝒪_L`, `ker θ₀ = G₁`.
Pass 34's reduction + `hresid` (now a theorem). Serre IV §2 Prop. 7 (level 0), general case. -/
theorem ker_tameCharacter_extensionIntegers_general [Algebra.IsSeparable K L]
    [Finite ↥(ramificationGroup K (extensionIntegers K L) 0)]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0) :
    (tameCharacter K π hspan hπ0).ker
      = (ramificationGroup K (extensionIntegers K L) 1).subgroupOf
          (ramificationGroup K (extensionIntegers K L) 0) :=
  ker_tameCharacter_of_inertiaFixed_cover K L π hspan hπ0
    (inertiaFixedIntegers_residue_cover K L)

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms map_residue_inertiaFixedIntegers_eq_top
#print axioms inertiaFixedIntegers_residue_cover
#print axioms ker_tameCharacter_extensionIntegers_general

end Anabelian
