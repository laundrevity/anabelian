/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.FiniteField
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable

/-!
# Rung L1, toward `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`: the Galois-side level subfields `𝔽_{q^n}` (Pass 9)

## What this pass is, and is not

This is **Pass 9** of the `≅ Ẑ` sub-plan (`ROADMAP.md`): it executes the one missing Galois-side
ingredient and is graded honestly as **infrastructure**, not the closed whole. Pass 8 resolved the
`≅ Ẑ` obstruction to a single absent construction — Mathlib has no `𝔽_{q^n}` as a
`FiniteGaloisIntermediateField` of `AlgebraicClosure K` — so the level projection
`Gal(K̄/K) → Gal(𝔽_{q^n}/K)` did not exist. This file builds exactly that, with the Frobenius
alignment Pass 10 will consume. **It does not close `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`**: injectivity of
`zhatToGalois` is the separate cofinality/diagram-chase step set up for Pass 10 below.

## What is built (for a finite field `K`, `q := Fintype.card K`, `n ≠ 0`)

* `Anabelian.levelField K n` — the degree-`n` subextension `𝔽_{q^n} ⊆ K̄`, as the fixed field of
  `Frob^n` (`Frob` the absolute Frobenius `x ↦ x^q`). `mem_levelField`:
  `x ∈ levelField K n ↔ x^(q^n) = x`.
* `Anabelian.levelField_finite`, `levelField_finrank` — it is finite, of degree exactly `n` over `K`
  (its carrier is the rootSet of the separable `X^(q^n) − X`, of cardinality `q^n`, and
  `q^n = q^(finrank)`).
* `Anabelian.levelFGIF K n` — `levelField K n` bundled as a `FiniteGaloisIntermediateField K K̄`
  (finite-dimensional + Galois, both automatic for a finite extension of a finite field).
* `Anabelian.levelRestrict K n` — the restriction `r_n : Gal(K̄/K) →* Gal(𝔽_{q^n}/K)`
  (`AlgEquiv.restrictNormalHom`), and `levelRestrict_surjective`.
* **The Frobenius alignment (the compatibility trap, handled):** `levelRestrict_frobenius` —
  `r_n (Frob) = frobeniusAlgEquivOfAlgebraic K (levelField K n)`, i.e. `r_n` sends the *absolute*
  Frobenius (which is `zhatToGalois (η (ofAdd 1))`, Pass 6) to the Frobenius of `𝔽_{q^n}`, **not**
  arbitrary cyclic generator. Hence `orderOf_levelRestrict_frobenius`: `orderOf (r_n Frob) = n`, so
  `r_n Frob` generates the cyclic `Gal(𝔽_{q^n}/K)`. This is precisely the generator Pass 10's
  square `r_n ∘ zhatToGalois = (level iso) ∘ (Ẑ → ℤ/n)` consumes.

## Honest grading

**Infrastructure, not a closed whole.** A `FiniteGaloisIntermediateField` term + a restriction
homomorphism + the Frobenius-alignment equation are the *means* to Pass 10's injectivity, not
`≅ Ẑ` itself. The half-accumulation pressure is satisfied only by the *eventual* `≅ Ẑ` at the end of
the sub-plan. **Recovers nothing from an abstract group**; no reach toward R1–R3. No load-bearing
hypothesis beyond `n ≠ 0` (`NeZero n`; for `n = 0` the "level field" is all of `K̄`, infinite — so
finite-level statements genuinely require it), no new `structure`/`class`
(`FiniteGaloisIntermediateField`
is Mathlib's), hence no rule-2 obligation.

## Axiom status

Standard axioms only (`#print axioms` below). Pass-9 ledger delta: **0 / 0** (no `DEBT`, no new
`FOUNDATIONAL`). The one existing `FOUNDATIONAL` entry (`residueReduction_surjective`, Pass 5) is
untouched and unused here.

## Pass 10 setup (what the injectivity step will consume)

With `χ_n := levelRestrict K n ∘ zhatToGalois : Ẑ → Gal(𝔽_{q^n}/K)`: `χ_n` is surjective (Pass 6
surjectivity ∘ `levelRestrict_surjective`) and `χ_n (η (ofAdd 1)) = r_n (Frob) =`
`frobeniusAlgEquivOfAlgebraic`
(Pass 6 `zhatToGalois_etaFn` + `levelRestrict_frobenius`), generating `Gal(𝔽_{q^n}/K)` of order `n`
(`orderOf_levelRestrict_frobenius`). So `ker χ_n` is the (open, index-`n`) subgroup of `Ẑ`. Pass 10:
show `⋂_n ker χ_n = ⊥` (each finite quotient of `Ẑ` is cyclic, Pass 8; a procyclic group has one
subgroup of each finite index, and these are cofinal) ⟹ `ker zhatToGalois = ⊥` ⟹ (with Pass 6
surjectivity) `zhatToGalois` bijective ⟹ the `ContinuousMulEquiv` via
`Continuous.homeoOfEquivCompactToT2` + `MulEquiv.ofBijective`. That closes `≅ Ẑ`.
-/

open Polynomial IntermediateField

namespace Anabelian

variable (K : Type) [Field K] [Fintype K]

/-- The absolute Frobenius `x ↦ x^q` of a finite field `K`, as an automorphism of `K̄`. This is the
same element as `zhatToGalois (η (ofAdd 1))` (Pass 6). -/
noncomputable abbrev absFrobenius : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
  FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)

/-- The degree-`n` level subfield `𝔽_{q^n} ⊆ K̄`, defined as the fixed field of `Frob^n`. -/
noncomputable def levelField (n : ℕ) : IntermediateField K (AlgebraicClosure K) :=
  fixedField (Subgroup.zpowers ((absFrobenius K) ^ n))

/-- Membership in the level field: `x ∈ 𝔽_{q^n}` iff `x^(q^n) = x` (fixed points of `Frob^n`). -/
theorem mem_levelField (n : ℕ) (x : AlgebraicClosure K) :
    x ∈ levelField K n ↔ x ^ (Fintype.card K ^ n) = x := by
  have key : ((absFrobenius K) ^ n) x = x ^ (Fintype.card K ^ n) := by
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [levelField, mem_fixedField_iff]
  constructor
  · intro h; rw [← key]; exact h _ (Subgroup.mem_zpowers _)
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hfix : ((absFrobenius K) ^ n) x = x := key.trans h
    have hfix' : ((absFrobenius K) ^ n)⁻¹ x = x := by
      apply ((absFrobenius K) ^ n).injective
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hfix]
    refine Int.induction_on k ?_ (fun m ih => ?_) (fun m ih => ?_)
    · simp
    · rw [zpow_add_one, AlgEquiv.mul_apply, hfix, ih]
    · rw [zpow_sub_one, AlgEquiv.mul_apply, hfix', ih]

/-- `X^(q^n) − X` is separable over `K` (its derivative is `−1`). -/
theorem separable_X_pow_card_pow_sub_X (n : ℕ) (hn : n ≠ 0) :
    (X ^ Fintype.card K ^ n - X : K[X]).Separable := by
  rw [separable_def]
  have hd : derivative (X ^ Fintype.card K ^ n - X : K[X]) = -1 := by
    rw [derivative_sub, derivative_X, derivative_X_pow]
    have : ((Fintype.card K ^ n : ℕ) : K) = 0 := by
      rw [Nat.cast_pow, Nat.cast_card_eq_zero, zero_pow hn]
    rw [this]; simp
  rw [hd]
  exact isCoprime_one_right.neg_right

/-- The carrier of the level field is exactly the rootSet of `X^(q^n) − X`. -/
theorem levelField_coe_eq_rootSet (n : ℕ) (hn : n ≠ 0) :
    (levelField K n : Set (AlgebraicClosure K))
      = (X ^ Fintype.card K ^ n - X : K[X]).rootSet (AlgebraicClosure K) := by
  have hne : (X ^ Fintype.card K ^ n - X : K[X]) ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero K hn Fintype.one_lt_card
  ext x
  rw [SetLike.mem_coe, mem_levelField, mem_rootSet]
  simp only [hne, ne_eq, not_false_eq_true, true_and, map_sub, map_pow, aeval_X, sub_eq_zero]

/-- The level field `𝔽_{q^n}` is finite (for `n ≠ 0`). -/
instance levelField_finite (n : ℕ) [NeZero n] : Finite (levelField K n) := by
  have hfin : ((levelField K n : Set (AlgebraicClosure K))).Finite :=
    (levelField_coe_eq_rootSet K n (NeZero.ne n)) ▸
      Polynomial.rootSet_finite (X ^ Fintype.card K ^ n - X) (AlgebraicClosure K)
  exact hfin.to_subtype

/-- **The level field `𝔽_{q^n}` has degree exactly `n` over `K`.** Its carrier is the rootSet of the
separable polynomial `X^(q^n) − X`, of cardinality `q^n`; and `q^n = q^(finrank K 𝔽_{q^n})`. -/
theorem levelField_finrank (n : ℕ) [NeZero n] : Module.finrank K (levelField K n) = n := by
  have hn : n ≠ 0 := NeZero.ne n
  have hsplit : Splits ((X ^ Fintype.card K ^ n - X : K[X]).map
      (algebraMap K (AlgebraicClosure K))) := IsAlgClosed.splits _
  have hcardroot : Nat.card ((X ^ Fintype.card K ^ n - X : K[X]).rootSet (AlgebraicClosure K))
      = Fintype.card K ^ n := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree (separable_X_pow_card_pow_sub_X K n hn)
        hsplit, FiniteField.X_pow_card_pow_sub_X_natDegree_eq K hn Fintype.one_lt_card]
  have hLFcard : Nat.card (levelField K n) = Fintype.card K ^ n := by
    rw [← hcardroot]; exact Nat.card_congr (Equiv.setCongr (levelField_coe_eq_rootSet K n hn))
  haveI : Fintype (levelField K n) := Fintype.ofFinite _
  have hpow : Fintype.card (levelField K n) = Fintype.card K ^ Module.finrank K (levelField K n) :=
    Module.card_eq_pow_finrank
  rw [← Nat.card_eq_fintype_card, hLFcard] at hpow
  exact Nat.pow_right_injective Fintype.one_lt_card hpow.symm

/-- The level field `𝔽_{q^n}`, bundled as a `FiniteGaloisIntermediateField K K̄`
(finite-dimensional and Galois — both automatic for a finite extension of a finite field). -/
noncomputable def levelFGIF (n : ℕ) [NeZero n] :
    FiniteGaloisIntermediateField K (AlgebraicClosure K) where
  toIntermediateField := levelField K n
  finiteDimensional := Module.Finite.of_finite
  isGalois := inferInstance

/-- The level projection `r_n : Gal(K̄/K) →* Gal(𝔽_{q^n}/K)` (restriction to the degree-`n`
subextension). -/
noncomputable def levelRestrict (n : ℕ) [NeZero n] :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* (levelField K n ≃ₐ[K] levelField K n) :=
  haveI : FiniteDimensional K (levelField K n) := Module.Finite.of_finite
  AlgEquiv.restrictNormalHom (levelField K n)

/-- The level projection `r_n` is surjective. -/
theorem levelRestrict_surjective (n : ℕ) [NeZero n] :
    Function.Surjective (levelRestrict K n) := by
  haveI : FiniteDimensional K (levelField K n) := Module.Finite.of_finite
  exact AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K)

/-- **The Frobenius-alignment equation (the compatibility trap).** `r_n` sends the *absolute*
Frobenius to the Frobenius of `𝔽_{q^n}` — not an arbitrary cyclic generator. Both are `x ↦ x^q`. -/
theorem levelRestrict_frobenius (n : ℕ) [NeZero n] :
    levelRestrict K n (absFrobenius K)
      = FiniteField.frobeniusAlgEquivOfAlgebraic K (levelField K n) := by
  haveI : FiniteDimensional K (levelField K n) := Module.Finite.of_finite
  ext y
  simp only [levelRestrict, AlgEquiv.restrictNormalHom_apply,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, IntermediateField.coe_pow]

/-- `r_n (Frob)` has order exactly `n` in `Gal(𝔽_{q^n}/K)` — so it generates that cyclic group.
This is the Frobenius-aligned generator Pass 10's commuting square consumes. -/
theorem orderOf_levelRestrict_frobenius (n : ℕ) [NeZero n] :
    orderOf (levelRestrict K n (absFrobenius K)) = n := by
  rw [levelRestrict_frobenius, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
    levelField_finrank]

-- Reproducible axiom audit. Standard axioms only — no `DEBT`, no `FOUNDATIONAL` used.
#print axioms levelField_finrank
#print axioms levelRestrict_surjective
#print axioms levelRestrict_frobenius
#print axioms orderOf_levelRestrict_frobenius

end Anabelian
