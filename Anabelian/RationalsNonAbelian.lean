/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Discharging owed witness W1: the absolute Galois group of ℚ is non-commutative

This file discharges **W1** (`AXIOM_LEDGER.md`), the load-bearing-hypothesis witness owed since
Pass 1: it proves a *concrete* field — ℚ — whose absolute Galois group is **non-commutative**, hence
non-procyclic. This shows `[Finite F]` is genuinely load-bearing for the Pass-1/Pass-2
finite-field lemmas (`Anabelian.absoluteGaloisGroup_mul_comm`,
`Anabelian.frobenius_topologicalClosure_eq_top`): those would be **false** for the non-finite ℚ.

## What is proved

`Anabelian.rationals_absoluteGaloisGroup_not_commutative`:
`¬ ∀ σ τ : Field.absoluteGaloisGroup ℚ, σ * τ = τ * σ`.

Proof: the splitting field of `X³ - 2` over ℚ has Galois group `≅ S₃` (non-abelian), via Mathlib's
`Gal.galActionHom_bijective_of_prime_degree'` (an irreducible prime-degree rational polynomial with
the right real/complex root count has full symmetric Galois group). The absolute Galois group
surjects onto it (`Gal.restrict_surjective`), and a surjection onto a non-abelian group is
non-abelian.

## Why this is genuine content — and what it is NOT

It is the **discharge of a tracked debt of rigor**: Passes 1–2 *claimed* `[Finite F]` was essential
but only registered the witness (W1). This proves it. It is **not** reconstruction: the statement is
a property of the Galois action on the *given* field ℚ (and its given algebraic closure); nothing is
recovered from an abstract topological group. It introduces no new load-bearing hypothesis of its
own (it *is* the counterexample witness), and no new `structure`/`class`.

## A note on the ℚ-algebra diamond

The proof locally disables the instance `DivisionRing.toRatAlgebra`. Without this, instance
resolution gives `Algebra ℚ (AlgebraicClosure ℚ)` via the generic "every characteristic-0 division
ring is a ℚ-algebra" route rather than `AlgebraicClosure.instAlgebra`, and the two do not match at
the reducibility used by instance search — so `Normal ℚ (AlgebraicClosure ℚ)` (needed by
`restrict_surjective`) fails to synthesize. Disabling the generic instance for this declaration
makes every `Algebra ℚ (AlgebraicClosure ℚ)` use the algebraic-closure structure consistently (the
same one baked into `Field.absoluteGaloisGroup ℚ`), and the proof goes through. This was found by
probe (see this pass's `NOTES.md`); the `ℂ`-side (`Algebra ℚ ℂ`) is unaffected, as ℂ carries its own
ℚ-algebra instance.

## Axiom status

Standard axioms only (`#print axioms` below). Pass-3 ledger delta: **0 DEBT / 0 FOUNDATIONAL**;
Owed witnesses: **W1 discharged**.
-/

open Polynomial Polynomial.Gal

namespace Anabelian

/-- `2` is not a cube in `ℚ` (so `X³ - 2` is irreducible over `ℚ`). Proof via the rational root
theorem: a rational root of the monic integer polynomial `X³ - 2` is an integer, and no integer
cubes to `2`. -/
theorem two_not_cube : ∀ b : ℚ, b ^ 3 ≠ 2 := by
  intro b hb
  have hroot : aeval b (X ^ 3 - C 2 : ℤ[X]) = 0 := by
    have h : aeval b (X ^ 3 - C 2 : ℤ[X]) = b ^ 3 - 2 := by
      simp [map_sub, map_pow, aeval_X, map_ofNat]
    rw [h, hb]; norm_num
  have hmonic : (X ^ 3 - C 2 : ℤ[X]).Monic := monic_X_pow_sub_C 2 (by norm_num)
  obtain ⟨n, hn⟩ := isInteger_of_is_root_of_monic hmonic hroot
  simp only [algebraMap_int_eq, eq_intCast] at hn
  have hn3 : (n : ℤ) ^ 3 = 2 := by
    have : (n : ℚ) ^ 3 = 2 := by rw [hn]; exact hb
    exact_mod_cast this
  have hdvd : n ∣ 2 := ⟨n ^ 2, by rw [← hn3]; ring⟩
  have hub : n ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  have hlb : -2 ≤ n := by
    have := Int.le_of_dvd (show (0:ℤ) < 2 by norm_num) (neg_dvd.mpr hdvd); linarith
  interval_cases n <;> norm_num at hn3

attribute [-instance] DivisionRing.toRatAlgebra in
/-- **The absolute Galois group of `ℚ` is non-commutative.** This discharges owed witness W1:
`[Finite F]` is load-bearing for the finite-field commutativity/procyclicity lemmas, since their
conclusion fails for the (non-finite) field `ℚ`. -/
theorem rationals_absoluteGaloisGroup_not_commutative :
    ¬ ∀ σ τ : Field.absoluteGaloisGroup ℚ, σ * τ = τ * σ := by
  set f : ℚ[X] := X ^ 3 - C 2 with hf
  -- `X³ - 2` is irreducible of prime degree 3 and separable.
  have hf_irr : Irreducible f := X_pow_sub_C_irreducible_of_prime Nat.prime_three two_not_cube
  have hf_deg : f.natDegree = 3 := by rw [hf, natDegree_X_pow_sub_C]
  have hf_sep : f.Separable := hf_irr.separable
  haveI : Fact ((f.map (algebraMap ℚ ℂ)).Splits) := ⟨IsAlgClosed.splits (f.map _)⟩
  -- It has 3 complex roots and ≤ 1 real root (the cube map is injective on ℝ).
  have hcardC : Fintype.card (f.rootSet ℂ) = 3 := by
    rw [card_rootSet_eq_natDegree hf_sep (IsAlgClosed.splits (f.map _)), hf_deg]
  have hcardR : Fintype.card (f.rootSet ℝ) ≤ 1 := by
    rw [Fintype.card_le_one_iff_subsingleton, Set.subsingleton_coe]
    intro x hx y hy
    simp only [hf, mem_rootSet', map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at hx hy
    have : x ^ 3 = y ^ 3 := by rw [hx.2, hy.2]
    exact Odd.pow_injective (by decide) this
  -- Hence its Galois group is the full symmetric group on the 3 roots — non-abelian.
  have hbij : Function.Bijective (galActionHom f ℂ) := by
    apply galActionHom_bijective_of_prime_degree' hf_irr (by rw [hf_deg]; exact Nat.prime_three)
    · rw [hcardC]; omega
    · rw [hcardC]; omega
  let e := Fintype.equivFinOfCardEq hcardC
  let χ : f.Gal ≃* Equiv.Perm (Fin 3) :=
    (MulEquiv.ofBijective (galActionHom f ℂ) hbij).trans (Equiv.permCongrHom e)
  haveI : Fact ((f.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits) :=
    ⟨IsAlgClosed.splits (f.map _)⟩
  -- Assume commutative; the absolute Galois group surjects onto `f.Gal`, forcing it commutative.
  intro hcomm
  have hGalComm : ∀ a b : f.Gal, a * b = b * a := by
    intro a b
    obtain ⟨σ, rfl⟩ := restrict_surjective f (AlgebraicClosure ℚ) a
    obtain ⟨τ, rfl⟩ := restrict_surjective f (AlgebraicClosure ℚ) b
    rw [← map_mul, ← map_mul]
    exact congrArg _ (hcomm σ τ)
  -- But `f.Gal ≅ S₃` is non-abelian (`decide`), contradiction.
  obtain ⟨s, t, hst⟩ : ∃ s t : Equiv.Perm (Fin 3), s * t ≠ t * s := by decide
  exact hst (by have h := hGalComm (χ.symm s) (χ.symm t); simpa using congrArg χ h)

#print axioms rationals_absoluteGaloisGroup_not_commutative

end Anabelian
