/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.CyclicPair
import Mathlib

/-!
# L3.1: `q(ℤ) = n` — the fundamental computation (Pass 92)

The first nontrivial Herbrand-quotient value. For the trivial action (any `n`) the pair
degenerates — `N = (·)ⁿ`, `D = 1` — and:

* **`card_herbrandH_diff_norm`** (generic in `A`): `|Ĥ⁰| = [A : Aⁿ]` — the presentation
  `A ↠ Ĥ⁰` via the full kernel of `D`, read through the first isomorphism theorem;
* **`card_herbrandH_norm_diff_eq_one`** (generic): `Ĥ¹` is trivial on `n`-torsion-free
  `A`;
* **`cyclicHerbrandQuotient_int`**: **`q(ℤ) = n`** on the carrier `Multiplicative ℤ` —
  the index computation lands on Mathlib's `Int.index_zmultiples` through the
  `AddSubgroup.toSubgroup` bridge.

This is the computation the valuation exact sequence `1 → 𝒪ˣ → Lˣ → ℤ → 0` will pull
`q(Lˣ) = [L:K]` out of (with `q(𝒪ˣ) = 1`, the unit-filtration track) — the input to the
class-formation axioms of the Neukirch route.

Pass 94 extracts `multiplicative_int_pow_eq_one` and derives
`finite_herbrandH_norm_diff_int` from the cardinality-one result, so multiplicativity
can use the value-group finiteness without a supplied instance.

## Honesty

A concrete cohomology computation — **no reach toward R1–R3**, no class field theory
claimed. The generic lemmas' hypotheses (`n`-torsion-freeness) are visibly consumed; no
sharpness claimed, no witness owed. No new `structure`/`class`; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian


section TrivialAction

variable {A : Type*} [CommGroup A]

/-- The norm of the trivial action is the `n`-th power map. -/
theorem cyclicNorm_one_apply (n : ℕ) (x : A) :
    cyclicNorm (1 : MulAut A) n x = x ^ n := by
  rw [cyclicNorm_apply]
  have h1 : ∀ i ∈ Finset.range n, ((1 : MulAut A) ^ i) x = x := by
    intro i _
    rw [one_pow]
    rfl
  rw [Finset.prod_congr rfl h1, Finset.prod_const, Finset.card_range]

/-- The twisted difference of the trivial action is the trivial hom. -/
theorem cyclicDiff_one_apply (x : A) :
    cyclicDiff (1 : MulAut A) x = 1 := by
  rw [cyclicDiff_apply]
  have h1 : (1 : MulAut A) x = x := rfl
  rw [h1, mul_inv_cancel]

/-- `Ĥ¹` of the trivial action on an (`n`-)torsion-free group is trivial: the kernel of
the `n`-th power map is already trivial. -/
theorem card_herbrandH_norm_diff_eq_one (n : ℕ)
    (htf : ∀ x : A, x ^ n = 1 → x = 1) :
    Nat.card (herbrandH (cyclicNorm (1 : MulAut A) n)
      (cyclicDiff (1 : MulAut A))) = 1 := by
  have hsub : Subsingleton ((cyclicNorm (1 : MulAut A) n).ker) := by
    constructor
    intro a b
    apply Subtype.ext
    have ha : a.1 ^ n = 1 := by
      have h2 : cyclicNorm (1 : MulAut A) n a.1 = 1 := a.2
      rwa [cyclicNorm_one_apply] at h2
    have hb : b.1 ^ n = 1 := by
      have h2 : cyclicNorm (1 : MulAut A) n b.1 = 1 := b.2
      rwa [cyclicNorm_one_apply] at h2
    rw [htf a.1 ha, htf b.1 hb]
  have : Subsingleton (herbrandH (cyclicNorm (1 : MulAut A) n)
      (cyclicDiff (1 : MulAut A))) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with | _ a =>
    induction b using QuotientGroup.induction_on with | _ b =>
    rw [Subsingleton.elim a b]
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨1⟩⟩

/-- The inclusion `A → ker D` for the trivial difference (whose kernel is everything). -/
def diffKerIncl : A →* (cyclicDiff (1 : MulAut A)).ker where
  toFun x := ⟨x, by rw [MonoidHom.mem_ker, cyclicDiff_one_apply]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The presentation `A ↠ Ĥ⁰` of the trivial action: include into `ker D = A`, project.
Generic in `A` — the workhorse for computing `Ĥ⁰ = A/Aⁿ` cards. -/
noncomputable def diffKerProj (n : ℕ) :
    A →* herbrandH (cyclicDiff (1 : MulAut A))
      (cyclicNorm (1 : MulAut A) n) :=
  (QuotientGroup.mk' _).comp diffKerIncl

theorem diffKerProj_surjective (n : ℕ) :
    Function.Surjective (diffKerProj (A := A) n) := by
  intro c
  induction c using QuotientGroup.induction_on with | _ y =>
  refine ⟨y.1, ?_⟩
  have h1 : diffKerIncl (A := A) y.1 = y := Subtype.ext rfl
  change QuotientGroup.mk (diffKerIncl y.1) = QuotientGroup.mk y
  rw [h1]

theorem diffKerProj_ker (n : ℕ) :
    (diffKerProj (A := A) n).ker = (cyclicNorm (1 : MulAut A) n).range := by
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : diffKerProj (A := A) n x
      = QuotientGroup.mk (diffKerIncl x) := rfl
  rw [h1]
  exact ⟨fun h => Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h),
    fun h => (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)⟩

/-- **`|Ĥ⁰| = [A : Aⁿ]`** for the trivial action — the first isomorphism theorem reads
the cohomology card off the index of the power subgroup. -/
theorem card_herbrandH_diff_norm (n : ℕ) :
    Nat.card (herbrandH (cyclicDiff (1 : MulAut A))
        (cyclicNorm (1 : MulAut A) n))
      = (cyclicNorm (1 : MulAut A) n).range.index := by
  have e := QuotientGroup.quotientKerEquivOfSurjective _ (diffKerProj_surjective (A := A) n)
  rw [← Nat.card_congr e.toEquiv]
  rw [Subgroup.index]
  rw [diffKerProj_ker]

end TrivialAction

section IntComputation

/-- The range of the `n`-th power map on `Multiplicative ℤ` is (the multiplicative avatar
of) `nℤ`. -/
theorem range_cyclicNorm_int (n : ℕ) :
    (cyclicNorm (1 : MulAut (Multiplicative ℤ)) n).range
      = AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) := by
  ext x
  rw [Multiplicative.mem_toSubgroup, Int.mem_zmultiples_iff]
  constructor
  · rintro ⟨y, rfl⟩
    rw [cyclicNorm_one_apply]
    refine ⟨Multiplicative.toAdd y, ?_⟩
    have h1 : Multiplicative.toAdd (y ^ n) = n • Multiplicative.toAdd y := by
      simp
    rw [h1, nsmul_eq_mul]
  · rintro ⟨k, hk⟩
    refine ⟨Multiplicative.ofAdd k, ?_⟩
    rw [cyclicNorm_one_apply]
    apply Multiplicative.toAdd.injective
    have h2 : Multiplicative.toAdd ((Multiplicative.ofAdd k) ^ n)
        = n • k := by simp
    rw [h2, hk, nsmul_eq_mul]

/-- The infinite cyclic group has no nontrivial `n`-torsion when `n ≠ 0`. -/
theorem multiplicative_int_pow_eq_one (n : ℕ) (hn : n ≠ 0) :
    ∀ x : Multiplicative ℤ, x ^ n = 1 → x = 1 := by
  intro x hx
  have h2 : (n : ℤ) * Multiplicative.toAdd x = 0 := by
    have h3 : Multiplicative.toAdd (x ^ n) = n • Multiplicative.toAdd x := by simp
    rw [hx] at h3
    have h4 : Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 := rfl
    rw [h4] at h3
    rw [nsmul_eq_mul] at h3
    linarith [h3]
  have h5 : Multiplicative.toAdd x = 0 := by
    rcases mul_eq_zero.mp h2 with h6 | h6
    · exfalso
      exact hn (by exact_mod_cast h6)
    · exact h6
  apply Multiplicative.toAdd.injective
  exact h5

/-- `Ĥ¹` of the trivial cyclic action on `ℤ` is finite, derived from its card being one. -/
theorem finite_herbrandH_norm_diff_int (n : ℕ) (hn : n ≠ 0) :
    Finite (herbrandH (cyclicNorm (1 : MulAut (Multiplicative ℤ)) n)
      (cyclicDiff (1 : MulAut (Multiplicative ℤ)))) := by
  apply Nat.finite_of_card_ne_zero
  rw [card_herbrandH_norm_diff_eq_one n (multiplicative_int_pow_eq_one n hn)]
  exact one_ne_zero

/-- **`q(ℤ) = n`** (Serre VIII §4; the fundamental computation): the Herbrand quotient of
the trivial action of a cyclic group of order `n` on the infinite cyclic module is `n` —
`Ĥ⁰ = ℤ/nℤ` (card `n` via `Int.index_zmultiples`), `Ĥ¹ = 0` (torsion-freeness). The
prototype for `q(Lˣ) = [L:K]`: the valuation exact sequence will reduce `q(Lˣ)` to
exactly this computation plus `q(units) = 1`. -/
theorem cyclicHerbrandQuotient_int (n : ℕ) (hn : n ≠ 0) :
    cyclicHerbrandQuotient (1 : MulAut (Multiplicative ℤ)) n = n := by
  rw [cyclicHerbrandQuotient, herbrandQuotient]
  have h0 : Nat.card (herbrandH
      (cyclicDiff (1 : MulAut (Multiplicative ℤ)))
      (cyclicNorm (1 : MulAut (Multiplicative ℤ)) n)) = n := by
    rw [card_herbrandH_diff_norm, range_cyclicNorm_int, AddSubgroup.index_toSubgroup,
        Int.index_zmultiples, Int.natAbs_natCast]
  have h1 := card_herbrandH_norm_diff_eq_one (A := Multiplicative ℤ) n
    (multiplicative_int_pow_eq_one n hn)
  rw [h0, h1]
  norm_num

end IntComputation


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms cyclicNorm_one_apply
#print axioms card_herbrandH_norm_diff_eq_one
#print axioms card_herbrandH_diff_norm
#print axioms range_cyclicNorm_int
#print axioms multiplicative_int_pow_eq_one
#print axioms finite_herbrandH_norm_diff_int
#print axioms cyclicHerbrandQuotient_int

end Anabelian
