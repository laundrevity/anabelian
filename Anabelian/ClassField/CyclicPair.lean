/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.Multiplicativity
import Mathlib

/-!
# L3.1: the cyclic pair — `q(σ, A)` instantiated for Galois modules (Pass 91)

The concrete computations begin. For an automorphism `σ` of a commutative group `A` with
`σ ^ n = 1` (the cyclic Galois action; the target case: a generator of `Gal(L/K)` acting
on `Lˣ`):

* **`cyclicNorm σ n`** — the norm `N(x) = ∏_{i<n} σⁱ(x)` (the field norm, on units);
* **`cyclicDiff σ`** — the twisted difference `D(x) = σ(x)·x⁻¹` (the multiplicative
  `σ − 1`);
* the **complex conditions** `D∘N = 1` (`cyclicDiff_cyclicNorm` — norms are fixed, by the
  index-shift lemma `sigma_cyclicNorm`) and `N∘D = 1` (`cyclicNorm_cyclicDiff` —
  telescoping);
* **`cyclicHerbrandQuotient σ n := herbrandQuotient (cyclicDiff σ) (cyclicNorm σ n)`** —
  the `(diff, norm)` ORDER is the convention that makes this `|Ĥ⁰|/|Ĥ¹|` with
  `Ĥ⁰ = A^σ/N(A)`, pinned here once for all downstream computations;
* a sanity computation (`q = 1` for the trivial order-1 action).

With Pass 87 (triviality) and Pass 90 (multiplicativity) this arms the cyclic layer's
standard computations: next are `q(ℤ) = n` (trivial action) and the `q(Lˣ) = [L:K]` track
through the valuation exact sequence and the unit filtration.

## Honesty

The instantiation layer for Galois modules — **no reach toward R1–R3**, no class field
theory claimed. Rule-2 note: the `σ ^ n = 1` hypothesis is load-bearing in the two
complex-condition theorems and is USED in both proofs (the index-shift cycle closure);
no sharpness claim is made, so no witness is owed. No new `structure`/`class`; D1 N/A;
D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian


variable {A : Type*} [CommGroup A]

/-- **The norm of a cyclic action**: `N(x) = ∏_{i<n} σⁱ(x)` — for `σ` a generator of
`Gal(L/K)` acting on `Lˣ`, this is the field norm on units. A `MonoidHom` by
commutativity of `A`. -/
noncomputable def cyclicNorm (σ : MulAut A) (n : ℕ) : A →* A where
  toFun x := ∏ i ∈ Finset.range n, (σ ^ i) x
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [Finset.prod_mul_distrib]

/-- **The twisted difference** `D(x) = σ(x)·x⁻¹` — the multiplicative "σ − 1". Its kernel
is the fixed subgroup `A^σ`; its image is the augmentation part. -/
def cyclicDiff (σ : MulAut A) : A →* A where
  toFun x := σ x * x⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv_rev, mul_comm, mul_assoc, mul_left_comm]

theorem cyclicNorm_apply (σ : MulAut A) (n : ℕ) (x : A) :
    cyclicNorm σ n x = ∏ i ∈ Finset.range n, (σ ^ i) x := rfl

theorem cyclicDiff_apply (σ : MulAut A) (x : A) :
    cyclicDiff σ x = σ x * x⁻¹ := rfl

/-- `σ` fixes every norm: `σ(N x) = N x` — the index shift `i ↦ i+1` permutes the factors
(`σ^n = 1` closes the cycle). -/
theorem sigma_cyclicNorm (σ : MulAut A) (n : ℕ) (hσ : σ ^ n = 1) (x : A) :
    σ (cyclicNorm σ n x) = cyclicNorm σ n x := by
  rw [cyclicNorm_apply σ n x, map_prod]
  have h1 : ∀ i, σ ((σ ^ i) x) = (σ ^ (i + 1)) x := by
    intro i
    rw [pow_succ']
    rfl
  simp only [h1]
  have h2 := Finset.prod_range_succ' (fun i => (σ ^ i) x) n
  have h3 := Finset.prod_range_succ (fun i => (σ ^ i) x) n
  have h4 : (σ ^ n) x = (σ ^ 0) x := by rw [hσ, pow_zero]
  have h5 : (∏ i ∈ Finset.range n, (σ ^ (i + 1)) x) * (σ ^ 0) x
      = (∏ i ∈ Finset.range n, (σ ^ i) x) * (σ ^ n) x := by
    rw [← h2, ← h3]
  rw [h4] at h5
  exact mul_right_cancel h5

/-- The complex condition `D ∘ N = 1`: norms are `σ`-fixed. -/
theorem cyclicDiff_cyclicNorm (σ : MulAut A) (n : ℕ) (hσ : σ ^ n = 1) (x : A) :
    cyclicDiff σ (cyclicNorm σ n x) = 1 := by
  rw [cyclicDiff_apply, sigma_cyclicNorm σ n hσ, mul_inv_cancel]

/-- The complex condition `N ∘ D = 1`: the norm of a twisted difference telescopes. -/
theorem cyclicNorm_cyclicDiff (σ : MulAut A) (n : ℕ) (hσ : σ ^ n = 1) (x : A) :
    cyclicNorm σ n (cyclicDiff σ x) = 1 := by
  rw [cyclicDiff_apply, map_mul, map_inv]
  -- N(σx) · N(x)⁻¹ = 1 since N(σx) = N(x) (same index-shift argument)
  have h1 : cyclicNorm σ n (σ x) = cyclicNorm σ n x := by
    rw [cyclicNorm_apply σ n (σ x), cyclicNorm_apply σ n x]
    have h2 : ∀ i : ℕ, (σ ^ i) (σ x) = (σ ^ (i + 1)) x := by
      intro i
      rw [pow_succ]
      rfl
    simp only [h2]
    have h3 := Finset.prod_range_succ' (fun i => (σ ^ i) x) n
    have h4 := Finset.prod_range_succ (fun i => (σ ^ i) x) n
    have h5 : (σ ^ n) x = (σ ^ 0) x := by rw [hσ, pow_zero]
    have h6 : (∏ i ∈ Finset.range n, (σ ^ (i + 1)) x) * (σ ^ 0) x
        = (∏ i ∈ Finset.range n, (σ ^ i) x) * (σ ^ n) x := by
      rw [← h3, ← h4]
    rw [h5] at h6
    exact mul_right_cancel h6
  rw [h1, mul_inv_cancel]

/-- **The Herbrand quotient of a cyclic action**: `q(σ, A) = |Ĥ⁰|/|Ĥ¹|` where
`Ĥ⁰ = A^σ/N(A) = ker D / im N` and `Ĥ¹ = ker N / im D` — hence the `(diff, norm)`
argument order into Pass 87's `herbrandQuotient` (CONVENTION: pinned here once; every
downstream computation uses it). Passes 87/90 supply the calculus: `q = 1` on finite
modules, `q(M) = q(M')·q(M'')` along equivariant short exact sequences. -/
noncomputable def cyclicHerbrandQuotient (σ : MulAut A) (n : ℕ) : ℚ :=
  herbrandQuotient (cyclicDiff σ) (cyclicNorm σ n)

/-- Sanity computation: the trivial action of order 1 has `q = 1` (`N = id`, `D = 1`;
both cohomologies collapse). -/
example : cyclicHerbrandQuotient (1 : MulAut A) 1 = 1 := by
  have hN : cyclicNorm (1 : MulAut A) 1 = MonoidHom.id A := by
    ext x
    rw [cyclicNorm_apply]
    simp
  have hD : cyclicDiff (1 : MulAut A) = 1 := by
    ext x
    rw [cyclicDiff_apply]
    simp
  rw [cyclicHerbrandQuotient, herbrandQuotient, hN, hD]
  -- Ĥ⁰ = ker 1 / im id = ⊤/⊤; Ĥ¹ = ker id / im 1 = ⊥/⊥ — both trivial
  have h1 : Nat.card (herbrandH (1 : A →* A) (MonoidHom.id A)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      intro a b
      induction a using QuotientGroup.induction_on with | _ a =>
      induction b using QuotientGroup.induction_on with | _ b =>
      refine (QuotientGroup.eq).mpr (Subgroup.mem_subgroupOf.mpr ⟨(a : A)⁻¹ * b, ?_⟩)
      rfl
    · exact ⟨1⟩
  have h2 : Nat.card (herbrandH (MonoidHom.id A) (1 : A →* A)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · constructor
      intro a b
      induction a using QuotientGroup.induction_on with | _ a =>
      induction b using QuotientGroup.induction_on with | _ b =>
      have ha : (a : A) = 1 := a.2
      have hb : (b : A) = 1 := b.2
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      rw [hab]
    · exact ⟨1⟩
  rw [h1, h2]
  norm_num


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms cyclicNorm
#print axioms cyclicDiff
#print axioms sigma_cyclicNorm
#print axioms cyclicDiff_cyclicNorm
#print axioms cyclicNorm_cyclicDiff
#print axioms cyclicHerbrandQuotient

end Anabelian
