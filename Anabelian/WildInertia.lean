/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.AdditiveCharacter

/-!
# Rung L2: wild inertia — `G₁` is pro-`p` (finite-level form: a `p`-group) (Pass 28)

The capstone of the Passes 23–27 finite-level arc (Serre, *Local Fields*, IV §2, corollaries to
Props. 7/9). Let `𝓀` be the residue field, `char 𝓀 = p`. The two character embeddings built in
Passes 24/25/27 have opposite torsion behavior in characteristic `p`:

* `𝓀⁺` has **exponent `p`**, so the additive embeddings force `(G_i/G_{i+1})^p = 1` for `i ≥ 1`;
* `𝓀ˣ` has **no `p`-torsion** (Frobenius is injective), so the tame embedding forces `G₀/G₁` to
  have none either.

Chaining the first through the eventually-trivial filtration (Pass 24's
`exists_ramificationGroup_eq_bot`) gives the headline:

> **`G₁` is a `p`-group** (`IsPGroup p G₁`) — every element has `p`-power order — while
> **`p ∤ |G₀/G₁|`** (Cauchy). At finite level, `G₁` is the wild inertia: the normal Sylow
> `p`-subgroup of the inertia group.

## What is proved (all axiom-free)

* `additiveQuotient_pow_eq_one` — `x^p = 1` on `G_i/G_{i+1}` (`i ≥ 1`; `char 𝓀 = p`;
  monogenicity): the additive embedding + `p • c = 0` in `𝓀`.
* `pow_mem_ramificationGroup_succ` — `σ ∈ G_i ⟹ σ^p ∈ G_{i+1}` (`i ≥ 1`).
* `pow_pow_mem_ramificationGroup` — `σ ∈ G₁ ⟹ σ^(p^k) ∈ G_{1+k}` (induction).
* **`isPGroup_ramificationGroup_one`** — `IsPGroup p G₁` (finite decomposition group +
  separation + monogenicity + `char 𝓀 = p`). Note `p` need not be *assumed* prime for this.
* `tameQuotient_pow_prime_eq_one_imp` — on `G₀/G₁`, `y^p = 1 ⟹ y = 1` (`p` prime,
  `char 𝓀 = p`): the tame embedding + injectivity of Frobenius.
* **`not_dvd_natCard_tameQuotient`** — `p ∤ |G₀/G₁|` (Cauchy's theorem, contrapositive).

Together: at finite level the inertia group `G₀` is `p`-by-`p'` — `G₁` is its normal Sylow
`p`-subgroup, the **wild inertia**, and the tame quotient `G₀/G₁ ↪ 𝓀ˣ` is its `p'`-complement
witness. (The pro-`p` statement for the *absolute* group is upper-numbering/limit territory —
named, not attempted.)

## Honesty

The hypotheses are exactly the Pass-25/27 stack (uniformizer package, monogenicity — named, not
claimed irremovable) plus `[CharP (ResidueField ↥A) p]` and, where genuinely needed (the tame
side and Cauchy), `[Fact p.Prime]`; finiteness + separation only where the statement consumes
them (the `IsPGroup` chain and Cauchy). NOT attempted: packaging `G₁` as a Mathlib `Sylow p`
term (routine on top of these two results — named); the pro-`p` limit statement (needs upper
numbering); the local-field instantiation (`char 𝓀 = p` then holds automatically). No new
`structure`/`class`; no owed witness (the `1 ≤ i` dichotomy was already witnessed in Pass 27);
D1 N/A; D2 N/A (`ValuationSubring`-native). Recovers nothing from an abstract group; R1–R3
untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open scoped Pointwise

namespace Anabelian

open ValuationSubring IsLocalRing

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}
  {A₀ : Subring ↥A} (p : ℕ)

/-! ### Exponent `p` on the higher quotients -/

/-- In residue characteristic `p`, the higher quotients `G_i/G_{i+1}` (`i ≥ 1`) have
**exponent `p`**: they embed in `𝓀⁺` (Pass 27), and `p • c = 0` there. -/
theorem additiveQuotient_pow_eq_one [CharP (ResidueField ↥A) p]
    (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    {i : ℕ} (hi : 1 ≤ i)
    (hfix : ∀ σ : ↥(ramificationGroup K A i), ∀ a ∈ A₀, σ.1 • a = a)
    (x : ↥(ramificationGroup K A i) ⧸
      ((ramificationGroup K A (i + 1)).subgroupOf (ramificationGroup K A i))) :
    x ^ p = 1 := by
  apply additiveQuotientHom_injective K π hspan hπ0 hgen hi hfix
  rw [map_pow, map_one]
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero (ResidueField ↥A) p, zero_mul]

/-- `σ ∈ G_i ⟹ σ^p ∈ G_{i+1}` (`i ≥ 1`, `char 𝓀 = p`, monogenicity). -/
theorem pow_mem_ramificationGroup_succ [CharP (ResidueField ↥A) p]
    (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    {i : ℕ} (hi : 1 ≤ i)
    (hfix : ∀ σ : ↥(ramificationGroup K A i), ∀ a ∈ A₀, σ.1 • a = a)
    {σ : A.decompositionSubgroup K} (hσ : σ ∈ ramificationGroup K A i) :
    σ ^ p ∈ ramificationGroup K A (i + 1) := by
  have hx : (QuotientGroup.mk' ((ramificationGroup K A (i + 1)).subgroupOf
        (ramificationGroup K A i)) (⟨σ, hσ⟩ : ↥(ramificationGroup K A i))) ^ p = 1 :=
    additiveQuotient_pow_eq_one K p π hspan hπ0 hgen hi hfix _
  rw [← map_pow] at hx
  have h1 : ((⟨σ, hσ⟩ : ↥(ramificationGroup K A i)) ^ p) ∈
      (ramificationGroup K A (i + 1)).subgroupOf (ramificationGroup K A i) :=
    (QuotientGroup.eq_one_iff _).mp hx
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

/-- `σ ∈ G₁ ⟹ σ^(p^k) ∈ G_{1+k}`: iterating `pow_mem_ramificationGroup_succ` climbs the
filtration. The fixed-ring hypothesis is taken once, over `G₀`, and restricted via
antitonicity. -/
theorem pow_pow_mem_ramificationGroup [CharP (ResidueField ↥A) p]
    (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    (hfix : ∀ σ : ↥(ramificationGroup K A 0), ∀ a ∈ A₀, σ.1 • a = a)
    {σ : A.decompositionSubgroup K} (hσ : σ ∈ ramificationGroup K A 1) (k : ℕ) :
    σ ^ p ^ k ∈ ramificationGroup K A (1 + k) := by
  induction k with
  | zero => simpa using hσ
  | succ k ih =>
    have hfixi : ∀ τ : ↥(ramificationGroup K A (1 + k)), ∀ a ∈ A₀, τ.1 • a = a :=
      fun τ => hfix ⟨τ.1, ramificationGroup_antitone K A (Nat.zero_le (1 + k)) τ.2⟩
    have h2 := pow_mem_ramificationGroup_succ K p π hspan hπ0 hgen
      (Nat.le_add_right 1 k) hfixi ih
    rw [← pow_mul, ← pow_succ] at h2
    exact h2

/-- **Wild inertia is a `p`-group** (finite level): for a finite decomposition group with
separating filtration, residue characteristic `p`, and the monogenicity package, every element
of `G₁` has `p`-power order. (`p` is not even assumed prime here.) -/
theorem isPGroup_ramificationGroup_one [CharP (ResidueField ↥A) p]
    [Finite ↥(A.decompositionSubgroup K)]
    (hsep : (⨅ n : ℕ, maximalIdeal ↥A ^ n) = ⊥)
    (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    (hfix : ∀ σ : ↥(ramificationGroup K A 0), ∀ a ∈ A₀, σ.1 • a = a) :
    IsPGroup p ↥(ramificationGroup K A 1) := by
  intro σ
  obtain ⟨n, hn⟩ := exists_ramificationGroup_eq_bot K A hsep
  refine ⟨n, ?_⟩
  have h1 := pow_pow_mem_ramificationGroup K p π hspan hπ0 hgen hfix σ.2 n
  have h2 : (σ.1 : A.decompositionSubgroup K) ^ p ^ n ∈ ramificationGroup K A n :=
    ramificationGroup_antitone K A (Nat.le_add_left n 1) h1
  rw [hn, Subgroup.mem_bot] at h2
  apply Subtype.ext
  simpa using h2

/-! ### The tame quotient has no `p`-torsion -/

/-- On the tame quotient `G₀/G₁`, `y^p = 1 ⟹ y = 1` (`p` prime, `char 𝓀 = p`, monogenicity):
the tame embedding lands in `𝓀ˣ`, where Frobenius injectivity kills `p`-torsion. -/
theorem tameQuotient_pow_prime_eq_one_imp [Fact p.Prime] [CharP (ResidueField ↥A) p]
    (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    (hfix : ∀ σ : ↥(ramificationGroup K A 0), ∀ a ∈ A₀, σ.1 • a = a)
    {y : ↥(ramificationGroup K A 0) ⧸
      ((ramificationGroup K A 1).subgroupOf (ramificationGroup K A 0))}
    (hy : y ^ p = 1) : y = 1 := by
  apply tameQuotientHom_injective K π hspan hπ0 hgen hfix
  rw [map_one]
  have h1 : (tameQuotientHom K π hspan hπ0 y) ^ p = 1 := by
    rw [← map_pow, hy, map_one]
  have h2 := congrArg Units.val h1
  rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have h3 : frobenius (ResidueField ↥A) p (↑(tameQuotientHom K π hspan hπ0 y)) =
      frobenius (ResidueField ↥A) p 1 := by
    rw [frobenius_def, frobenius_def, one_pow, h2]
  exact Units.ext (by rw [frobenius_inj (ResidueField ↥A) p h3, Units.val_one])

/-- **`p` does not divide the order of the tame quotient** (Cauchy's theorem, contrapositive):
an element of order `p` in `G₀/G₁` would contradict the absence of `p`-torsion. With
`isPGroup_ramificationGroup_one`, this exhibits `G₁` as the normal Sylow `p`-subgroup of `G₀`
at finite level — the wild inertia. -/
theorem not_dvd_natCard_tameQuotient [Fact p.Prime] [CharP (ResidueField ↥A) p]
    [Finite ↥(A.decompositionSubgroup K)]
    (π : ↥A) (hspan : maximalIdeal ↥A = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hgen : Subring.closure ((A₀ : Set ↥A) ∪ {π}) = ⊤)
    (hfix : ∀ σ : ↥(ramificationGroup K A 0), ∀ a ∈ A₀, σ.1 • a = a) :
    ¬ p ∣ Nat.card (↥(ramificationGroup K A 0) ⧸
      ((ramificationGroup K A 1).subgroupOf (ramificationGroup K A 0))) := by
  intro hdvd
  cases nonempty_fintype (↥(ramificationGroup K A 0) ⧸
    ((ramificationGroup K A 1).subgroupOf (ramificationGroup K A 0)))
  rw [Nat.card_eq_fintype_card] at hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card p hdvd
  have h1 : y ^ p = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have h2 := tameQuotient_pow_prime_eq_one_imp K p π hspan hπ0 hgen hfix h1
  rw [h2, orderOf_one] at hy
  exact (Fact.out : p.Prime).one_lt.ne' hy.symm

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms additiveQuotient_pow_eq_one
#print axioms pow_mem_ramificationGroup_succ
#print axioms pow_pow_mem_ramificationGroup
#print axioms isPGroup_ramificationGroup_one
#print axioms tameQuotient_pow_prime_eq_one_imp
#print axioms not_dvd_natCard_tameQuotient

end Anabelian
