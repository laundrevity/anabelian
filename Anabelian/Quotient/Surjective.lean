/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.Basic
import Anabelian.Extension.Integers
import Mathlib

/-!
# The ascent: surjectivity of the quotient restriction — `D(𝒪_L) ↠ D(𝒪_L ∩ K')` (Pass 52)

Pass 50 built the quotient-restriction skeleton and named its two missing arithmetic pieces;
this pass discharges one of them: **surjectivity of `decompositionQuotient`** — every element of
the subextension's decomposition group lifts. This is on the critical path to Serre IV §1
Prop. 3 (the sum `i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` ranges over the lifts of `σ̄`,
which must exist) and gives, with Pass 50's exactness, the **first-isomorphism description of
the quotient**: `D(A) ⧸ H ≃* D(A ∩ K')` — the `(G/H)` object of Herbrand's theorem, realized.

The route: Mathlib's `AlgEquiv.restrictNormalHom_surjective` lifts any `τ̄ ∈ Gal(K'/K)` through
`Gal(L/K)` when `L/K` is normal; what remains is to land the lift **inside the decomposition
group**. At the canonical valuation subring this is free — and for a structural reason worth
isolating: **`𝒪_L` (Pass 29's `extensionIntegers K L`) is the integral closure of `𝒪_K` in
`L`, and integral closure is Galois-stable**, so `D(𝒪_L) = ⊤` and *every* automorphism is
decomposed. (Serre works over complete local fields precisely so that the valuation is unique
and the decomposition group is everything — IV §1; this is that fact, in integral-closure
form.)

## What is proved (all axiom-free)

* `smul_extensionIntegers` — `σ • 𝒪_L = 𝒪_L` for every `σ ∈ Gal(L/K)`: membership is
  `IsIntegral 𝒪_K` (Pass 29, definitionally), and integrality transfers along the
  `𝒪_K`-algebra map `σ` (`IsIntegral.map`).
* **`decompositionSubgroup_extensionIntegers_eq_top`** — `D(𝒪_L) = ⊤`: the whole Galois group
  decomposes at the canonical valuation subring.
* **`decompositionQuotient_surjective`** — abstract form: if every `σ ∈ Gal(L/K)` stabilizes
  `A` and `L/K`, `K'/K` are normal, then `decompositionQuotient K K' A` is surjective (lift by
  `restrictNormalHom_surjective`; the stability hypothesis puts the lift in `D(A)`). Stability
  is a *sufficient* condition, discharged below at `A = 𝒪_L`; no necessity claim is made.
* `decompositionRestrict_range_normal` — `H = range (decompositionRestrict)` is **normal** in
  `D(A)` (it is a kernel, by Pass 50's exactness) — the hypothesis `(G/H)` needs to be a group.
* **`decompositionQuotientEquiv`** — the first-isomorphism packaging:
  `D(A) ⧸ range (decompositionRestrict) ≃* D(A ∩ K')` (Pass 50 exactness + surjectivity +
  `QuotientGroup.quotientKerEquivOfSurjective`). Instantiated at `𝒪_L`
  (`decompositionQuotient_extensionIntegers_surjective`,
  `decompositionQuotientEquiv_extensionIntegers`): **`Gal(K'/K)`'s decomposition data is the
  quotient `G/H` of `Gal(L/K)`'s** — the object Herbrand's theorem
  `(G/H)^v = G^v H/H` is about, now available as a quotient.

## Honesty

Group-theoretic structure of a tower of given fields — **no reach toward R1–R3**; nothing
recovered from an abstract group. One of Pass 50's two named gaps (surjectivity) is now a
theorem; the other — the higher-`i` image, i.e. Lemma 5's `i_{K'/K}` vs `i_{L/K}` arithmetic
(Serre IV §1 Prop. 3) — remains the wall, untouched here. No new `structure`/`class`
(`decompositionQuotientEquiv` is a `def` of a `MulEquiv`); the stability hypothesis of the
abstract surjectivity is discharged at the instantiation (sufficient, not claimed necessary);
no owed witness. D1 N/A; D2 (the spectral bridge) stays inside Pass 29's proof — this file only
uses `extensionIntegers` through its `IsIntegral` membership, and every `#print axioms` below
is standard-only.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

section Abstract

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [Normal K K']
variable (A : ValuationSubring L)

/-- **Surjectivity of the quotient restriction** (abstract form): if every `K`-automorphism of
`L` stabilizes `A` (true at `A = 𝒪_L` — `smul_extensionIntegers` below) and `L/K`, `K'/K` are
normal, then `decompositionQuotient K K' A` is surjective: lift `τ̄ ∈ D(A ∩ K')` through
`Gal(L/K)` (`AlgEquiv.restrictNormalHom_surjective`); stability lands the lift in `D(A)`. -/
theorem decompositionQuotient_surjective [Normal K L]
    (hA : ∀ σ : L ≃ₐ[K] L, σ • A = A) :
    Function.Surjective (decompositionQuotient K K' A) := by
  intro τ
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (E := L) (K₁ := K') τ.1
  exact ⟨⟨σ, MulAction.mem_stabilizer_iff.mpr (hA σ)⟩, Subtype.ext hσ⟩

/-- `H = Gal(L/K') ∩ D(A)` (as `range (decompositionRestrict)`) is **normal** in `D(A)`: by
Pass 50's exactness it is a kernel. The hypothesis under which `G/H` is a group. -/
theorem decompositionRestrict_range_normal :
    (decompositionRestrict K K' A).range.Normal := by
  rw [← decompositionQuotient_ker]
  infer_instance

/-- **The first-isomorphism packaging of the quotient theory**:
`D(A) ⧸ H ≃* D(A ∩ K')` where `H = range (decompositionRestrict)` — Pass 50's exactness
(`ker = range`) + surjectivity + the first isomorphism theorem. The `(G/H)` of Herbrand's
theorem `(G/H)^v = G^v H/H`, realized as an honest quotient of the ambient decomposition
group. -/
noncomputable def decompositionQuotientEquiv [Normal K L]
    (hA : ∀ σ : L ≃ₐ[K] L, σ • A = A) :
    letI := decompositionRestrict_range_normal K K' A
    A.decompositionSubgroup K ⧸ (decompositionRestrict K K' A).range
      ≃* (A.comap (algebraMap K' L)).decompositionSubgroup K := by
  letI := decompositionRestrict_range_normal K K' A
  exact (QuotientGroup.quotientMulEquivOfEq (decompositionQuotient_ker K K' A).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (decompositionQuotient_surjective K K' A hA))

end Abstract

section Integers

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **`𝒪_L` is Galois-stable**: `σ • 𝒪_L = 𝒪_L` for every `σ ∈ Gal(L/K)`. Membership in
`extensionIntegers K L` is integrality over `𝒪_K` (Pass 29, `Iff.rfl`), and integrality
transfers along the `𝒪_K`-algebra map `σ` (`IsIntegral.map`, both ways via `σ⁻¹`). The
integral-closure form of "the valuation of a complete field extends uniquely" (Serre IV §1). -/
theorem smul_extensionIntegers (σ : L ≃ₐ[K] L) :
    σ • extensionIntegers K L = extensionIntegers K L := by
  have key : ∀ (τ : L ≃ₐ[K] L) (x : L), IsIntegral ↥𝒪[K] x → IsIntegral ↥𝒪[K] (τ x) :=
    fun τ x hx => IsIntegral.map (τ.restrictScalars ↥𝒪[K]).toAlgHom hx
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      mem_extensionIntegers_iff, mem_extensionIntegers_iff]
  constructor
  · intro h
    have h2 := key σ _ h
    simpa using h2
  · intro h
    exact key σ⁻¹ x h

/-- **The whole Galois group decomposes at `𝒪_L`**: `D(𝒪_L) = ⊤`. The reason Serre can treat
`Gal(L/K)` itself as "the" decomposition group in the complete local setting. -/
theorem decompositionSubgroup_extensionIntegers_eq_top :
    (extensionIntegers K L).decompositionSubgroup K = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  exact MulAction.mem_stabilizer_iff.mpr (smul_extensionIntegers K L σ)

end Integers

section Instantiate

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Normal K K'] [Normal K L]

/-- Surjectivity at the canonical valuation subring: `D(𝒪_L) ↠ D(𝒪_L ∩ K')` for a Galois
tower over a nonarchimedean local field. The lifts Serre IV §1 Prop. 3 sums over exist. -/
theorem decompositionQuotient_extensionIntegers_surjective :
    Function.Surjective (decompositionQuotient K K' (extensionIntegers K L)) :=
  decompositionQuotient_surjective K K' _ (smul_extensionIntegers K L)

/-- The first-isomorphism description at `𝒪_L`:
`D(𝒪_L) ⧸ H ≃* D(𝒪_L ∩ K')` — the subextension's decomposition data **is** the quotient
`G/H`. -/
noncomputable def decompositionQuotientEquiv_extensionIntegers :
    letI := decompositionRestrict_range_normal K K' (extensionIntegers K L)
    (extensionIntegers K L).decompositionSubgroup K
        ⧸ (decompositionRestrict K K' (extensionIntegers K L)).range
      ≃* ((extensionIntegers K L).comap (algebraMap K' L)).decompositionSubgroup K :=
  decompositionQuotientEquiv K K' _ (smul_extensionIntegers K L)

end Instantiate

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms decompositionQuotient_surjective
#print axioms decompositionRestrict_range_normal
#print axioms decompositionQuotientEquiv
#print axioms smul_extensionIntegers
#print axioms decompositionSubgroup_extensionIntegers_eq_top
#print axioms decompositionQuotient_extensionIntegers_surjective
#print axioms decompositionQuotientEquiv_extensionIntegers

end Anabelian
