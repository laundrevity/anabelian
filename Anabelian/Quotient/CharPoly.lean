/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.Basic
import Anabelian.Quotient.Surjective
import Anabelian.Extension.Uniformizer
import Mathlib

/-!
# Toward Serre IV §1 Prop. 3: the subextension characteristic polynomial (Pass 55)

The sum formula `i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` (Serre IV §1 Prop. 3) — the last
wall before Lemma 5 — is proved by comparing `σ̄y − y` with `∏_{s ↦ σ̄} (sx − x)` through **one
polynomial**: `f(X) = ∏_{h ∈ H} (X − h·x)`, `H = Gal(L/K')`, whose coefficients lie in
`𝒪_{K'}` (they are `H`-fixed integers), so that `(σ̄f)(x) = ± ∏_{s ↦ σ̄}(sx − x)` and the
division `g(X) − y = f·q` can be pushed along `σ̄`. **This pass builds that polynomial and its
descent** — the substrate both divisibility directions of Prop. 3 run through.

Two remarks on the construction:

* Mathlib's `prodXSubSMul` is the product over the **orbit** (`G ⧸ stabilizer`); Prop. 3 needs
  the product over **all** of `H` — the lift-set product `∏_{s ↦ σ̄}` counts multiplicities.
  So `fullProdXSubSMul` (the `Finset.univ` product) is defined here, with the same four
  properties by the same techniques (monic, degree `|G|`, kills `x`, `G`-invariant
  coefficients). For a *generator* `x` the stabilizer is trivial and the two agree — but the
  full product is the right primitive.
* The coefficient descent is the fixed-points theorem: an `H`-fixed element of `𝒪_L` lies in
  `K'` (Galois, `IsGalois.mem_range_algebraMap_iff_fixed`) and is integral, hence lies in
  `𝒪_L ∩ K' = A.comap (algebraMap K' L)` — Pass 50's subring, with Pass 50's `comapRingHom`
  as the inclusion. Pass 52's `D(𝒪_L) = ⊤` (transported to the `K'`-level by Pass 46's
  `restrictScalars` compatibility) makes the abstract stability hypothesis vacuous at `𝒪_L`.

## What is proved (all axiom-free)

* `fullProdXSubSMul G R x = ∏ g : G, (X − C (g • x))` — monic (`fullProdXSubSMul_monic`),
  `natDegree = |G|` (`fullProdXSubSMul_natDegree`), kills `x` (`fullProdXSubSMul_eval`),
  `G`-invariant (`fullProdXSubSMul_smul`, hence `fullProdXSubSMul_coeff`).
* `exists_comapRingHom_eq_of_forall_smul_eq` — **the fixed-points descent**: an element of
  `𝒪_L` fixed by every `K'`-automorphism lies in the image of `A ∩ K'`.
* **`exists_fullProdXSubSMul_lift`** — the headline: under `D_{K'}(A) = ⊤`, Serre's polynomial
  descends — there is a **monic** `F` over `A ∩ K'` with
  `F.map (comapRingHom K' A) = fullProdXSubSMul` and the same degree.
* `decompositionSubgroup_extensionIntegers_restrict_eq_top` — `𝒪_L` is stable under
  `Gal(L/K')` for any intermediate `K'` of the tower (Pass 52's Galois-stability, transported
  by Pass 46's `restrictScalars_smul_valuationSubring`), i.e. `D_{K'}(𝒪_L) = ⊤`.
* `exists_fullProdXSubSMul_lift_extensionIntegers` — the instantiation at `A = 𝒪_L` over the
  subextension `K'`: the hypothesis is discharged; only the ambient Galois/finiteness
  instances remain.
* `extensionIntegers_comap_algebraMap` — the same-base identification `𝒪_L ∩ K = 𝒪_K` (as
  the canonical valuation subring of `K`), from Pass 35's
  `algebraMap_mem_extensionIntegers_iff`.

## Honesty

Substrate for Prop. 3 — **no reach toward R1–R3**; nothing recovered from an abstract group.
This pass proves no divisibility and no part of the sum formula: it constructs the polynomial
and its descent, complete and hypothesis-free at `𝒪_L`. The two divisibility directions
(`a ∣ b` via `σ̄f − f` coefficient-telescoping; `b ∣ a` via the monic division `g(X) − y =
f·q`) are the next bricks, deliberately unbuilt rather than half-built. No new
`structure`/`class` (`fullProdXSubSMul` is a `def` of a polynomial); no owed witness; D1 N/A;
D2 stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Polynomial
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

section FullProd

variable (G : Type*) [Group G] [Fintype G]
variable (R : Type*) [CommRing R] [MulSemiringAction G R]

/-- **The full product `∏_{g ∈ G} (X − g·x)`** — Serre's polynomial `f` (IV §1, the proof of
Prop. 3). Unlike Mathlib's `prodXSubSMul` (which ranges over the orbit `G ⧸ stabilizer`), this
ranges over all of `G` with multiplicity — the form whose `σ̄`-transport is the lift-set
product `∏_{s ↦ σ̄} (X − sx)`. -/
noncomputable def fullProdXSubSMul (x : R) : R[X] :=
  ∏ g : G, (Polynomial.X - Polynomial.C (g • x))

theorem fullProdXSubSMul_monic (x : R) : (fullProdXSubSMul G R x).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem fullProdXSubSMul_natDegree (x : R) [Nontrivial R] :
    (fullProdXSubSMul G R x).natDegree = Fintype.card G := by
  rw [fullProdXSubSMul,
      Polynomial.natDegree_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _]
  simp

theorem fullProdXSubSMul_eval (x : R) : (fullProdXSubSMul G R x).eval x = 0 := by
  rw [fullProdXSubSMul, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ (1 : G)) ?_
  simp

/-- The full product is `G`-invariant: acting by `g` permutes the factors (left translation). -/
theorem fullProdXSubSMul_smul (x : R) (g : G) :
    g • fullProdXSubSMul G R x = fullProdXSubSMul G R x := by
  rw [fullProdXSubSMul, Finset.smul_prod']
  have h1 : ∀ h : G, g • (Polynomial.X - Polynomial.C (h • x))
      = Polynomial.X - Polynomial.C ((g * h) • x) := by
    intro h
    rw [smul_sub, Polynomial.smul_X, Polynomial.smul_C, mul_smul]
  calc ∏ h : G, g • (Polynomial.X - Polynomial.C (h • x))
      = ∏ h : G, (Polynomial.X - Polynomial.C ((g * h) • x)) :=
        Finset.prod_congr rfl fun h _ => h1 h
    _ = ∏ h : G, (Polynomial.X - Polynomial.C (h • x)) :=
        Equiv.prod_comp (Equiv.mulLeft g) fun h => Polynomial.X - Polynomial.C (h • x)

/-- The coefficients of the full product are `G`-fixed. -/
theorem fullProdXSubSMul_coeff (x : R) (g : G) (n : ℕ) :
    g • (fullProdXSubSMul G R x).coeff n = (fullProdXSubSMul G R x).coeff n := by
  rw [← Polynomial.coeff_smul, fullProdXSubSMul_smul]

end FullProd

section Abstract

variable (K' : Type*) [Field K']
variable {L : Type*} [Field L] [Algebra K' L]
variable (A : ValuationSubring L)

/-- **The fixed-points descent**: an element of `A` fixed by every `K'`-automorphism of `L`
lies in `K'` (Galois fixed-points) and is integral there — i.e. it comes from `A ∩ K'` along
Pass 50's `comapRingHom`. The integral form of `L^{Gal(L/K')} = K'`. -/
theorem exists_comapRingHom_eq_of_forall_smul_eq [FiniteDimensional K' L] [IsGalois K' L]
    {a : ↥A} (ha : ∀ σ : L ≃ₐ[K'] L, σ (a : L) = (a : L)) :
    ∃ b : ↥(A.comap (algebraMap K' L)), comapRingHom K' A b = a := by
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed ((a : L))).mpr ha
  refine ⟨⟨b, ?_⟩, ?_⟩
  · rw [mem_comap, hb]; exact a.2
  · exact Subtype.ext hb

/-- **Serre's polynomial descends to the subextension** (the substrate of IV §1 Prop. 3):
if the whole `Gal(L/K')` decomposes at `A`, the `H`-fixed coefficients of
`∏_{h} (X − h·x)` come from `A ∩ K'` — there is a **monic** `F` over `A ∩ K'` with
`F.map (comapRingHom K' A) = fullProdXSubSMul` and the same degree. -/
theorem exists_fullProdXSubSMul_lift [Fintype (A.decompositionSubgroup K')]
    [FiniteDimensional K' L] [IsGalois K' L]
    (hD : A.decompositionSubgroup K' = ⊤) (x : ↥A) :
    ∃ F : Polynomial ↥(A.comap (algebraMap K' L)),
      F.map (comapRingHom K' A) = fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x
        ∧ F.Monic
        ∧ F.degree = (fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x).degree := by
  have hlift : fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x
      ∈ Polynomial.lifts (comapRingHom K' A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have hfix : ∀ σ : L ≃ₐ[K'] L,
        σ (((fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x).coeff n : L))
          = ((fullProdXSubSMul (A.decompositionSubgroup K') (↥A) x).coeff n : L) := by
      intro σ
      have hσD : σ ∈ A.decompositionSubgroup K' := by
        rw [hD]; exact Subgroup.mem_top σ
      exact congrArg Subtype.val
        (fullProdXSubSMul_coeff (A.decompositionSubgroup K') (↥A) x ⟨σ, hσD⟩ n)
    obtain ⟨b, hb⟩ := exists_comapRingHom_eq_of_forall_smul_eq K' A hfix
    exact ⟨b, hb⟩
  obtain ⟨F, hmap, hdeg, hmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlift
      (fullProdXSubSMul_monic (A.decompositionSubgroup K') (↥A) x)
  exact ⟨F, hmap, hmonic, hdeg⟩

end Abstract

section Tower

variable (K K' : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L]

/-- **`𝒪_L` is stable under `Gal(L/K')` for any intermediate field `K'`**: a
`K'`-automorphism is in particular a `K`-automorphism (Pass 46's `restrictScalars`
compatibility), and those stabilize the integral closure (Pass 52). So `D_{K'}(𝒪_L) = ⊤`. -/
theorem decompositionSubgroup_extensionIntegers_restrict_eq_top :
    (extensionIntegers K L).decompositionSubgroup K' = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [MulAction.mem_stabilizer_iff,
      ← restrictScalars_smul_valuationSubring K K' (extensionIntegers K L) σ]
  exact smul_extensionIntegers K L (σ.restrictScalars K)

/-- Serre's polynomial at `𝒪_L` over the subextension `K'`, hypothesis-free: the monic `F`
over `𝒪_L ∩ K'` with `F.map (comapRingHom) = ∏_{h ∈ Gal(L/K')} (X − h·x)`. -/
theorem exists_fullProdXSubSMul_lift_extensionIntegers
    [Fintype ((extensionIntegers K L).decompositionSubgroup K')]
    [FiniteDimensional K' L] [IsGalois K' L] (x : ↥(extensionIntegers K L)) :
    ∃ F : Polynomial ↥((extensionIntegers K L).comap (algebraMap K' L)),
      F.map (comapRingHom K' (extensionIntegers K L))
          = fullProdXSubSMul ((extensionIntegers K L).decompositionSubgroup K')
              (↥(extensionIntegers K L)) x
        ∧ F.Monic
        ∧ F.degree = (fullProdXSubSMul ((extensionIntegers K L).decompositionSubgroup K')
              (↥(extensionIntegers K L)) x).degree :=
  exists_fullProdXSubSMul_lift K' (extensionIntegers K L)
    (decompositionSubgroup_extensionIntegers_restrict_eq_top K K') x

end Tower

section SameBase

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The same-base identification **`𝒪_L ∩ K = 𝒪_K`** (as the canonical valuation subring of
`K`): comapping the integral closure along `K → L` recovers the integers of `K` — Pass 35's
integrally-closedness statement, packaged at the `ValuationSubring` level for the coming
Prop.-3 bookkeeping. -/
theorem extensionIntegers_comap_algebraMap :
    (extensionIntegers K L).comap (algebraMap K L)
      = (ValuativeRel.valuation K).valuationSubring := by
  refine SetLike.ext fun c => ?_
  rw [mem_comap, Valuation.mem_valuationSubring_iff,
      algebraMap_mem_extensionIntegers_iff K L c]
  exact Valuation.mem_integer_iff _ c

end SameBase

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms fullProdXSubSMul
#print axioms fullProdXSubSMul_monic
#print axioms fullProdXSubSMul_natDegree
#print axioms fullProdXSubSMul_eval
#print axioms fullProdXSubSMul_smul
#print axioms fullProdXSubSMul_coeff
#print axioms exists_comapRingHom_eq_of_forall_smul_eq
#print axioms exists_fullProdXSubSMul_lift
#print axioms decompositionSubgroup_extensionIntegers_restrict_eq_top
#print axioms exists_fullProdXSubSMul_lift_extensionIntegers
#print axioms extensionIntegers_comap_algebraMap

end Anabelian
