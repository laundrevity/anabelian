/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.RamificationMinpolyBound
import Anabelian.RamificationLiftDvd
import Mathlib

/-!
# Serre IV §1 Prop. 3, direction (ii): `b ∣ a` (Pass 62)

The second divisibility of Prop. 3 is now a theorem: for **every** `y ∈ B = 𝒪_L ∩ K'` and
every `s₀`,

> **`∏_{s ↦ σ̄} (x − s·x)` divides `ι(σ̄y − y)` in `𝒪_L`** (`liftProd_dvd_comapRingHom_smul_sub`).

Serre's division argument, with every step a named brick: represent `ι y = g(x)` with `g`
over `𝒪_K` (Pass 60); move `g` to `B[X]` (the commuting square); `G := g_B − C y` kills `x`
after `ι`; divide by Serre's monic `F` (Pass 55's descent) — the remainder kills `x` and has
degree `< natDegree F = |H|`, so it **vanishes** (Pass 61's brick); the exact identity
`G = F·(G /ₘ F)` transports along `σ̄` (the base coefficients are `σ̄`-fixed — Pass 57 — and
`C y ↦ C (σ̄y)`); mapping along `ι` and evaluating at `x` turns the left side into
`ι y − ι(σ̄y) = −ι(a)` and the right side into `(∏_{s ↦ σ̄} (x − s·x)) · (…)` (Pass 58's
polynomial equivariance + Pass 56's lift-set identity). Note the statement needs no
generator property of `y` — the division argument is uniform in `y ∈ B`.

With Pass 58 (`a ∣ b`, same product), the two elements are **mutually divisible**; the
Prop. 3 assembly (`Associated` + the Pass 59 `addVal` readings) is the next and final pass.

## Honesty

One direction of a comparison of elements of a given tower — **no reach toward R1–R3**. The
assembly (Associated + the sum formula) is NOT claimed — next pass. No new
`structure`/`class`; no owed witness; D1 N/A; D2 stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Polynomial
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [FiniteDimensional K' L] [IsGalois K' L]
variable [Fintype ((extensionIntegers K L).decompositionSubgroup K')]

/-- **Prop. 3, direction (ii)**: the lift-set product divides `ι(σ̄y − y)`, for **every**
`y ∈ B` and every lift `s₀`. Serre's monic-division argument: `ι y = g(x)` (Pass 60),
`G = g_B − C y` kills `x` after `ι`, the `F`-division remainder vanishes (Pass 61), and the
exact identity `G = F·(G /ₘ F)` transports along `σ̄` and evaluates at `x` to
`−ι(a) = (∏_{s ↦ σ̄} (x − s·x))·(…)` (Passes 55–58). -/
theorem liftProd_dvd_comapRingHom_smul_sub
    {x : ↥(extensionIntegers K L)}
    (hgen : Subring.closure
      (((extensionAlgebraMap K L).range :
          Set ↥(extensionIntegers K L)) ∪ {x}) = ⊤)
    (y : ↥((extensionIntegers K L).comap (algebraMap K' L)))
    (s₀ : (extensionIntegers K L).decompositionSubgroup K) :
    (∏ h : (extensionIntegers K L).decompositionSubgroup K',
        (x - (s₀ * decompositionRestrict K K'
            (extensionIntegers K L) h) • x))
      ∣ comapRingHom K' (extensionIntegers K L)
          (decompositionQuotient K K' (extensionIntegers K L) s₀ • y
            - y) := by
  -- Serre's polynomial and its descent (P55)
  obtain ⟨F, hF, hFmonic, hFdeg⟩ :=
    exists_fullProdXSubSMul_lift_extensionIntegers K K' (L := L) x
  -- represent ι y as g(x), g over 𝒪_K (P60)
  obtain ⟨g, hg⟩ := exists_polynomial_generator_rep K hgen
    (comapRingHom K' (extensionIntegers K L) y)
  -- move g to B[X]; its ι-image is the original
  have hgB : (g.map (baseToComapRingHom K K' (L := L))).map
      (comapRingHom K' (extensionIntegers K L))
      = g.map (extensionAlgebraMap K L) := by
    rw [Polynomial.map_map, comapRingHom_comp_baseToComapRingHom]
  -- G kills x after ι
  have hGeval : (((g.map (baseToComapRingHom K K' (L := L))
      - Polynomial.C y)).map
        (comapRingHom K' (extensionIntegers K L))).eval x = 0 := by
    rw [Polynomial.map_sub, Polynomial.eval_sub, hgB, hg, Polynomial.map_C,
        Polynomial.eval_C, sub_self]
  -- divide by F; the remainder is killed by P61
  have hid := Polynomial.modByMonic_add_div
    ((g.map (baseToComapRingHom K K' (L := L))) - Polynomial.C y) F
  have hFnat : F.natDegree
      = Fintype.card ((extensionIntegers K L).decompositionSubgroup K') := by
    rw [Polynomial.natDegree_eq_of_degree_eq hFdeg, fullProdXSubSMul_natDegree]
  have hreval : ((((g.map (baseToComapRingHom K K' (L := L)))
      - Polynomial.C y) %ₘ F).map
        (comapRingHom K' (extensionIntegers K L))).eval x = 0 := by
    have h5a := congrArg (fun P => (P.map
      (comapRingHom K' (extensionIntegers K L))).eval x) hid
    simp only [Polynomial.map_add, Polynomial.eval_add, Polynomial.map_mul,
      Polynomial.eval_mul] at h5a
    rw [hF, fullProdXSubSMul_eval, hGeval, zero_mul, add_zero] at h5a
    exact h5a
  have hrdeg : ((((g.map (baseToComapRingHom K K' (L := L)))
      - Polynomial.C y) %ₘ F)).natDegree
      < Fintype.card ((extensionIntegers K L).decompositionSubgroup K') := by
    by_cases h : (((g.map (baseToComapRingHom K K' (L := L)))
        - Polynomial.C y) %ₘ F) = 0
    · rw [h]
      simpa using Fintype.card_pos
    · rw [← hFnat]
      exact Polynomial.natDegree_lt_natDegree h
        (Polynomial.degree_modByMonic_lt _ hFmonic)
  have hr0 := eq_zero_of_map_comapRingHom_eval_eq_zero K K' hgen hreval hrdeg
  -- the exact division identity
  have hGF : (g.map (baseToComapRingHom K K' (L := L))) - Polynomial.C y
      = F * (((g.map (baseToComapRingHom K K' (L := L)))
          - Polynomial.C y) /ₘ F) := by
    conv_lhs => rw [← hid]
    rw [hr0, zero_add]
  -- transport along σ̄ (base coefficients are fixed; C y moves to C (σ̄ y))
  have hsmul_gB : decompositionQuotient K K'
        (extensionIntegers K L) s₀
        • (g.map (baseToComapRingHom K K' (L := L)))
      = g.map (baseToComapRingHom K K' (L := L)) := by
    ext n
    simp only [Polynomial.coeff_smul, Polynomial.coeff_map]
    exact congrArg Subtype.val
      (smul_baseToComapRingHom_range_eq K K' _ _ ⟨g.coeff n, rfl⟩)
  have h8 : (g.map (baseToComapRingHom K K' (L := L)))
      - Polynomial.C (decompositionQuotient K K'
          (extensionIntegers K L) s₀ • y)
      = (decompositionQuotient K K' (extensionIntegers K L) s₀ • F)
          * (decompositionQuotient K K' (extensionIntegers K L) s₀
              • (((g.map (baseToComapRingHom K K' (L := L)))
                  - Polynomial.C y) /ₘ F)) := by
    have h8a := congrArg (fun P => decompositionQuotient K K'
      (extensionIntegers K L) s₀ • P) hGF
    simp only [smul_sub, smul_mul', Polynomial.smul_C] at h8a
    rw [hsmul_gB] at h8a
    exact h8a
  -- map along ι, evaluate at x
  have h9 := congrArg (fun P => (P.map
    (comapRingHom K' (extensionIntegers K L))).eval x) h8
  simp only [Polynomial.map_sub, Polynomial.eval_sub, Polynomial.map_mul,
    Polynomial.eval_mul, Polynomial.map_C, Polynomial.eval_C] at h9
  rw [hgB, hg, map_comapRingHom_smul K K' (extensionIntegers K L) s₀ F,
      hF, map_fullProdXSubSMul_eval K K' (extensionIntegers K L) s₀ x]
    at h9
  -- h9 : ι y − ι (σ̄ y) = ∏ · c
  have h10 : comapRingHom K' (extensionIntegers K L)
      (decompositionQuotient K K' (extensionIntegers K L) s₀ • y - y)
      = -(comapRingHom K' (extensionIntegers K L) y
          - comapRingHom K' (extensionIntegers K L)
              (decompositionQuotient K K'
                (extensionIntegers K L) s₀ • y)) := by
    rw [map_sub]
    ring
  rw [h10, h9]
  exact dvd_neg.mpr ⟨_, rfl⟩


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms liftProd_dvd_comapRingHom_smul_sub

end Anabelian
