/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.Division
import Anabelian.Quotient.AddVal
import Mathlib

/-!
# SERRE IV §1 PROP. 3: the sum formula `e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)` (Pass 63)

**The wall is down.** For a tower `K ⊆ K' ⊆ L` of finite extensions of a nonarchimedean
local field (`K'/K` normal, `L/K'` Galois), every `σ̄` in the subextension's decomposition
group, and every lift `s₀`:

> **`i_{K'/K}(σ̄) · e' = Σ_{h ∈ H} i_{L/K}(s₀ · h)`**
> (`lowerIndex_decompositionQuotient_mul_eq_sum`)

— Serre, *Local Fields*, IV §1 Prop. 3, in the project's terms: `i` is Pass 51's
generator-free `lowerIndex` (`ℕ∞`-valued, so the statement needs **no** `σ̄ ≠ 1`
hypothesis — at `σ̄ = 1` both sides are `⊤`), `e' = addVal_{𝒪_L}(ι π_B)` is the ramification
index of `L/K'` in `addVal` form (any irreducible `π_B` of `B = 𝒪_L ∩ K'`), and the sum
ranges over the lift set in its `H`-parametrized form (Pass 56's fiber bijection). The final
statement is **generator-free**: the `x` and `y` of the proof disappear.

The proof is eight lines of assembly over fourteen passes of substrate: choose `x` (Pass 54)
and `y` (Pass 57); `ι(σ̄y − y)` and the lift-set product **divide each other** (Pass 58's
telescoping direction; Pass 62's division direction); mutual divisibility gives equal
`addVal` (`addVal_le_iff_dvd`); the left side reads as `i_{K'/K}(σ̄)·e'` (Pass 59's
`e'`-dilation + Pass 57's concrete `i_{K'/K}`), the right side as `Σ_h i_{L/K}(s₀·dr h)`
(Pass 59's fiber sum, per-factor Passes 53–54).

## Why this matters (the ladder)

Prop. 3 is the arithmetic engine of Serre IV §3 **Lemma 5**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H`, which is the gate to **`φ`-transitivity** (Prop. 15) and
**Herbrand's theorem** `(G/H)^v = G^v H/H` (Prop. 14) — the upper numbering's defining
quotient-compatibility, and the reason the quotient arc (Passes 50–63) was built. With the
`φ`/`ψ` analytic theory complete (Passes 44–49), Lemma 5 is the next target.

## Honesty

A quantitative identity for the Galois action of a **given** tower — **no reach toward
R1–R3**; nothing is recovered from an abstract group. Lemma 5 / Herbrand are NOT claimed:
Prop. 3 is their input, and converting the `i`-identity into the `φ`-renumbering statement
is real further work (the `inf`/`min` arguments of Serre's Lemma 5 proof). No new
`structure`/`class`; no owed witness; D1 N/A; D2 stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged —
**Prop. 3 is proved from the standard axioms of Lean + Mathlib, with zero project axioms.**
-/

open ValuationSubring IsLocalRing IsDiscreteValuationRing Polynomial
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [FiniteDimensional K' L] [IsGalois K' L]
variable [Fintype ((extensionIntegers K L).decompositionSubgroup K')]

/-- **Serre IV §1 Prop. 3 — the sum formula**: for every `σ̄ = decompositionQuotient s₀` in
the subextension's decomposition group and every irreducible `π` of `B = 𝒪_L ∩ K'`,

`i_{K'/K}(σ̄) · e' = Σ_{h ∈ H} i_{L/K}(s₀ · dr h)`

where `e' = addVal_{𝒪_L}(ι π)` is the ramification index of `L/K'` and the right side is the
sum over the lifts of `σ̄` (Pass 56's `H`-parametrization). Generator-free and valid for all
`σ̄` (both sides `⊤` at `σ̄ = 1`). Proof: `ι(σ̄y − y)` and `∏_{s ↦ σ̄}(x − s·x)` divide each
other (Passes 58/62), hence have equal `addVal`; read the two sides by Passes 57/59. -/
theorem lowerIndex_decompositionQuotient_mul_eq_sum
    (s₀ : (extensionIntegers K L).decompositionSubgroup K)
    {π : ↥((extensionIntegers K L).comap (algebraMap K' L))}
    (hπ : Irreducible π) :
    lowerIndex K ((extensionIntegers K L).comap (algebraMap K' L))
        (decompositionQuotient K K' (extensionIntegers K L) s₀)
      * addVal ↥(extensionIntegers K L)
          (comapRingHom K' (extensionIntegers K L) π)
      = ∑ h : (extensionIntegers K L).decompositionSubgroup K',
          lowerIndex K (extensionIntegers K L)
            (s₀ * decompositionRestrict K K' (extensionIntegers K L) h) := by
  obtain ⟨x, hgenx⟩ := exists_generator_extensionIntegers K L
  obtain ⟨y, hyGen, hydvd, hyaddval⟩ := exists_generator_comap_spec K K' (L := L)
  obtain ⟨F, hF, _, _⟩ := exists_fullProdXSubSMul_lift_extensionIntegers K K' (L := L) x
  have h1 := comapRingHom_smul_sub_dvd_liftProd K K' (extensionIntegers K L) s₀ x hF
    (fun c => hydvd (decompositionQuotient K K' (extensionIntegers K L) s₀) c)
  have h2 := liftProd_dvd_comapRingHom_smul_sub K K' hgenx y s₀
  have h3 : addVal ↥(extensionIntegers K L)
      (comapRingHom K' (extensionIntegers K L)
        (decompositionQuotient K K' (extensionIntegers K L) s₀ • y - y))
      = addVal ↥(extensionIntegers K L)
          (∏ h : (extensionIntegers K L).decompositionSubgroup K',
            (x - (s₀ * decompositionRestrict K K' (extensionIntegers K L) h) • x)) :=
    le_antisymm (addVal_le_iff_dvd.mpr h1) (addVal_le_iff_dvd.mpr h2)
  rw [addVal_comapRingHom K' (extensionIntegers K L) hπ,
      ← hyaddval (decompositionQuotient K K' (extensionIntegers K L) s₀)] at h3
  rw [addVal_liftProd K K' hgenx s₀] at h3
  exact h3

-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms lowerIndex_decompositionQuotient_mul_eq_sum

end Anabelian
