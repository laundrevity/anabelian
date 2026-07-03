/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.RamificationIdx
import Anabelian.Quotient.CharPoly
import Mathlib

/-!
# Toward `e' = |H₀|`: the `IsGaloisGroup` instance package (Pass 69)

Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` (`|inertia| = e`) runs on a group `G`
with `[IsGaloisGroup G R S]` — faithful action, commuting with `R`-scalars, fixed points
exactly `R`. This pass supplies that package for `G = D_{K'}(𝒪_L)`, `R = B = 𝒪_L ∩ K'`,
`S = 𝒪_L` (on Pass 68's `comapAlgebra`):

* **faithful** — automorphisms agreeing on the integers agree on `L` (valuation dichotomy);
* **commutes** — decomposition elements fix the `B`-scalars (`AlgEquiv.commutes`);
* **isInvariant** — the fixed points of the action are exactly `B`: Pass 55's fixed-points
  descent, with `D_{K'}(𝒪_L) = ⊤` converting subgroup-fixedness to Galois-fixedness.

Each component was already a project brick; this pass is the instance packaging. Remaining
for `e' = |H₀|` (next passes): the Dedekind/finite/torsion-free/`LiesOver`/separable-residue
instance package, the inertia matching (`Ideal.inertia` vs `ramificationGroup … 0`), and the
application.

## Honesty

Instance packaging of existing theorems for a given tower — **no reach toward R1–R3**.
`e' = |H₀|` is NOT claimed. All three declarations instantiate existing Mathlib classes
(`FaithfulSMul`, `SMulCommClass`, `Algebra.IsInvariant`, `IsGaloisGroup`) — no new
`structure`/`class`, no rule-2 obligation; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian


section Faithful

variable (K' : Type*) [Field K']
variable {L : Type*} [Field L] [Algebra K' L]
variable (A : ValuationSubring L)

/-- **The decomposition action on the integers is faithful**: automorphisms agreeing on `A`
agree on all of `L` (the valuation dichotomy `mem_or_inv_mem` — the Pass 23 ending, as an
instance). -/
instance faithfulSMul_decomposition : FaithfulSMul (A.decompositionSubgroup K') ↥A where
  eq_of_smul_eq_smul := by
    intro σ τ h
    apply Subtype.ext
    apply AlgEquiv.ext
    intro l
    rcases A.mem_or_inv_mem l with hl | hl
    · exact congrArg Subtype.val (h ⟨l, hl⟩)
    · have h2 : (σ : L ≃ₐ[K'] L) l⁻¹ = (τ : L ≃ₐ[K'] L) l⁻¹ :=
        congrArg Subtype.val (h ⟨l⁻¹, hl⟩)
      rw [map_inv₀, map_inv₀] at h2
      exact inv_injective h2

/-- **The action commutes with the `B`-scalars**: `b • s = ι(b)·s` (Pass 68's
`comapAlgebra`), and decomposition elements fix `ι(b)` (`AlgEquiv.commutes` — they are
`K'`-algebra maps). -/
instance smulCommClass_decomposition :
    SMulCommClass (A.decompositionSubgroup K') ↥(A.comap (algebraMap K' L)) ↥A where
  smul_comm := by
    intro g b s
    have hfix : g • comapRingHom K' A b = comapRingHom K' A b := by
      apply Subtype.ext
      exact AlgEquiv.commutes (g : L ≃ₐ[K'] L) (b : K')
    calc g • (b • s) = g • (comapRingHom K' A b * s) := by
          rw [Algebra.smul_def, algebraMap_comapAlgebra]
      _ = (g • comapRingHom K' A b) * (g • s) := smul_mul' g _ s
      _ = comapRingHom K' A b * (g • s) := by rw [hfix]
      _ = b • (g • s) := by rw [Algebra.smul_def, algebraMap_comapAlgebra]

end Faithful

section Invariant

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [FiniteDimensional K' L] [IsGalois K' L]

/-- **The fixed points of the decomposition action on `𝒪_L` are exactly `B`** — Pass 55's
fixed-points descent (`exists_comapRingHom_eq_of_forall_smul_eq`), converted from
`D`-fixedness to full-`Gal(L/K')`-fixedness by `D_{K'}(𝒪_L) = ⊤` (Pass 55). -/
instance isInvariant_decomposition :
    Algebra.IsInvariant
      ↥((extensionIntegers K L).comap (algebraMap K' L))
      ↥(extensionIntegers K L)
      ((extensionIntegers K L).decompositionSubgroup K') where
  isInvariant := by
    intro b hb
    have hfield : ∀ σ : L ≃ₐ[K'] L, σ (b : L) = (b : L) := by
      intro σ
      have hσD : σ ∈ (extensionIntegers K L).decompositionSubgroup K' := by
        rw [decompositionSubgroup_extensionIntegers_restrict_eq_top K K']
        exact Subgroup.mem_top σ
      exact congrArg Subtype.val (hb ⟨σ, hσD⟩)
    obtain ⟨a, ha⟩ :=
      exists_comapRingHom_eq_of_forall_smul_eq K'
        (extensionIntegers K L) hfield
    exact ⟨a, ha⟩

/-- **The decomposition group is a Galois group for `B ⊆ 𝒪_L`** in Mathlib's sense
(`IsGaloisGroup` = faithful + commutes + invariant) — the gateway hypothesis of the
`RamificationInertia` machinery, in particular `Ideal.card_inertia_eq_ramificationIdxIn`
(`|inertia| = e`). -/
instance isGaloisGroup_decomposition :
    IsGaloisGroup ((extensionIntegers K L).decompositionSubgroup K')
      ↥((extensionIntegers K L).comap (algebraMap K' L))
      ↥(extensionIntegers K L) where
  faithful := faithfulSMul_decomposition K' (extensionIntegers K L)
  commutes := smulCommClass_decomposition K' (extensionIntegers K L)
  isInvariant := isInvariant_decomposition K K'

end Invariant


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms faithfulSMul_decomposition
#print axioms smulCommClass_decomposition
#print axioms isInvariant_decomposition
#print axioms isGaloisGroup_decomposition

end Anabelian
