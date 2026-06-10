/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionRamificationData
import Anabelian.TameInjectivity

/-!
# The descent, rung 5 (second half): the assembled showcase — tame injectivity, concrete (Pass 33)

The assembly. For a finite separable extension of nonarchimedean local fields with surjective
residue extension (totally ramified):

* **`closure_eq_top_of_residue_surjective`** — the complete `hgen` package: the Pass-32 engine
  fed with Pass 33's discharged data.
* **`ker_tameCharacter_extensionIntegers`** — **the showcase**: Pass 25's kernel identification,
  instantiated — `ker θ₀ = G₁` for any uniformizer of `𝒪_L`. Combined with Pass 24's
  `tameQuotientHom`, this is Serre IV §2 Prop. 7 at level 0 **as a theorem about actual local
  fields**: the tame character of a totally ramified extension embeds `G₀/G₁ ↪ 𝓀_Lˣ`.

Every hypothesis the abstract L2 theory accumulated since Pass 23 — separation, finiteness,
eventual triviality, uniformizer package, monogenicity — is now **proved** in this setting; the
hypothesis-parametrized architecture has paid out in full on the totally ramified case.

## Honesty

`hsurj` (residue surjectivity) is the totally-ramified datum itself, stated in its honest form.
The general case routes through the maximal unramified subextension `L₀` — named, the block's
remaining depth. No new `structure`/`class`; no owed witness; D1 N/A; D2 N/A. Recovers nothing
from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The `hgen` package, complete**: for totally ramified `L/K` (surjective residue extension),
the base image together with any uniformizer generates `𝒪_L` as a ring. -/
theorem closure_eq_top_of_residue_surjective [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π})
    (hsurj : Function.Surjective (ResidueField.map (extensionAlgebraMap K L))) :
    Subring.closure
      (((extensionAlgebraMap K L).range : Set ↥(extensionIntegers K L)) ∪ {π}) = ⊤ := by
  obtain ⟨e, he⟩ := exists_pow_maximalIdeal_le_map K L
  exact closure_range_union_uniformizer_eq_top K L π hspan
    (residue_sub_mem_of_surjective K L hsurj) e he

/-- **The showcase — tame injectivity on actual local fields**: for a totally ramified finite
separable extension `L/K` of nonarchimedean local fields and any uniformizer `π` of `𝒪_L`,

> `ker θ₀ = G₁` —

Pass 25's kernel identification with every hypothesis discharged. With `tameQuotientHom`
(Pass 24), the tame character embeds `G₀/G₁ ↪ 𝓀_Lˣ`: Serre IV §2 Prop. 7 at level 0, as a
theorem about local fields rather than a hypothesis-parametrized schema. -/
theorem ker_tameCharacter_extensionIntegers [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0)
    (hsurj : Function.Surjective (ResidueField.map (extensionAlgebraMap K L))) :
    (tameCharacter K π hspan hπ0).ker
      = (ramificationGroup K (extensionIntegers K L) 1).subgroupOf
          (ramificationGroup K (extensionIntegers K L) 0) :=
  ker_tameCharacter K π hspan hπ0
    (closure_eq_top_of_residue_surjective K L π hspan hsurj)
    (fun σ a ha => smul_extensionAlgebraMap_range_eq K L σ.1 a ha)

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms closure_eq_top_of_residue_surjective
#print axioms ker_tameCharacter_extensionIntegers

end Anabelian
