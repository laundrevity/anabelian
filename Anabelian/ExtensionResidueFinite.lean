/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionResidue

/-!
# The descent, rung 3 (second half): the residue field of `𝒪_L` is finite (Pass 31)

The finiteness half of rung 3 (the local-hom half is `Anabelian/ExtensionResidue.lean`; split
for build-granularity). The chain: `𝒪_L` is module-finite over `𝒪[K]` (Pass 29's
integral-closure finiteness, transported); the residue map is a surjective `𝒪[K]`-linear map,
so `𝓀_L` is module-finite over `𝒪[K]`; the action factors through `𝓀[K]` (the local-hom brick),
and a finite-dimensional space over the finite `𝓀[K]` is finite.

* **`finite_residueField_extensionIntegers`** — `𝓀_L` is finite (`[Algebra.IsSeparable K L]`).
* `charP_residueField_extensionIntegers` — `char 𝓀_L = char 𝓀[K]` (injective residue
  extension): **Pass 28's `CharP` hypothesis is concrete at `𝒪_L`.**

## Honesty

`[Algebra.IsSeparable K L]` exactly where module-finiteness is consumed. All module/algebra
structures in the finiteness proof are `letI`-local (no new global instances). Remaining rungs:
the `IsNonarchimedeanLocalField L` assembly; the monogenicity discharge; `e·f = n`. No new
`structure`/`class`; no owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group;
R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The residue field of `𝒪_L` is finite** (`L/K` finite separable): module-finiteness over
`𝒪[K]` (Pass 29) descends to the residue level through the local homomorphism, and a
finite-dimensional space over the finite `𝓀[K]` is finite. -/
theorem finite_residueField_extensionIntegers [Algebra.IsSeparable K L] :
    Finite (ResidueField ↥(extensionIntegers K L)) := by
  -- 𝒪_L is module-finite over 𝒪[K] (subalgebra result, transported along the carrier identity)
  haveI hC : Module.Finite ↥𝒪[K] ↥(integralClosure ↥𝒪[K] L) :=
    IsIntegralClosure.finite ↥𝒪[K] K L ↥(integralClosure ↥𝒪[K] L)
  letI : Algebra ↥𝒪[K] ↥(extensionIntegers K L) := (extensionAlgebraMap K L).toAlgebra
  let e : ↥(integralClosure ↥𝒪[K] L) →ₗ[↥𝒪[K]] ↥(extensionIntegers K L) :=
    { toFun := fun y => ⟨y.1, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun c y => by
        apply Subtype.ext
        have h1 : ((c • y : ↥(integralClosure ↥𝒪[K] L)) : L)
            = algebraMap ↥𝒪[K] L c * (y : L) := by
          rw [SetLike.val_smul, Algebra.smul_def]
        rw [RingHom.id_apply]
        refine h1.trans ?_
        rw [IsScalarTower.algebraMap_apply ↥𝒪[K] K L]
        rfl }
  haveI hOL : Module.Finite ↥𝒪[K] ↥(extensionIntegers K L) :=
    Module.Finite.of_surjective e (fun z => ⟨⟨z.1, z.2⟩, rfl⟩)
  -- the residue map is a surjective 𝒪[K]-linear map
  letI : Algebra ↥𝒪[K] (ResidueField ↥(extensionIntegers K L)) :=
    ((IsLocalRing.residue ↥(extensionIntegers K L)).comp (extensionAlgebraMap K L)).toAlgebra
  let r : ↥(extensionIntegers K L) →ₗ[↥𝒪[K]] ResidueField ↥(extensionIntegers K L) :=
    { toFun := IsLocalRing.residue ↥(extensionIntegers K L)
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun c z => by
        change IsLocalRing.residue _ ((extensionAlgebraMap K L c) * z) = _
        rw [map_mul]
        rfl }
  haveI hkL : Module.Finite ↥𝒪[K] (ResidueField ↥(extensionIntegers K L)) :=
    Module.Finite.of_surjective r Ideal.Quotient.mk_surjective
  -- the action factors through 𝓀[K] (the local-hom brick); restrict scalars
  letI : Algebra (ResidueField ↥𝒪[K]) (ResidueField ↥(extensionIntegers K L)) :=
    (ResidueField.map (extensionAlgebraMap K L)).toAlgebra
  haveI : IsScalarTower ↥𝒪[K] (ResidueField ↥𝒪[K])
      (ResidueField ↥(extensionIntegers K L)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (ResidueField ↥𝒪[K]) (ResidueField ↥(extensionIntegers K L)) :=
    Module.Finite.of_restrictScalars_finite ↥𝒪[K] _ _
  exact Module.finite_of_finite (ResidueField ↥𝒪[K])

/-- **The residue characteristic is preserved**: `CharP 𝓀_L = CharP 𝓀[K]` along the (injective)
residue extension — Pass 28's `CharP` hypothesis, concrete at `𝒪_L`. -/
theorem charP_residueField_extensionIntegers (p : ℕ) [CharP (ResidueField ↥𝒪[K]) p] :
    CharP (ResidueField ↥(extensionIntegers K L)) p :=
  charP_of_injective_ringHom (ResidueField.map (extensionAlgebraMap K L)).injective p

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms finite_residueField_extensionIntegers
#print axioms charP_residueField_extensionIntegers

end Anabelian
