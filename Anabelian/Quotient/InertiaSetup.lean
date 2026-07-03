/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.GaloisGroup
import Anabelian.Quotient.ComapIntegers
import Anabelian.Quotient.GeneratorRep
import Anabelian.Extension.ResidueFinite
import Mathlib

/-!
# Toward `e' = |H₀|`: the remaining instances, and the inertia matching (Pass 70)

The hypothesis list of Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` (`|inertia| = e`)
is now fully coverable. This pass supplies everything that was missing:

* **the inertia matching** (`ramificationGroup_zero_eq_inertia`): the project's
  `G₀ = ramificationGroup K' A 0` **is** Mathlib's `(𝔪_L).inertia D` — Pass 23 built the
  whole filtration from `Ideal.inertia` of `𝔪^(i+1)`, so at level `0` the two notions
  coincide by `pow_one`; the anticipated "kernel-vs-kernel comparison" is a `norm_num`;
* `isTorsionFree_comap`, `liesOver_maximalIdeal` (generic `(K', A)`): torsion-freeness of the
  tower module and `𝔪_L.LiesOver 𝔪_B` (Pass 50's `𝔪`-reflection + Pass 59's unit
  transfer);
* `baseComapAlgebra` + `isScalarTower_baseComap` + `moduleFinite_comap`: the tower
  `𝒪_K → B → 𝒪_L` as algebras (Pass 60's commuting square, verbatim, as the tower axiom)
  and **`Module.Finite ↥B ↥𝒪_L`** by restricting Pass 32's finiteness;
* `isSeparable_residue`: the residue extension is separable (finite fields are perfect).

Probe checks confirmed the rest is automatic: `IsDedekindDomain` for both rings follows from
the DVR instances (P35/P57), and the finite-field separability chain
(`Finite` + `IsAlgebraic` ⟹ `IsSeparable`) is already in Mathlib. With Pass 68
(`ramificationIdx = e'`) and Pass 69 (`IsGaloisGroup`), every hypothesis of
`card_inertia_eq_ramificationIdxIn` is now available — the application (`e' = |H₀|`) is the
next pass.

## Honesty

Instance plumbing and a definitional matching for a given tower — **no reach toward R1–R3**.
`e' = |H₀|` is NOT claimed. All declarations instantiate existing Mathlib classes or match
existing definitions — no new `structure`/`class`, no rule-2 obligation; no owed witness;
D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


section Generic

variable (K' : Type*) [Field K']
variable {L : Type*} [Field L] [Algebra K' L]
variable (A : ValuationSubring L)

/-- **The inertia matching**: the project's `G₀ = ramificationGroup K' A 0` IS Mathlib's
`Ideal.inertia` of the maximal ideal — both are `{g | ∀ x, g•x − x ∈ 𝔪}`; Pass 23 built the
filtration from `Ideal.inertia` of `𝔪^(i+1)`, so at `i = 0` this is `pow_one`. -/
theorem ramificationGroup_zero_eq_inertia :
    ramificationGroup K' A 0
      = (IsLocalRing.maximalIdeal ↥A).inertia (A.decompositionSubgroup K') := by
  rw [ramificationGroup]
  norm_num

/-- The tower module is torsion-free: `B` and `𝒪_L` are domains and the inclusion is
injective, so regular scalars act injectively. -/
instance isTorsionFree_comap : Module.IsTorsionFree ↥(A.comap (algebraMap K' L)) ↥A where
  isSMulRegular := by
    intro r hr m₁ m₂ h
    have hr0 : (r : K') ≠ 0 := by
      intro h0
      exact isRegular_iff_ne_zero.mp hr (Subtype.ext h0)
    have hι : comapRingHom K' A r ≠ 0 := by
      intro h1
      have h2 := congrArg Subtype.val h1
      change algebraMap K' L (r : K') = 0 at h2
      exact hr0 ((map_eq_zero (algebraMap K' L)).mp h2)
    have h3 : comapRingHom K' A r * m₁ = comapRingHom K' A r * m₂ := by
      have h4 : r • m₁ = r • m₂ := h
      rwa [Algebra.smul_def, Algebra.smul_def, algebraMap_comapAlgebra] at h4
    exact mul_left_cancel₀ hι h3

/-- **`𝔪_L` lies over `𝔪_B`**: the comap of the maximal ideal along the tower inclusion is
the maximal ideal — Pass 50's `𝔪`-reflection one way, Pass 59's two-way unit transfer the
other. -/
instance liesOver_maximalIdeal :
    (IsLocalRing.maximalIdeal ↥A).LiesOver
      (IsLocalRing.maximalIdeal ↥(A.comap (algebraMap K' L))) :=
  ⟨by
    refine le_antisymm ?_ ?_
    · intro b hb
      change comapRingHom K' A b ∈ IsLocalRing.maximalIdeal ↥A
      rw [mem_maximalIdeal, _root_.mem_nonunits_iff]
      intro hu
      rw [isUnit_comapRingHom_iff] at hu
      rw [mem_maximalIdeal, _root_.mem_nonunits_iff] at hb
      exact hb hu
    · intro b hb
      have h1 : comapRingHom K' A b ∈ IsLocalRing.maximalIdeal ↥A := hb
      exact mem_maximalIdeal_of_comapRingHom K' A h1⟩

end Generic

section Tower

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L]

/-- The base algebra `𝒪_K → B` (via `baseToComapRingHom`; no canonical instance exists, no
diamond). -/
noncomputable instance baseComapAlgebra :
    Algebra ↥𝒪[K] ↥((extensionIntegers K L).comap (algebraMap K' L)) :=
  (baseToComapRingHom K K' (L := L)).toAlgebra

/-- The tower `𝒪_K → B → 𝒪_L` is a scalar tower — Pass 60's commuting square, verbatim. -/
instance isScalarTower_baseComap :
    IsScalarTower ↥𝒪[K]
      ↥((extensionIntegers K L).comap (algebraMap K' L))
      ↥(extensionIntegers K L) :=
  IsScalarTower.of_algebraMap_eq'
    (comapRingHom_comp_baseToComapRingHom K K' (L := L)).symm

/-- **`𝒪_L` is module-finite over `B`**: Pass 32's finiteness over `𝒪_K`, restricted along
the tower (`Module.Finite.of_restrictScalars_finite`). -/
instance moduleFinite_comap [Algebra.IsSeparable K L] :
    Module.Finite ↥((extensionIntegers K L).comap (algebraMap K' L))
      ↥(extensionIntegers K L) :=
  Module.Finite.of_restrictScalars_finite ↥𝒪[K]
    ↥((extensionIntegers K L).comap (algebraMap K' L))
    ↥(extensionIntegers K L)

/-- **The residue extension is separable**: `𝒪_L`'s residue field is finite (Pass 36),
`B`'s embeds into it (fields), a finite extension of a finite field is algebraic, and finite
fields are perfect — Mathlib's instance chain closes it. -/
instance isSeparable_residue [Algebra.IsSeparable K L] :
    Algebra.IsSeparable
      (↥((extensionIntegers K L).comap (algebraMap K' L))
        ⧸ IsLocalRing.maximalIdeal
            ↥((extensionIntegers K L).comap (algebraMap K' L)))
      (↥(extensionIntegers K L)
        ⧸ IsLocalRing.maximalIdeal ↥(extensionIntegers K L)) := by
  letI := Ideal.Quotient.field
    (IsLocalRing.maximalIdeal ↥((extensionIntegers K L).comap (algebraMap K' L)))
  letI := Ideal.Quotient.field
    (IsLocalRing.maximalIdeal ↥(extensionIntegers K L))
  haveI hfinE : Finite (↥(extensionIntegers K L)
      ⧸ IsLocalRing.maximalIdeal ↥(extensionIntegers K L)) :=
    finite_residueField_extensionIntegers K L
  haveI hfinF : Finite (↥((extensionIntegers K L).comap (algebraMap K' L))
      ⧸ IsLocalRing.maximalIdeal
          ↥((extensionIntegers K L).comap (algebraMap K' L))) := by
    refine Finite.of_injective (algebraMap _ (↥(extensionIntegers K L)
      ⧸ IsLocalRing.maximalIdeal ↥(extensionIntegers K L))) ?_
    exact RingHom.injective _
  haveI : Module.Finite
      (↥((extensionIntegers K L).comap (algebraMap K' L))
        ⧸ IsLocalRing.maximalIdeal
            ↥((extensionIntegers K L).comap (algebraMap K' L)))
      (↥(extensionIntegers K L)
        ⧸ IsLocalRing.maximalIdeal ↥(extensionIntegers K L)) :=
    Module.Finite.of_finite
  infer_instance

end Tower


-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms ramificationGroup_zero_eq_inertia
#print axioms isTorsionFree_comap
#print axioms liesOver_maximalIdeal
#print axioms baseComapAlgebra
#print axioms isScalarTower_baseComap
#print axioms moduleFinite_comap
#print axioms isSeparable_residue

end Anabelian
