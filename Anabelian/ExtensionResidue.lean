/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionUniformizer

/-!
# The descent, rung 3: the residue field of `𝒪_L` is finite (Pass 31)

Third rung of the finite-extension block. The residue field `𝓀_L` of `𝒪_L = extensionIntegers
K L` is **finite** — so the Pass-28 wild/tame hypotheses (`CharP 𝓀 p`, with `p` the residue
characteristic) are now concrete at `𝒪_L`.

The chain: `𝒪_L` is module-finite over `𝒪[K]` (Pass 29's integral-closure finiteness,
transported); the residue map is a surjective `𝒪[K]`-linear map, so `𝓀_L` is module-finite over
`𝒪[K]`; the `𝒪[K]`-action factors through `𝓀[K]` (the **local homomorphism** brick — the
Pass-30 unit-transfer argument, abstracted from the uniformizer to every element); and a
finite-dimensional space over the finite `𝓀[K]` is finite.

## What is proved (all axiom-free)

This file holds the **local-homomorphism half** (unconditional); the finiteness half lives in
`Anabelian/ExtensionResidueFinite.lean` — split into two files for build-granularity (each file
of the descent must elaborate within the sandbox's per-call window; see the NOTES environment
log).

* `extensionAlgebraMap : 𝒪[K] →+* 𝒪_L` — the canonical inclusion.
* `isUnit_extensionAlgebraMap_iff` — **unit transfer**: `ι x` is a unit iff `x` is (forward via
  the integrally-closed intersection `𝒪_L ∩ K = 𝒪[K]`, Pass 30's argument generalized).
* `instance : IsLocalHom (extensionAlgebraMap K L)` — the finite-level Pass-19 brick; with it,
  `ResidueField.map` gives the residue extension `𝓀[K] →+* 𝓀_L`.

## Honesty

The local-hom bricks are unconditional (no separability needed here). No new `structure`/`class`
(`IsLocalHom` of a named map is a `Prop`-instance); no owed witness; D1 N/A; D2 N/A. Recovers
nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The canonical inclusion `𝒪[K] →+* 𝒪_L`. -/
noncomputable def extensionAlgebraMap : ↥𝒪[K] →+* ↥(extensionIntegers K L) where
  toFun x := ⟨algebraMap K L ↑x, (algebraMap_mem_extensionIntegers_iff K L ↑x).mpr x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp] theorem coe_extensionAlgebraMap (x : ↥𝒪[K]) :
    ((extensionAlgebraMap K L x : ↥(extensionIntegers K L)) : L) = algebraMap K L ↑x :=
  rfl

/-- **Unit transfer**: the inclusion `𝒪[K] → 𝒪_L` reflects units — the Pass-30 argument
(a unit-inverse lands in `𝒪_L ∩ K = 𝒪[K]`), abstracted from the uniformizer to every element. -/
theorem isUnit_extensionAlgebraMap_iff (x : ↥𝒪[K]) :
    IsUnit (extensionAlgebraMap K L x) ↔ IsUnit x := by
  constructor
  · intro hu
    obtain ⟨y, hy1, _⟩ := isUnit_iff_exists.mp hu
    by_cases hx0 : (↑x : K) = 0
    · exfalso
      have h1 : (extensionAlgebraMap K L x : L) * (y : L) = 1 := congrArg Subtype.val hy1
      rw [coe_extensionAlgebraMap, hx0, map_zero, zero_mul] at h1
      exact zero_ne_one h1
    · have hy1' : (algebraMap K L ↑x) * (y : L) = 1 := congrArg Subtype.val hy1
      have hyval : algebraMap K L (↑x)⁻¹ = (y : L) := by
        rw [map_inv₀]
        exact inv_eq_of_mul_eq_one_right hy1'
      have h3 : (↑x)⁻¹ ∈ 𝒪[K] := by
        have h4 : algebraMap K L (↑x)⁻¹ ∈ extensionIntegers K L := by
          rw [hyval]
          exact y.2
        exact (algebraMap_mem_extensionIntegers_iff K L _).mp h4
      exact isUnit_iff_exists.mpr ⟨⟨(↑x)⁻¹, h3⟩,
        Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩
  · intro hu
    exact hu.map (extensionAlgebraMap K L)

/-- The inclusion `𝒪[K] → 𝒪_L` is a **local homomorphism** (the finite-level Pass-19 brick). -/
instance : IsLocalHom (extensionAlgebraMap K L) :=
  ⟨fun {a} h => (isUnit_extensionAlgebraMap_iff K L a).mp h⟩

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms extensionAlgebraMap
#print axioms isUnit_extensionAlgebraMap_iff

end Anabelian
