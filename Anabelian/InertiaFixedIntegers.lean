/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionRamificationData

/-!
# The descent, rung 6 (first half): the inertia-fixed integers (Pass 34)

Toward the maximal unramified subextension. The general-case base ring for the monogenicity
package is `𝒪_{L₀}` — classically, the integers of the inertia fixed field. This file builds
its working incarnation directly inside `𝒪_L`:

* **`inertiaFixedIntegers K L : Subring 𝒪_L`** — the elements fixed by every inertia element
  (`G₀ = ramificationGroup K (extensionIntegers K L) 0`).
* `smul_inertiaFixedIntegers_eq` — the **`hfix` half of the monogenicity package is free by
  definition** for this base.
* `extensionAlgebraMap_mem_inertiaFixedIntegers` — the base image lies inside it (Pass 32's
  `AlgEquiv.commutes` lemma), so the generalized engine
  (`Anabelian/ExtensionMonogenicGeneral.lean`) applies over it.

## Honesty

This is the *ring-theoretic* incarnation; the *field* `L₀` (fixed field of inertia in `L`) and
the identification `inertiaFixedIntegers = 𝒪_{L₀}` are not needed for the monogenicity package
and are not built here. No new `structure`/`class` beyond a `Subring` instance of a Mathlib
structure (rule-2: the subring is pinned by genuinely different models — for totally ramified
`L/K` it can be as small as the closure of `𝒪[K]`'s image, for unramified `L/K` it is all of
`𝒪_L`); no owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3
untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The inertia-fixed integers**: the subring of `𝒪_L` fixed pointwise by every inertia
element — the working incarnation of `𝒪_{L₀}` (the integers of the maximal unramified
subextension). -/
def inertiaFixedIntegers : Subring ↥(extensionIntegers K L) where
  carrier := {x | ∀ σ : ↥(ramificationGroup K (extensionIntegers K L) 0), σ.1 • x = x}
  one_mem' := fun σ => smul_one _
  mul_mem' := fun {a b} ha hb σ => by rw [smul_mul', ha σ, hb σ]
  zero_mem' := fun σ => smul_zero _
  add_mem' := fun {a b} ha hb σ => by rw [smul_add, ha σ, hb σ]
  neg_mem' := fun {a} ha σ => by rw [smul_neg, ha σ]

/-- Membership unfolded. -/
theorem mem_inertiaFixedIntegers_iff (x : ↥(extensionIntegers K L)) :
    x ∈ inertiaFixedIntegers K L ↔
      ∀ σ : ↥(ramificationGroup K (extensionIntegers K L) 0), σ.1 • x = x :=
  Iff.rfl

/-- **The `hfix` half of the monogenicity package is free by definition** over the
inertia-fixed integers. -/
theorem smul_inertiaFixedIntegers_eq
    (σ : ↥(ramificationGroup K (extensionIntegers K L) 0))
    (a : ↥(extensionIntegers K L)) (ha : a ∈ inertiaFixedIntegers K L) :
    σ.1 • a = a :=
  ha σ

/-- The base image lies in the inertia-fixed integers (decomposition elements are `K`-algebra
maps — Pass 32's lemma, restricted to inertia). -/
theorem extensionAlgebraMap_mem_inertiaFixedIntegers (c : ↥𝒪[K]) :
    extensionAlgebraMap K L c ∈ inertiaFixedIntegers K L :=
  fun σ => smul_extensionAlgebraMap_range_eq K L σ.1 _ ⟨c, rfl⟩

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms inertiaFixedIntegers
#print axioms smul_inertiaFixedIntegers_eq
#print axioms extensionAlgebraMap_mem_inertiaFixedIntegers

end Anabelian
