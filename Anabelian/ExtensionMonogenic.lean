/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionResidueFinite

/-!
# The descent, rung 4 (first half): the monogenicity data over the base (Pass 32)

Toward the monogenicity discharge. This file sets up the **statement-level structures** and the
**free half** of the monogenicity package for `A₀ = 𝒪[K]` (its image in `𝒪_L`):

* the global `Algebra 𝒪[K] 𝒪_L` instance (promoting Pass 31's proof-local structure — the
  canonical one, via `extensionAlgebraMap`; no competing instance exists),
* the global `Module.Finite 𝒪[K] 𝒪_L` instance (Pass 29's integral-closure finiteness,
  transported — now available to statements),
* **`smul_extensionAlgebraMap_range_eq`** — the `hfix` half of the monogenicity package is
  **free** for `A₀ = range(𝒪[K] → 𝒪_L)`: every decomposition element is a `K`-algebra
  equivalence, so it fixes the base pointwise. (Hence every `G_i`, by restriction.)

The `hgen` half — `Subring.closure (A₀ ∪ {π}) = ⊤` under totally-ramified data — is the engine
in `Anabelian/ExtensionMonogenicTop.lean` (split for build-granularity).

## Honesty

The choice `A₀ = range(𝒪[K])` targets the **totally ramified** case (where it is the right
inertia-fixed base); the general case needs `A₀ = 𝒪_{L₀}` (the maximal unramified subextension)
— named future work. The global instances are the canonical structures on our own definitions
(no diamond: nothing else provides `Algebra 𝒪[K] 𝒪_L`); noted per the D-discipline. No new
`structure`/`class` beyond these instances; no owed witness; D1 N/A; D2 N/A. Recovers nothing
from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The canonical algebra structure `𝒪[K] → 𝒪_L` (global form of Pass 31's proof-local
structure). -/
noncomputable instance : Algebra ↥𝒪[K] ↥(extensionIntegers K L) :=
  (extensionAlgebraMap K L).toAlgebra

/-- `𝒪_L` is module-finite over `𝒪[K]` (`L/K` finite separable) — Pass 29's integral-closure
finiteness, transported to the valuation-subring carrier (global form). -/
instance [Algebra.IsSeparable K L] : Module.Finite ↥𝒪[K] ↥(extensionIntegers K L) := by
  haveI hC : Module.Finite ↥𝒪[K] ↥(integralClosure ↥𝒪[K] L) :=
    IsIntegralClosure.finite ↥𝒪[K] K L ↥(integralClosure ↥𝒪[K] L)
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
  exact Module.Finite.of_surjective e (fun z => ⟨⟨z.1, z.2⟩, rfl⟩)

/-- **The `hfix` half of the monogenicity package, free**: every decomposition element fixes
the base image `A₀ = range(𝒪[K] → 𝒪_L)` pointwise (it is a `K`-algebra equivalence). -/
theorem smul_extensionAlgebraMap_range_eq
    (σ : ↥((extensionIntegers K L).decompositionSubgroup K))
    (a : ↥(extensionIntegers K L)) (ha : a ∈ (extensionAlgebraMap K L).range) :
    σ • a = a := by
  obtain ⟨c, rfl⟩ := ha
  apply Subtype.ext
  change (σ : L ≃ₐ[K] L) (algebraMap K L ↑c) = algebraMap K L ↑c
  exact AlgEquiv.commutes _ _

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms smul_extensionAlgebraMap_range_eq

end Anabelian
