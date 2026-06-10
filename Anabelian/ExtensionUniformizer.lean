/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionIntegers
import Anabelian.TameCharacter

/-!
# The descent, rung 2: `𝒪_L` is a DVR — the uniformizer package, discharged (Pass 30)

Second rung of the finite-extension block. Pass 29 made `𝒪_L = extensionIntegers K L` a
Noetherian valuation subring; this pass makes it a **discrete valuation ring** and extracts the
**uniformizer package** `(π_L, 𝔪_L = (π_L), π_L ≠ 0)` — the exact hypothesis triple that every
character theorem since Pass 24 (`tameCharacter`, the Pass-25/27 embeddings, the Pass-28
wild/tame dichotomy) has carried as `(π, hspan, hπ0)`. At `𝒪_L` it is now a **theorem**.

## What is proved (all axiom-free)

* `algebraMap_mem_extensionIntegers_iff` — **the integrally-closed intersection**
  `𝒪_L ∩ K = 𝒪[K]`: an element of the base field is integral over `𝒪[K]` iff it lies in
  `𝒪[K]`.
* `maximalIdeal_extensionIntegers_ne_bot` — `𝒪_L` is **not a field**: the base uniformizer
  `ϖ_K` stays a nonzero non-unit in `𝒪_L` (a unit-inverse would land in `𝒪_L ∩ K = 𝒪[K]`).
* **`isDiscreteValuationRing_extensionIntegers`** — `IsDiscreteValuationRing 𝒪_L`
  (`[Algebra.IsSeparable K L]`): a Noetherian Bezout domain is a PID (`IsBezout.TFAE`), local
  with `𝔪 ≠ ⊥`.
* **`exists_uniformizer_extensionIntegers`** — the package: `∃ π, 𝔪_L = (π) ∧ π ≠ 0`.
* `extensionTameCharacter` — the showcase: **the tame character of a finite separable extension
  of local fields exists**, by instantiating Pass 24's `tameCharacterOfIrreducible` at `𝒪_L`
  (canonical by Pass 24's uniformizer-independence).

With Pass 29's discharges (separation, finiteness, eventual triviality) and this pass's
uniformizer package, the abstract L2 theory applies to `𝒪_L` with **only the monogenicity
hypothesis remaining open** (it gates the injectivity/kernel-identification half and the
Pass-28 dichotomy) — that discharge, plus the finite residue field, are the block's remaining
rungs.

## Honesty

`[Algebra.IsSeparable K L]` appears exactly where Pass 29's Noetherian-ness is consumed (the DVR
instance and everything after it) — same named boundary. NOT yet built: finite residue field
(`𝓀_L`, then `CharP 𝓀_L p` concrete); `IsNonarchimedeanLocalField L` assembly; the monogenicity
discharge; `e·f = n`. No new `structure`/`class`; no owed witness; D1 N/A; D2 N/A (this file is
`integralClosure`/`ValuationSubring`-native — the spectral structure stays sealed in Pass 29's
definition). Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The integrally-closed intersection `𝒪_L ∩ K = 𝒪[K]`**: a base-field element is in `𝒪_L`
iff it is in `𝒪[K]`. -/
theorem algebraMap_mem_extensionIntegers_iff (x : K) :
    algebraMap K L x ∈ extensionIntegers K L ↔ x ∈ 𝒪[K] := by
  rw [mem_extensionIntegers_iff]
  constructor
  · intro h
    have h2 : IsIntegral ↥𝒪[K] x :=
      (isIntegral_algebraMap_iff (algebraMap K L).injective).mp h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
    rw [← hy]
    exact y.2
  · intro h
    exact (isIntegral_algebraMap_iff (algebraMap K L).injective).mpr
      (IsIntegrallyClosed.isIntegral_iff.mpr ⟨⟨x, h⟩, rfl⟩)

/-- `𝒪_L` is **not a field**: the base uniformizer remains a nonzero non-unit (its would-be
inverse would lie in `𝒪_L ∩ K = 𝒪[K]`, making `ϖ_K` a unit of `𝒪[K]`). -/
theorem maximalIdeal_extensionIntegers_ne_bot :
    maximalIdeal ↥(extensionIntegers K L) ≠ ⊥ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[K]
  have hϖK0 : (↑ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hmem : algebraMap K L ↑ϖ ∈ extensionIntegers K L :=
    (algebraMap_mem_extensionIntegers_iff K L ↑ϖ).mpr ϖ.2
  set x : ↥(extensionIntegers K L) := ⟨algebraMap K L ↑ϖ, hmem⟩ with hxdef
  have hx0 : x ≠ 0 := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [hxdef] at h1
    exact hϖK0 ((map_eq_zero (algebraMap K L)).mp h1)
  have hxnu : ¬ IsUnit x := by
    intro hu
    obtain ⟨y, hy1, _⟩ := isUnit_iff_exists.mp hu
    have hy1' : (algebraMap K L ↑ϖ) * (y : L) = 1 := congrArg Subtype.val hy1
    have hyval : algebraMap K L (↑ϖ)⁻¹ = (y : L) := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right hy1'
    have h3 : (↑ϖ)⁻¹ ∈ 𝒪[K] := by
      have h4 : algebraMap K L (↑ϖ)⁻¹ ∈ extensionIntegers K L := by
        rw [hyval]
        exact y.2
      exact (algebraMap_mem_extensionIntegers_iff K L _).mp h4
    apply hϖ.not_isUnit
    refine isUnit_iff_exists.mpr ⟨⟨(↑ϖ)⁻¹, h3⟩, ?_, ?_⟩
    · exact Subtype.ext (mul_inv_cancel₀ hϖK0)
    · exact Subtype.ext (inv_mul_cancel₀ hϖK0)
  intro hbot
  have hm : x ∈ maximalIdeal ↥(extensionIntegers K L) :=
    (IsLocalRing.mem_maximalIdeal x).mpr hxnu
  rw [hbot, Submodule.mem_bot] at hm
  exact hx0 hm

/-- **`𝒪_L` is a discrete valuation ring** (`L/K` finite separable): Noetherian (Pass 29) +
Bezout (valuation ring) ⟹ PID (`IsBezout.TFAE`); local with `𝔪 ≠ ⊥`. -/
instance isDiscreteValuationRing_extensionIntegers [Algebra.IsSeparable K L] :
    IsDiscreteValuationRing ↥(extensionIntegers K L) := by
  haveI hnoeth := isNoetherianRing_extensionIntegers K L
  haveI hpir : IsPrincipalIdealRing ↥(extensionIntegers K L) :=
    ((IsBezout.TFAE (R := ↥(extensionIntegers K L))).out 0 1).mp hnoeth
  exact ⟨maximalIdeal_extensionIntegers_ne_bot K L⟩

/-- **The uniformizer package at `𝒪_L`** — the `(π, hspan, hπ0)` hypothesis triple of every
character theorem since Pass 24, now a theorem for finite separable extensions of local
fields. -/
theorem exists_uniformizer_extensionIntegers [Algebra.IsSeparable K L] :
    ∃ π : ↥(extensionIntegers K L),
      maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π} ∧ π ≠ 0 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(extensionIntegers K L)
  exact ⟨π, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, hπ.ne_zero⟩

/-- **The showcase**: the tame character of a finite separable extension of local fields,
`θ₀ : G₀(L/K) →* 𝓀_Lˣ` — Pass 24's `tameCharacterOfIrreducible` instantiated at `𝒪_L` (the
choice of irreducible is immaterial by Pass 24's `tameCharacter_eq_of_span_eq`). -/
noncomputable def extensionTameCharacter [Algebra.IsSeparable K L] :
    ↥(ramificationGroup K (extensionIntegers K L) 0) →*
      (ResidueField ↥(extensionIntegers K L))ˣ :=
  tameCharacterOfIrreducible K
    (IsDiscreteValuationRing.exists_irreducible ↥(extensionIntegers K L)).choose
    (IsDiscreteValuationRing.exists_irreducible ↥(extensionIntegers K L)).choose_spec

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms algebraMap_mem_extensionIntegers_iff
#print axioms maximalIdeal_extensionIntegers_ne_bot
#print axioms isDiscreteValuationRing_extensionIntegers
#print axioms exists_uniformizer_extensionIntegers
#print axioms extensionTameCharacter

end Anabelian
