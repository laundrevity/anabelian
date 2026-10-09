/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Ramification.AdditiveCharacter
import Anabelian.Extension.InertiaResidueCover
import Anabelian.Ramification.WildInertia

/-!
# The descent, consolidated: the P27/P28 quotient theory concrete at `𝒪_L` (Pass 37)

With the descent closed (Pass 36), every hypothesis of the abstract Passes-23–28 theory is a
theorem at `𝒪_L` in the **general** finite-separable case. This file harvests the remaining
abstract results — the Pass-27 additive-character structure and the Pass-28 wild/tame
dichotomy — as concrete theorems about local fields:

* **`closure_inertiaFixedIntegers_union_uniformizer_eq_top`** — the feeder: the general
  monogenicity theorem at `𝒪_L`. `𝒪_L` is generated (as a ring) by the inertia-fixed integers
  together with any uniformizer — Pass 34's engine + Pass 36's `hresid`, packaged once.
* **`ker_additiveCharacter_extensionIntegers`** and
  **`additiveQuotientHom_injective_extensionIntegers`** — Pass 27 concrete:
  `ker θ_i = G_{i+1}` and `G_i/G_{i+1} ↪ 𝓀_L⁺` for every `i ≥ 1`.
* **`isPGroup_wildInertia_extensionIntegers`** and
  **`not_dvd_natCard_tameQuotient_extensionIntegers`** — Pass 28 concrete:
  `G₁` is a `p`-group and `p ∤ |G₀/G₁|` — `G₁` is the normal Sylow
  `p`-subgroup of `G₀`: **the wild inertia of a finite separable extension of nonarchimedean
  local fields, with no conditional hypotheses left.**

## Honesty

No new mathematics: the content is that the abstract theory and the descent **compose with
zero residue** — every `hgen`/`hfix`/`hsep`/finiteness/`CharP` input is discharged by a named
prior theorem (P29 separation + Noetherian, P30 uniformizers, P31 `CharP` transfer — consumed
here for the first time, P34 engine, P36 cover). No `Finite`/`Fintype` hypotheses appear: the
decomposition subgroup's finiteness is an instance (P29), and subgroup finiteness synthesizes
from it. `p` enters as the residue characteristic of the BASE field `𝓀[K]`, transported to
`𝓀_L` by Pass 31. No new `structure`/`class`; no owed witness; D1 N/A; D2 N/A. Recovers
nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The general monogenicity theorem at `𝒪_L`**: the integers of any finite separable
extension are generated, as a ring, by the inertia-fixed integers together with any
uniformizer. Pass 34's generalized engine fed by Pass 36's residue cover, packaged once for
every downstream instantiation. -/
theorem closure_inertiaFixedIntegers_union_uniformizer_eq_top [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) :
    Subring.closure
        ((inertiaFixedIntegers K L : Set ↥(extensionIntegers K L)) ∪ {π}) = ⊤ := by
  obtain ⟨e, he⟩ := exists_pow_maximalIdeal_le_map K L
  exact closure_subring_union_uniformizer_eq_top K L (inertiaFixedIntegers K L)
    (extensionAlgebraMap_mem_inertiaFixedIntegers K L) π hspan
    (inertiaFixedIntegers_residue_cover K L) e he

/-- **Pass 27, concrete (kernels)**: for any finite separable `L/K` and any uniformizer,
`ker θ_i = G_{i+1}` for every `i ≥ 1` — the additive characters detect exactly the next
filtration step, on actual local fields. -/
theorem ker_additiveCharacter_extensionIntegers [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0)
    {i : ℕ} (hi : 1 ≤ i) :
    (additiveCharacter K π hspan hπ0 hi).ker
      = (ramificationGroup K (extensionIntegers K L) (i + 1)).subgroupOf
          (ramificationGroup K (extensionIntegers K L) i) :=
  ker_additiveCharacter K π hspan hπ0
    (closure_inertiaFixedIntegers_union_uniformizer_eq_top K L π hspan) hi
    (fun σ a ha => smul_inertiaFixedIntegers_eq K L
      ⟨σ.1, ramificationGroup_antitone K (extensionIntegers K L) (Nat.zero_le i) σ.2⟩ a ha)

/-- **Pass 27, concrete (embeddings)**: `G_i/G_{i+1} ↪ 𝓀_L⁺` for every `i ≥ 1` — the higher
quotients embed in the additive group of the residue field; in particular they are abelian. -/
theorem additiveQuotientHom_injective_extensionIntegers [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0)
    {i : ℕ} (hi : 1 ≤ i) :
    Function.Injective (additiveQuotientHom K π hspan hπ0 hi) :=
  additiveQuotientHom_injective K π hspan hπ0
    (closure_inertiaFixedIntegers_union_uniformizer_eq_top K L π hspan) hi
    (fun σ a ha => smul_inertiaFixedIntegers_eq K L
      ⟨σ.1, ramificationGroup_antitone K (extensionIntegers K L) (Nat.zero_le i) σ.2⟩ a ha)

/-- **Pass 28, concrete (wild side)**: `G₁` is a `p`-group, `p` the residue characteristic of
the base — the wild inertia of a finite separable extension of nonarchimedean local fields,
unconditionally. -/
theorem isPGroup_wildInertia_extensionIntegers (p : ℕ)
    [CharP (ResidueField ↥𝒪[K]) p] [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0) :
    IsPGroup p ↥(ramificationGroup K (extensionIntegers K L) 1) := by
  have := charP_residueField_extensionIntegers K L p
  have := isNoetherianRing_extensionIntegers K L
  exact isPGroup_ramificationGroup_one K p
    (Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top')
    π hspan hπ0
    (closure_inertiaFixedIntegers_union_uniformizer_eq_top K L π hspan)
    (smul_inertiaFixedIntegers_eq K L)

/-- **Pass 28, concrete (tame side)**: `p ∤ |G₀/G₁|`. With the wild side, `G₁` is the normal
Sylow `p`-subgroup of `G₀` — the wild/tame dichotomy of Serre IV §2, complete on actual local
fields with no conditional hypotheses. -/
theorem not_dvd_natCard_tameQuotient_extensionIntegers (p : ℕ) [Fact p.Prime]
    [CharP (ResidueField ↥𝒪[K]) p] [Algebra.IsSeparable K L]
    (π : ↥(extensionIntegers K L))
    (hspan : maximalIdeal ↥(extensionIntegers K L) = Ideal.span {π}) (hπ0 : π ≠ 0) :
    ¬ p ∣ Nat.card (↥(ramificationGroup K (extensionIntegers K L) 0) ⧸
      ((ramificationGroup K (extensionIntegers K L) 1).subgroupOf
        (ramificationGroup K (extensionIntegers K L) 0))) := by
  have := charP_residueField_extensionIntegers K L p
  exact not_dvd_natCard_tameQuotient K p π hspan hπ0
    (closure_inertiaFixedIntegers_union_uniformizer_eq_top K L π hspan)
    (smul_inertiaFixedIntegers_eq K L)

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms closure_inertiaFixedIntegers_union_uniformizer_eq_top
#print axioms ker_additiveCharacter_extensionIntegers
#print axioms additiveQuotientHom_injective_extensionIntegers
#print axioms isPGroup_wildInertia_extensionIntegers
#print axioms not_dvd_natCard_tameQuotient_extensionIntegers

end Anabelian
