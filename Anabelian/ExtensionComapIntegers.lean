/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionMonogenicDischarge
import Anabelian.TameInjectivity
import Mathlib

/-!
# Toward Serre IV §1 Prop. 3: `𝒪_L ∩ K' = 𝒪_{K'}`, and the coefficient telescoping (Pass 57)

Prop. 3's direction (i) needs: every coefficient displacement `σ̄c − c` (for `c` in the
subextension's integers) is divisible by `a := σ̄y − y`, and `addVal (σ̄y − y)` **is**
`i_{K'/K}(σ̄)`. Both statements live on `B := 𝒪_L ∩ K' = (extensionIntegers K L).comap
(algebraMap K' L)` — the ring Pass 55's polynomial coefficients inhabit — while the generator
technology (Pass 54) lives on `𝒪_{K'} = extensionIntegers K K'`. This pass closes that gap:

* **the identification** `𝒪_L ∩ K' = 𝒪_{K'}` (`extensionIntegers_comap_eq`) — integrality of
  a `K'`-element over `𝒪_K` is the same tested in `K'` or in `L`
  (`isIntegral_algebraMap_iff` along the injective `K' ↪ L`); with the induced ring iso, the
  DVR structure, the base map `𝒪_K → B`, and Pass 54's **generator transported to `B`**;
* **the payoff** (`exists_generator_comap_spec`): a single `y ∈ B` with
  (1) `B = 𝒪_K[y]` (generation), (2) **`(σ̄y − y) ∣ (σ̄c − c)` for every `σ̄ ∈ D(B)` and
  every `c ∈ B`** — Serre's coefficient telescoping, the arithmetic half of direction (i)
  (Pass 25's engine, its hypotheses now theorems), and (3) **`i_{K'/K}(σ̄) = addVal_B (σ̄y −
  y)`** for every `σ̄` — the left side of Prop. 3's sum formula in concrete form (Pass 53's
  identification, its hypotheses now theorems at `B`).

## What is proved (all axiom-free)

* `extensionIntegers_comap_eq` — **`𝒪_L ∩ K' = 𝒪_{K'}`** (as valuation subrings of `K'`):
  the tower form of Pass 43's canonicity, at the `comap` level Pass 50–56 statements use.
* `comapIntegersEquiv` — the induced ring iso `↥𝒪_{K'} ≃+* ↥B` (value-preserving);
  `isDiscreteValuationRing_comap` — `B` is a DVR (transport along the iso).
* `baseToComapRingHom : 𝒪_K →+* B` (+ `coe_baseToComapRingHom`, `rfl`), and
  `comapIntegersEquiv_comp_extensionAlgebraMap` — the iso carries the `(K,K')` base map to it.
* `exists_generator_comap` — **`B` is monogenic over `𝒪_K`** (Pass 54 transported:
  `Subring.closure` commutes with the iso via `RingHom.map_closure`).
* `smul_baseToComapRingHom_range_eq` — decomposition elements fix the base range pointwise
  (`AlgEquiv.commutes`).
* **`exists_generator_comap_spec`** — the headline bundle (generator + telescoping +
  `lowerIndex = addVal`), described above.

## Honesty

Structure of a tower of given fields — **no reach toward R1–R3**; nothing recovered from an
abstract group. This closes the `𝒪_{K'}`-vs-`B` transport flagged in Pass 56's handoff and
delivers direction (i)'s *arithmetic* half; what remains of direction (i) is the *evaluation*
half — applying the telescoping to Pass 55's descended coefficients and evaluating at `x` via
Pass 56's lift-set identity — and then direction (ii) and the `addVal` bookkeeping. No new
`structure`/`class` (`comapIntegersEquiv`/`baseToComapRingHom` are `def`s of an equiv/hom);
no owed witness; D1 N/A; D2 stays inside the Pass-29 proofs.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L]

/-- **`𝒪_L ∩ K' = 𝒪_{K'}`**: comapping the integral closure of `𝒪_K` in `L` to the
intermediate field recovers the integral closure of `𝒪_K` in `K'` — integrality of a
`K'`-element over `𝒪_K` is insensitive to testing it in `K'` or in `L`
(`isIntegral_algebraMap_iff` along the injective `K' ↪ L`). The `comap`-level form of Pass
43's base-independence, connecting the Pass 50–56 quotient theory (stated on `comap`) to the
Pass 29+ generator technology (stated on `extensionIntegers K K'`). -/
theorem extensionIntegers_comap_eq :
    (extensionIntegers K L).comap (algebraMap K' L) = extensionIntegers K K' := by
  refine SetLike.ext fun c => ?_
  rw [mem_comap, mem_extensionIntegers_iff, mem_extensionIntegers_iff]
  exact isIntegral_algebraMap_iff ((algebraMap K' L).injective)

/-- The value-preserving ring iso `↥𝒪_{K'} ≃+* ↥(𝒪_L ∩ K')` induced by
`extensionIntegers_comap_eq`. -/
noncomputable def comapIntegersEquiv :
    ↥(extensionIntegers K K') ≃+* ↥((extensionIntegers K L).comap (algebraMap K' L)) where
  toFun x := ⟨x.1, (extensionIntegers_comap_eq K K' (L := L)).symm ▸ x.2⟩
  invFun x := ⟨x.1, (extensionIntegers_comap_eq K K' (L := L)) ▸ x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- `𝒪_L ∩ K'` is a **discrete valuation ring** (transported from Pass 35's DVR structure on
`𝒪_{K'}` along the iso). -/
instance isDiscreteValuationRing_comap [Algebra.IsSeparable K K'] :
    IsDiscreteValuationRing ↥((extensionIntegers K L).comap (algebraMap K' L)) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (comapIntegersEquiv K K' (L := L))

/-- The base ring map `𝒪_K →+* 𝒪_L ∩ K'` (through `algebraMap K K'`). -/
noncomputable def baseToComapRingHom :
    ↥𝒪[K] →+* ↥((extensionIntegers K L).comap (algebraMap K' L)) where
  toFun c := ⟨algebraMap K K' c,
    (extensionIntegers_comap_eq K K' (L := L)).symm ▸ (extensionAlgebraMap K K' c).2⟩
  map_one' := Subtype.ext (map_one (algebraMap K K'))
  map_mul' x y := Subtype.ext (map_mul (algebraMap K K') x.1 y.1)
  map_zero' := Subtype.ext (map_zero (algebraMap K K'))
  map_add' x y := Subtype.ext (map_add (algebraMap K K') x.1 y.1)

@[simp] theorem coe_baseToComapRingHom (c : ↥𝒪[K]) :
    ((baseToComapRingHom K K' (L := L) c :
      ↥((extensionIntegers K L).comap (algebraMap K' L))) : K')
      = algebraMap K K' c := rfl

/-- The iso carries the `(K, K')` base map (Pass 29's `extensionAlgebraMap`) to
`baseToComapRingHom` — both are `c ↦ algebraMap K K' c` on underlying values. -/
theorem comapIntegersEquiv_comp_extensionAlgebraMap :
    ((comapIntegersEquiv K K' (L := L) : _ ≃+* _) : _ →+* _).comp
        (extensionAlgebraMap K K')
      = baseToComapRingHom K K' (L := L) := by
  refine RingHom.ext fun c => ?_
  apply Subtype.ext
  change ((extensionAlgebraMap K K' c : ↥(extensionIntegers K K')) : K')
    = algebraMap K K' c
  rw [coe_extensionAlgebraMap]

/-- **`𝒪_L ∩ K'` is monogenic over `𝒪_K`**: Pass 54's generator of `𝒪_{K'}` transported
along the iso (`Subring.closure` commutes with ring homs, and the iso matches the two base
maps). -/
theorem exists_generator_comap [Algebra.IsSeparable K K'] :
    ∃ y : ↥((extensionIntegers K L).comap (algebraMap K' L)),
      Subring.closure
        (((baseToComapRingHom K K' (L := L)).range :
            Set ↥((extensionIntegers K L).comap (algebraMap K' L))) ∪ {y}) = ⊤ := by
  obtain ⟨x, hx⟩ := exists_generator_extensionIntegers K K'
  set e := comapIntegersEquiv K K' (L := L) with he
  refine ⟨e x, ?_⟩
  have himg : ⇑(RingEquiv.toRingHom e) ''
      (((extensionAlgebraMap K K').range : Set ↥(extensionIntegers K K')) ∪ {x})
      = ((baseToComapRingHom K K' (L := L)).range :
          Set ↥((extensionIntegers K L).comap (algebraMap K' L))) ∪ {e x} := by
    rw [Set.image_union, Set.image_singleton]
    congr 1
    rw [RingHom.coe_range, RingHom.coe_range, ← Set.range_comp]
    rw [← comapIntegersEquiv_comp_extensionAlgebraMap K K' (L := L)]
    rfl
  have hmap := (RingEquiv.toRingHom e).map_closure
    (((extensionAlgebraMap K K').range : Set ↥(extensionIntegers K K')) ∪ {x})
  rw [himg] at hmap
  rw [← hmap, hx]
  ext z
  simp only [Subring.mem_top, iff_true]
  exact Subring.mem_map.mpr ⟨e.symm z, Subring.mem_top _, e.apply_symm_apply z⟩

/-- Decomposition elements of `𝒪_L ∩ K'` fix the base range pointwise (`K`-algebra
automorphisms fix `algebraMap K K'`-images) — the `hfix` of the telescoping, free. -/
theorem smul_baseToComapRingHom_range_eq
    (σ : ((extensionIntegers K L).comap (algebraMap K' L)).decompositionSubgroup K)
    (a : ↥((extensionIntegers K L).comap (algebraMap K' L)))
    (ha : a ∈ (baseToComapRingHom K K' (L := L)).range) : σ • a = a := by
  obtain ⟨c, rfl⟩ := ha
  apply Subtype.ext
  exact AlgEquiv.commutes σ.1 (c : K)

/-- **The Prop.-3 generator package at `B = 𝒪_L ∩ K'`** (the headline): a single `y` with

1. **generation** — `B = 𝒪_K[y]`;
2. **the coefficient telescoping** (Serre IV §1, direction (i)'s arithmetic half) —
   `(σ̄y − y) ∣ (σ̄c − c)` for every `σ̄ ∈ D(B)` and every `c ∈ B` (Pass 25's engine, its
   `hgen`/`hfix` hypotheses now theorems);
3. **the concrete `i_{K'/K}`** — `lowerIndex K B σ̄ = addVal_B (σ̄y − y)` for every `σ̄`
   (Pass 53's identification, hypothesis-free at `B`) — the left side of Prop. 3's sum
   formula. -/
theorem exists_generator_comap_spec [Algebra.IsSeparable K K'] :
    ∃ y : ↥((extensionIntegers K L).comap (algebraMap K' L)),
      Subring.closure
          (((baseToComapRingHom K K' (L := L)).range :
              Set ↥((extensionIntegers K L).comap (algebraMap K' L))) ∪ {y}) = ⊤
        ∧ (∀ (σ : ((extensionIntegers K L).comap (algebraMap K' L)).decompositionSubgroup K)
            (c : ↥((extensionIntegers K L).comap (algebraMap K' L))),
            (σ • y - y) ∣ (σ • c - c))
        ∧ ∀ σ : ((extensionIntegers K L).comap (algebraMap K' L)).decompositionSubgroup K,
            lowerIndex K ((extensionIntegers K L).comap (algebraMap K' L)) σ
              = IsDiscreteValuationRing.addVal
                  ↥((extensionIntegers K L).comap (algebraMap K' L)) (σ • y - y) := by
  obtain ⟨y, hy⟩ := exists_generator_comap K K' (L := L)
  refine ⟨y, hy, fun σ c => ?_, fun σ => ?_⟩
  · refine smul_sub_dvd_of_mem_closure K
      (fun a ha => smul_baseToComapRingHom_range_eq K K' σ a ha) ?_
    rw [hy]
    exact Subring.mem_top c
  · exact lowerIndex_eq_addVal K _ hy
      (fun a ha => smul_baseToComapRingHom_range_eq K K' σ a ha)

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms extensionIntegers_comap_eq
#print axioms comapIntegersEquiv
#print axioms isDiscreteValuationRing_comap
#print axioms baseToComapRingHom
#print axioms coe_baseToComapRingHom
#print axioms comapIntegersEquiv_comp_extensionAlgebraMap
#print axioms exists_generator_comap
#print axioms smul_baseToComapRingHom_range_eq
#print axioms exists_generator_comap_spec

end Anabelian
