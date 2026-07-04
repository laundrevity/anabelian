/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Herbrand.HerbrandTheorem
import Anabelian.Quotient.ComapIntegers
import Mathlib

/-!
# The Herbrand package: Serre IV §1 + §3 for towers, consolidated (Pass 78)

One-stop summary and audit for the quotient arc (Passes 50–77): the ramification theory of
a tower `K ⊆ K' ⊆ L` of finite extensions of a nonarchimedean local field (`L/K`, `K'/K`
normal, `L/K'` Galois), from the subgroup filtration up to **Herbrand's theorem**, all
axiom-free. The chain, with the pass that proved each link:

* **Prop. 2 (subgroup)** — `H_u = H ∩ G_u`: the lower filtration of `L/K'` is the
  restriction of that of `L/K` (`ramificationGroup_map_eq`, Pass 46).
* **Prop. 3 (quotient sum formula)** — `i_{K'/K}(σ̄) · e' = Σ_{s ↦ σ̄} i_{L/K}(s)`
  (`lowerIndex_decompositionQuotient_mul_eq_sum`, Passes 50–63).
* **`e' = |H₀|`** — the ramification index of `L/K'` is the inertia cardinality
  (`natCast_card_ramificationGroup_zero_eq_addVal`, Passes 68–71, on Mathlib's
  `card_inertia_eq_ramificationIdxIn`).
* **The numerical Lemma 5** — `i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1` for `σ̄ ≠ 1`
  (`exists_lowerIndex_eq_herbrandPhi`, Pass 72).
* **Lemma 5** — `(G/H)_{φ_{L/K'}(u)} = G_u H/H`, i.e. the image of `G_u` is the quotient
  filtration at `⌈φ_{L/K'}(u)⌉` (`map_ramificationGroup_eq_ceil`, Pass 73).
* **The card multiplicativity** — `|G_u| = |(G/H)_{⌈φ(u)⌉}| · |H_u|`; at `u = 0` this is
  `e_{L/K} = e_{K'/K} · e_{L/K'}` (`card_ramificationGroup_eq_mul`, Pass 74).
* **Prop. 15 (`φ`-transitivity)** — `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` on all of `ℝ`
  (`herbrandPhi_comp`, Passes 75–76).
* **Prop. 14 (HERBRAND'S THEOREM)** — `(G^v).map (decompositionQuotient) = (G/H)^v`: the
  upper numbering is compatible with quotients (`map_upperRamificationGroup_eq`, Pass 77).

This file adds the **canonical-carrier form** of Herbrand's theorem. The arc's quotient
objects live on `B = 𝒪_L ∩ K'` (the comap of `𝒪_L` along `K' ↪ L`) — definitionally
convenient, but the canonical object for `K'/K` is `𝒪_{K'} = extensionIntegers K K'`.
Pass 57 proved they are EQUAL as valuation subrings (`extensionIntegers_comap_eq`), and
both decomposition subgroups live in the common ambient group `K' ≃ₐ[K] K'` = `Gal(K'/K)`,
so the clean statement compares images there:

> **`map_upperRamificationGroup_eq_extensionIntegers`** — in `Gal(K'/K)`, the image of
> `G^v(L/K)` under restriction equals `G^v(K'/K)` computed on `𝒪_{K'}` itself.

## Honesty

A consolidation: one new corollary (transport along a proved equality) and a re-audit —
**no new mathematics, no reach toward R1–R3**. The L3 upgrades (upper numbering on
`Gal(K̄/K)`, Hasse–Arf) are NOT claimed. No new `structure`/`class`; no owed witness;
D1 N/A; D2 untouched.

## Axiom status

The `#print axioms` block below audits the ENTIRE arc's headline theorems in one place —
all standard-axioms-only. Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Normal K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **HERBRAND'S THEOREM, canonical carrier** (Serre IV §3 Prop. 14): comparing images in
the common ambient group `Gal(K'/K) = (K' ≃ₐ[K] K')`, the image of the upper ramification
group `G^v(L/K)` under the quotient restriction equals the upper ramification group
`G^v(K'/K)` computed on the canonical integers `𝒪_{K'} = extensionIntegers K K'` — the
`B`-vs-`𝒪_{K'}` carrier distinction of the arc dissolves along Pass 57's equality
`𝒪_L ∩ K' = 𝒪_{K'}`. -/
theorem map_upperRamificationGroup_eq_extensionIntegers (v : ℝ) :
    ((upperRamificationGroup K (extensionIntegers K L) v).map
        (decompositionQuotient K K' (extensionIntegers K L))).map
        (((extensionIntegers K L).comap
          (algebraMap K' L)).decompositionSubgroup K).subtype
      = (upperRamificationGroup K (extensionIntegers K K') v).map
          ((extensionIntegers K K').decompositionSubgroup K).subtype := by
  rw [map_upperRamificationGroup_eq K K' v]
  rw [extensionIntegers_comap_eq K K' (L := L)]

-- The one-stop audit of the arc's headline theorems (re-runs on every `lake build`).
-- All standard-axioms-only: [propext, Classical.choice, Quot.sound].
#print axioms ramificationGroup_map_eq                       -- Prop. 2   (Pass 46)
#print axioms lowerIndex_decompositionQuotient_mul_eq_sum    -- Prop. 3   (Pass 63)
#print axioms natCast_card_ramificationGroup_zero_eq_addVal  -- e' = |H₀| (Pass 71)
#print axioms exists_lowerIndex_eq_herbrandPhi               -- num. Lemma 5 (Pass 72)
#print axioms map_ramificationGroup_eq_ceil                  -- Lemma 5   (Pass 73)
#print axioms card_ramificationGroup_eq_mul                  -- e-mult.   (Pass 74)
#print axioms herbrandPhi_comp                               -- Prop. 15  (Pass 76)
#print axioms map_upperRamificationGroup_eq                  -- Prop. 14  (Pass 77)
#print axioms map_upperRamificationGroup_eq_extensionIntegers -- canonical (Pass 78)

end Anabelian
