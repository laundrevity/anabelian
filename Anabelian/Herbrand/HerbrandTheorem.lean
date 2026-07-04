/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Herbrand.Transitivity
import Anabelian.Herbrand.UpperNumbering
import Mathlib

/-!
# HERBRAND'S THEOREM: `(G/H)^v = G^v H/H` (Pass 77)

**Serre IV §3 Proposition 14 — the upper numbering is compatible with quotients — is a
theorem.** For a tower `K ⊆ K' ⊆ L` of finite extensions of a nonarchimedean local field
(`L/K`, `K'/K` normal, `L/K'` Galois) and **every** `v : ℝ`:

> **`(upperRamificationGroup K (𝒪_L) v).map (decompositionQuotient)
>    = upperRamificationGroup K (𝒪_L ∩ K') v`**
> (`map_upperRamificationGroup_eq`)

This is the theorem the whole quotient arc (Passes 50–77) was aimed at: the reason the
upper numbering exists (Pass 45's `G^v = G_{⌈ψ(v)⌉}`) is exactly that it passes to
quotients — the property that lets ramification data glue across the infinite tower toward
`Gal(K̄/K)`, and the engine of the Hasse–Arf theorem and local class field theory's
ramification correspondence.

The proof is three bricks on top of the arc:

* **`herbrandPhi_herbrandPsi_eq`** — `φ_{L/K'}(ψ_{L/K}(v)) = ψ_{K'/K}(v)`: Prop. 15
  (Pass 76) evaluated at `ψ_{L/K}(v)`, inverted through `ψ_{K'/K}`.
* **`ramificationGroup_comap_ceil_collapse`** — `(G/H)_{⌈φ(⌈x⌉)⌉} = (G/H)_{⌈φ(x)⌉}`: not
  an integer identity (the two indices can differ!) but a group equality — both indices
  land in Pass 75's alignment window, where the quotient filtration is constant.
* **`map_upperRamificationGroup_eq`** — unfold `G^v = G_{⌈ψ(v)⌉}` (Pass 45), apply Lemma 5
  at `u = ⌈ψ_{L/K}(v)⌉` (Pass 73), rewrite by the `ψ`-composition, close by the
  ceil-collapse.

## Honesty

Quotient-compatibility for a **given** tower — **no reach toward R1–R3**; nothing is
recovered from an abstract group. The upgrades this unlocks (upper numbering on
`Gal(K̄/K)` via the inverse limit, Hasse–Arf) are NOT claimed. No new `structure`/`class`;
no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
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

/-- **The `ψ`-composition**: `φ_{L/K'}(ψ_{L/K}(v)) = ψ_{K'/K}(v)` — Prop. 15 (Pass 76)
evaluated at `ψ_{L/K}(v)` and inverted through `ψ_{K'/K}` (the Pass 45 inverse
identities). -/
theorem herbrandPhi_herbrandPsi_eq (v : ℝ) :
    herbrandPhi K' (extensionIntegers K L)
        (herbrandPsi K (extensionIntegers K L) v)
      = herbrandPsi K
          ((extensionIntegers K L).comap (algebraMap K' L)) v := by
  have h76 := herbrandPhi_comp K K' (L := L)
    (herbrandPsi K (extensionIntegers K L) v)
  rw [herbrandPhi_psi K (extensionIntegers K L) v] at h76
  have h2 := congrArg
    (herbrandPsi K ((extensionIntegers K L).comap (algebraMap K' L)))
    h76
  rw [herbrandPsi_phi K
    ((extensionIntegers K L).comap (algebraMap K' L))] at h2
  exact h2.symm

/-- **The ceil-collapse**: `(G/H)_{⌈φ(⌈x⌉)⌉} = (G/H)_{⌈φ(x)⌉}`. NOT an integer identity —
`⌈φ(⌈x⌉)⌉` and `⌈φ(x)⌉` can genuinely differ — but a GROUP equality: for non-integral `x`
both indices land in the alignment window `(φ(⌊x⌋), ⌈φ(⌊x⌋+1)⌉]`, where the quotient
filtration is constant (Pass 75). -/
theorem ramificationGroup_comap_ceil_collapse (x : ℝ) :
    ramificationGroup K
        ((extensionIntegers K L).comap (algebraMap K' L))
        ⌈herbrandPhi K' (extensionIntegers K L) ((⌈x⌉₊ : ℕ) : ℝ)⌉₊
      = ramificationGroup K
          ((extensionIntegers K L).comap (algebraMap K' L))
          ⌈herbrandPhi K' (extensionIntegers K L) x⌉₊ := by
  rcases le_or_gt x 0 with hx0 | hx0
  · -- x ≤ 0: both indices are 0
    have h1 : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.mpr hx0
    have h2 : herbrandPhi K' (extensionIntegers K L) x = x :=
      herbrandPhi_eq_id K' (extensionIntegers K L) hx0
    rw [h1, h2, Nat.cast_zero, herbrandPhi_zero, Nat.ceil_eq_zero.mpr hx0,
        Nat.ceil_zero]
  · rcases eq_or_ne ((⌈x⌉₊ : ℕ) : ℝ) x with hint | hne
    · rw [hint]
    · -- x non-integral: ⌈x⌉ = ⌊x⌋ + 1 and P75's alignment applies
      set n := ⌊x⌋₊ with hn
      have hnx : (n : ℝ) ≤ x := Nat.floor_le (le_of_lt hx0)
      have hxlt : x < ((n + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one x
      have hnlt : (n : ℝ) < x := by
        rcases lt_or_eq_of_le hnx with h | h
        · exact h
        · exact absurd (by rw [← h, Nat.ceil_natCast]) hne
      have hceil : ⌈x⌉₊ = n + 1 := by
        refine le_antisymm (Nat.ceil_le.mpr (le_of_lt hxlt)) ?_
        by_contra hcon
        push Not at hcon
        have h5 : ⌈x⌉₊ ≤ n := by omega
        have h6 : x ≤ (n : ℝ) :=
          le_trans (Nat.le_ceil x) (by exact_mod_cast h5)
        linarith
      have hw : herbrandPhi K' (extensionIntegers K L) (n : ℝ)
          < (⌈herbrandPhi K' (extensionIntegers K L) x⌉₊ : ℝ) :=
        lt_of_lt_of_le
          (herbrandPhi_strictMono K' (extensionIntegers K L) hnlt)
          (Nat.le_ceil _)
      have hw' : ⌈herbrandPhi K' (extensionIntegers K L) x⌉₊
          ≤ ⌈herbrandPhi K' (extensionIntegers K L)
              ((n + 1 : ℕ) : ℝ)⌉₊ :=
        Nat.ceil_le_ceil
          (herbrandPhi_monotone K' (extensionIntegers K L)
            (le_of_lt hxlt))
      have h75 := ramificationGroup_comap_eq_of_lt K K' (L := L) hw hw'
      rw [hceil]
      exact h75.symm

/-- **HERBRAND'S THEOREM** (Serre, *Local Fields*, IV §3, Prop. 14): for the tower
`K ⊆ K' ⊆ L` and EVERY `v : ℝ`,

`(G^v).map (decompositionQuotient) = (G/H)^v`

— **the upper numbering is compatible with quotients**. Three rewrites: the definition
`G^v = G_{⌈ψ(v)⌉}` (Pass 45), Lemma 5 at `u = ⌈ψ_{L/K}(v)⌉` (Pass 73), the
`ψ`-composition (Prop. 15, Pass 76), and the ceil-collapse (Pass 75's alignment). -/
theorem map_upperRamificationGroup_eq (v : ℝ) :
    (upperRamificationGroup K (extensionIntegers K L) v).map
        (decompositionQuotient K K' (extensionIntegers K L))
      = upperRamificationGroup K
          ((extensionIntegers K L).comap (algebraMap K' L)) v := by
  unfold upperRamificationGroup
  rw [map_ramificationGroup_eq_ceil K K'
    ⌈herbrandPsi K (extensionIntegers K L) v⌉₊]
  rw [← herbrandPhi_herbrandPsi_eq K K' (L := L) v]
  exact ramificationGroup_comap_ceil_collapse K K'
    (herbrandPsi K (extensionIntegers K L) v)


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms herbrandPhi_herbrandPsi_eq
#print axioms ramificationGroup_comap_ceil_collapse
#print axioms map_upperRamificationGroup_eq

end Anabelian
