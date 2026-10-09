/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Quotient.Alignment
import Anabelian.Quotient.CardMultiplicativity
import Anabelian.Herbrand.Formula
import Anabelian.Herbrand.Slope
import Mathlib

/-!
# PROP. 15: `φ`-TRANSITIVITY — `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` (Pass 76)

**Serre IV §3 Proposition 15 is a theorem.** For a tower `K ⊆ K' ⊆ L` of finite extensions
of a nonarchimedean local field (`L/K`, `K'/K` normal, `L/K'` Galois) and **every** `u : ℝ`:

> **`φ_{L/K}(u) = φ_{K'/K}(φ_{L/K'}(u))`** (`herbrandPhi_comp`)

The four-step plan of Pass 75's HANDOFF, executed in one pass:

1. **`herbrandPhi_hasDerivWithinAt_Ici`** — `φ` has right derivative `|G_{⌊u⌋+1}|/|G_0|` at
   every `u ≥ 0` (breakpoints included): Pass 48's affine formula on `[⌊u⌋, ⌊u⌋+1]`,
   transferred to the `Ici`-derivative by eventual equality on `𝓝[Ici u] u`.
2. The **chain rule** for right derivatives along the monotone inner function
   (`HasDerivWithinAt.comp` + `MapsTo` from Pass 44's monotonicity).
3. **`slope_match`** — the chain-rule product equals `φ_{L/K}`'s right slope: the
   **alignment lemma** (Pass 75) turns the outer index `⌊φ_{L/K'}(u)⌋+1` into
   `⌈φ_{L/K'}(⌊u⌋+1)⌉`, and the **card multiplicativity** (Pass 74, at `⌊u⌋+1` and `0`)
   collapses the product.
4. The **glue**: `eq_of_has_deriv_right_eq` on `[0, u]` — continuity (Pass 44), equal at
   `0` (`φ(0) = 0`), same right derivative everywhere. `u ≤ 0` is free (`φ = id`, Pass 44).

With Prop. 15, **Herbrand's theorem** (Prop. 14: `(G/H)^v = G^v H/H`) is next — Lemma 5
(Pass 73) read through the upper numbering (Pass 45) via the `ψ`-composition corollary.

## Honesty

The transitivity of the Herbrand function for a **given** tower — **no reach toward
R1–R3**; nothing recovered from an abstract group. Prop. 14 is NOT claimed — next pass. No
new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


section RightDeriv

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [Finite (A.decompositionSubgroup K)]

/-- **The right derivative of `φ` at every `u ≥ 0`** is `|G_{⌊u⌋+1}|/|G_0|` — including at
the integer breakpoints, where the two-sided derivative (Pass 47) fails. From Pass 48's
affine formula on `[⌊u⌋, ⌊u⌋+1]`, transferred by eventual equality on `𝓝[Ici u] u`. -/
theorem herbrandPhi_hasDerivWithinAt_Ici {u : ℝ} (hu : 0 ≤ u) :
    HasDerivWithinAt (herbrandPhi K A)
      (ramificationOrders K A (⌊u⌋₊ + 1) / ramificationOrders K A 0)
      (Ici u) u := by
  set n := ⌊u⌋₊ with hn
  have hun : (n : ℝ) ≤ u := Nat.floor_le hu
  have hu1 : u < (n : ℝ) + 1 := Nat.lt_floor_add_one u
  set s := ramificationOrders K A (n + 1) / ramificationOrders K A 0
    with hs
  set c := (∑ i ∈ Finset.range n, ramificationOrders K A (i + 1))
      / ramificationOrders K A 0 with hc
  -- the affine model
  have haff : HasDerivAt (fun x : ℝ => c + (x - (n : ℝ)) * s) s u := by
    simpa using (((hasDerivAt_id u).sub_const (n : ℝ)).mul_const s).const_add c
  -- φ agrees with the affine model near u within Ici u
  have hagree : ∀ x : ℝ, x ∈ Icc (n : ℝ) ((n : ℝ) + 1)
      → herbrandPhi K A x = c + (x - (n : ℝ)) * s := by
    intro x hx
    rw [herbrandPhi_eq_affine_formula K A hx, hc, hs]
    ring
  have hev : (fun x : ℝ => herbrandPhi K A x)
      =ᶠ[nhdsWithin u (Ici u)] (fun x : ℝ => c + (x - (n : ℝ)) * s) := by
    have h1 : Iio ((n : ℝ) + 1) ∈ nhdsWithin u (Ici u) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hu1)
    have h2 : Ici u ∈ nhdsWithin u (Ici u) := self_mem_nhdsWithin
    filter_upwards [h1, h2] with x hx1 hx2
    exact hagree x ⟨le_trans hun hx2, le_of_lt hx1⟩
  exact (haff.hasDerivWithinAt.congr_of_eventuallyEq hev
    (hagree u ⟨hun, le_of_lt hu1⟩))

end RightDeriv

section Transitivity

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (K' : Type*) [Field K'] [Algebra K K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] [Normal K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Normal K L]
variable [FiniteDimensional K' L] [IsGalois K' L]

/-- **The slope match**: the right-slope of the composite `φ_{K'/K} ∘ φ_{L/K'}` at `u ≥ 0`
equals `φ_{L/K}`'s. The chain-rule product collapses by the alignment lemma (Pass 75 turns
the outer index `⌊φ(u)⌋+1` into `⌈φ(⌊u⌋+1)⌉`) and the card multiplicativity (Pass 74 at
`⌊u⌋+1` and at `0`). -/
theorem slope_match {u : ℝ} (hu : 0 ≤ u) :
    ramificationOrders K
        ((extensionIntegers K L).comap (algebraMap K' L))
        (⌊herbrandPhi K' (extensionIntegers K L) u⌋₊ + 1)
      / ramificationOrders K
          ((extensionIntegers K L).comap (algebraMap K' L)) 0
      * (ramificationOrders K' (extensionIntegers K L) (⌊u⌋₊ + 1)
        / ramificationOrders K' (extensionIntegers K L) 0)
      = ramificationOrders K (extensionIntegers K L) (⌊u⌋₊ + 1)
        / ramificationOrders K (extensionIntegers K L) 0 := by
  set n := ⌊u⌋₊ with hn
  have hun : (n : ℝ) ≤ u := Nat.floor_le hu
  have hu1 : u < ((n + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one u
  -- P75: the (G/H)-index aligns to ⌈φ(n+1)⌉
  have halign := ramificationGroup_comap_floor_add_one_eq K K' (L := L) hun hu1
  have halignOrd : ramificationOrders K
      ((extensionIntegers K L).comap (algebraMap K' L))
      (⌊herbrandPhi K' (extensionIntegers K L) u⌋₊ + 1)
      = ramificationOrders K
          ((extensionIntegers K L).comap (algebraMap K' L))
          ⌈herbrandPhi K' (extensionIntegers K L)
            ((n + 1 : ℕ) : ℝ)⌉₊ := by
    unfold ramificationOrders
    rw [halign]
  rw [halignOrd]
  -- P74 at n+1 and at 0, in ℝ
  have h74 := card_ramificationGroup_eq_mul K K' (L := L) (n + 1)
  have h740 := card_ramificationGroup_zero_eq_mul K K' (L := L)
  have h74R : ramificationOrders K (extensionIntegers K L) (n + 1)
      = ramificationOrders K
          ((extensionIntegers K L).comap (algebraMap K' L))
          ⌈herbrandPhi K' (extensionIntegers K L)
            ((n + 1 : ℕ) : ℝ)⌉₊
        * ramificationOrders K' (extensionIntegers K L) (n + 1) := by
    unfold ramificationOrders
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h74
  have h740R : ramificationOrders K (extensionIntegers K L) 0
      = ramificationOrders K
          ((extensionIntegers K L).comap (algebraMap K' L)) 0
        * ramificationOrders K' (extensionIntegers K L) 0 := by
    unfold ramificationOrders
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h740
  rw [h74R, h740R]
  have hB0 : ramificationOrders K
      ((extensionIntegers K L).comap (algebraMap K' L)) 0 ≠ 0 :=
    ne_of_gt (ramificationOrders_pos K _ 0)
  have hH0 : ramificationOrders K' (extensionIntegers K L) 0 ≠ 0 :=
    ne_of_gt (ramificationOrders_pos K' _ 0)
  field_simp

/-- **PROP. 15 (Serre IV §3): `φ`-TRANSITIVITY** — for the tower `K ⊆ K' ⊆ L` and EVERY
real `u`:

`φ_{L/K}(u) = φ_{K'/K}(φ_{L/K'}(u))`.

For `u ≤ 0` all three are the identity (Pass 44). For `u > 0`: both sides are continuous on
`[0, u]` (Pass 44), agree at `0`, and have the SAME right derivative everywhere on `[0, u)`
(the two bricks above) — `eq_of_has_deriv_right_eq` closes. -/
theorem herbrandPhi_comp (u : ℝ) :
    herbrandPhi K (extensionIntegers K L) u
      = herbrandPhi K ((extensionIntegers K L).comap (algebraMap K' L))
          (herbrandPhi K' (extensionIntegers K L) u) := by
  rcases le_or_gt u 0 with hu0 | hu0
  · -- u ≤ 0: all three φ's are the identity
    rw [herbrandPhi_eq_id K' (extensionIntegers K L) hu0,
        herbrandPhi_eq_id K (extensionIntegers K L) hu0,
        herbrandPhi_eq_id K
          ((extensionIntegers K L).comap (algebraMap K' L)) hu0]
  · -- u > 0: right-derivative gluing on [0, u]
    have hmono := herbrandPhi_monotone K' (extensionIntegers K L)
    have key := eq_of_has_deriv_right_eq (a := (0 : ℝ)) (b := u)
      (f := herbrandPhi K (extensionIntegers K L))
      (g := fun x => herbrandPhi K
        ((extensionIntegers K L).comap (algebraMap K' L))
        (herbrandPhi K' (extensionIntegers K L) x))
      (f' := fun x => ramificationOrders K (extensionIntegers K L)
        (⌊x⌋₊ + 1) / ramificationOrders K (extensionIntegers K L) 0)
      ?_ ?_ ?_ ?_ ?_
    · exact key u ⟨le_of_lt hu0, le_refl u⟩
    · -- right derivative of φ_{L/K}
      intro x hx
      exact herbrandPhi_hasDerivWithinAt_Ici K (extensionIntegers K L) hx.1
    · -- right derivative of the composite
      intro x hx
      have hφx0 : (0 : ℝ) ≤ herbrandPhi K' (extensionIntegers K L) x := by
        rw [← herbrandPhi_zero K' (extensionIntegers K L)]
        exact hmono hx.1
      have houter := herbrandPhi_hasDerivWithinAt_Ici K
        ((extensionIntegers K L).comap (algebraMap K' L)) hφx0
      have hinner := herbrandPhi_hasDerivWithinAt_Ici K'
        (extensionIntegers K L) hx.1
      have hmaps : MapsTo (herbrandPhi K' (extensionIntegers K L))
          (Ici x)
          (Ici (herbrandPhi K' (extensionIntegers K L) x)) :=
        fun y hy => hmono hy
      have hcomp := HasDerivWithinAt.comp x houter hinner hmaps
      change HasDerivWithinAt _
        (ramificationOrders K (extensionIntegers K L) (⌊x⌋₊ + 1)
          / ramificationOrders K (extensionIntegers K L) 0)
        (Ici x) x
      rw [← slope_match K K' (L := L) hx.1]
      exact hcomp
    · -- continuity of φ_{L/K}
      exact (herbrandPhi_continuous K (extensionIntegers K L)).continuousOn
    · -- continuity of the composite
      exact ((herbrandPhi_continuous K
        ((extensionIntegers K L).comap (algebraMap K' L))).comp
        (herbrandPhi_continuous K' (extensionIntegers K L))).continuousOn
    · -- equal at 0
      rw [herbrandPhi_zero K (extensionIntegers K L),
          herbrandPhi_zero K' (extensionIntegers K L),
          herbrandPhi_zero K
            ((extensionIntegers K L).comap (algebraMap K' L))]

end Transitivity


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms herbrandPhi_hasDerivWithinAt_Ici
#print axioms slope_match
#print axioms herbrandPhi_comp

end Anabelian
