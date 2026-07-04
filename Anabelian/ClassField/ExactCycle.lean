/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.HerbrandQuotient
import Mathlib

/-!
# L3.1: the exact-cycle count and `herbrandH` functoriality (Pass 88)

Two sub-bricks toward the Herbrand quotient's multiplicativity in short exact sequences
(Serre VIII §4 Prop. 10) — the route chosen at Pass 87: the direct six-term construction,
whose counting core is proved here in full generality.

* **`card_prod_eq_of_exact_cycle`** — the 6-cycle alternating-card lemma: a periodic
  exact sequence `A₀ → ⋯ → A₅ → A₀` has `|A₀||A₂||A₄| = |A₁||A₃||A₅|`. Pure group theory,
  no finiteness needed (the `Nat.card` conventions), reusable anywhere a bounded exact
  cycle is counted. Applied to the six-term Herbrand cohomology cycle of a short exact
  sequence, it IS the multiplicativity `q(M) = q(M')·q(M'')` — once that cycle is built.
* **`herbrandHMap`** — functoriality of the Herbrand cohomology carrier: a
  pair-intertwining `φ : M →* N` induces `herbrandH f_M g_M →* herbrandH f_N g_N`. The
  four functorial maps of the six-term cycle are instances of this; the two CONNECTING
  maps (`Ĥ⁰(M'') → Ĥ¹(M')` and its periodic partner — the snake) are the remaining
  construction, next pass.
* `card_eq_card_ker_mul_card_range'` — the cross-hom first-isomorphism count (Pass 87's
  endo version, generalized).

## Honesty

Pure group-theoretic infrastructure — **no reach toward R1–R3**, and not yet the
multiplicativity theorem itself (the connecting maps and the six exactness proofs
remain — named as the next pass's work, not glossed). No new `structure`/`class`; no owed
witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian


section ExactCycle

/-- The first-isomorphism counting for a hom between different groups:
`|G| = |ker f| · |im f|` (generalizes Pass 87's endomorphism version; holds without
finiteness by the `Nat.card = 0` conventions). -/
theorem card_eq_card_ker_mul_card_range' {G H : Type*} [Group G] [Group H] (f : G →* H) :
    Nat.card G = Nat.card f.ker * Nat.card f.range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [h1, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  ring

variable {A0 A1 A2 A3 A4 A5 : Type*}
  [Group A0] [Group A1] [Group A2] [Group A3] [Group A4] [Group A5]

/-- **THE 6-CYCLE ALTERNATING-CARD LEMMA**: for a periodic exact sequence
`A₀ → A₁ → A₂ → A₃ → A₄ → A₅ → A₀` (exact at every node),

`|A₀|·|A₂|·|A₄| = |A₁|·|A₃|·|A₅|`.

Each `|Aᵢ| = |im dᵢ₋₁|·|im dᵢ|` (first isomorphism + exactness), and the two triple
products each collect all six ranges once. NO finiteness hypotheses — the `Nat.card = 0`
conventions make both sides vanish together when anything is infinite. This is the
counting engine of the Herbrand-quotient multiplicativity: applied to the six-term
`Ĥ⁰(M') → Ĥ⁰(M) → Ĥ⁰(M'') → Ĥ¹(M') → Ĥ¹(M) → Ĥ¹(M'')` cycle of a short exact sequence,
it IS `q(M) = q(M')·q(M'')` after division. -/
theorem card_prod_eq_of_exact_cycle
    (d0 : A0 →* A1) (d1 : A1 →* A2) (d2 : A2 →* A3)
    (d3 : A3 →* A4) (d4 : A4 →* A5) (d5 : A5 →* A0)
    (h01 : d0.range = d1.ker) (h12 : d1.range = d2.ker) (h23 : d2.range = d3.ker)
    (h34 : d3.range = d4.ker) (h45 : d4.range = d5.ker) (h50 : d5.range = d0.ker) :
    Nat.card A0 * Nat.card A2 * Nat.card A4
      = Nat.card A1 * Nat.card A3 * Nat.card A5 := by
  have e0 : Nat.card A0 = Nat.card d5.range * Nat.card d0.range := by
    rw [card_eq_card_ker_mul_card_range' d0, ← h50]
  have e1 : Nat.card A1 = Nat.card d0.range * Nat.card d1.range := by
    rw [card_eq_card_ker_mul_card_range' d1, ← h01]
  have e2 : Nat.card A2 = Nat.card d1.range * Nat.card d2.range := by
    rw [card_eq_card_ker_mul_card_range' d2, ← h12]
  have e3 : Nat.card A3 = Nat.card d2.range * Nat.card d3.range := by
    rw [card_eq_card_ker_mul_card_range' d3, ← h23]
  have e4 : Nat.card A4 = Nat.card d3.range * Nat.card d4.range := by
    rw [card_eq_card_ker_mul_card_range' d4, ← h34]
  have e5 : Nat.card A5 = Nat.card d4.range * Nat.card d5.range := by
    rw [card_eq_card_ker_mul_card_range' d5, ← h45]
  rw [e0, e1, e2, e3, e4, e5]
  ring

end ExactCycle

section Functoriality

variable {M N : Type*} [CommGroup M] [CommGroup N]
variable (fM gM : M →* M) (fN gN : N →* N)
variable (φ : M →* N)

/-- A pair-intertwining hom restricts to the kernels. -/
def kerRestrict (hf : ∀ x, φ (fM x) = fN (φ x)) : fM.ker →* fN.ker where
  toFun x := ⟨φ x.1, by
    have hx : fM x.1 = 1 := MonoidHom.mem_ker.mp x.2
    rw [MonoidHom.mem_ker, ← hf x.1, hx, map_one]⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp

/-- **Functoriality of `herbrandH`**: a hom `φ : M →* N` intertwining the pairs induces
`herbrandH f_M g_M →* herbrandH f_N g_N` (restrict to kernels, descend to the quotient).
The building block of the six-term sequence: the maps `Ĥ(M') → Ĥ(M) → Ĥ(M'')` of a short
exact sequence are instances; the connecting map `δ` is the remaining (snake) piece. -/
noncomputable def herbrandHMap (hf : ∀ x, φ (fM x) = fN (φ x))
    (hg : ∀ x, φ (gM x) = gN (φ x)) :
    Anabelian.herbrandH fM gM →* Anabelian.herbrandH fN gN :=
  QuotientGroup.map _ _ (kerRestrict fM fN φ hf) (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    obtain ⟨y, hy⟩ := hx
    exact ⟨φ y, by rw [← hg y, hy]; rfl⟩)

end Functoriality


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms card_eq_card_ker_mul_card_range'
#print axioms card_prod_eq_of_exact_cycle
#print axioms kerRestrict
#print axioms herbrandHMap

end Anabelian
