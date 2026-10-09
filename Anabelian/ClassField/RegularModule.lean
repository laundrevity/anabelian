/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.CyclicPair

/-!
# L3.1: the regular module of a finite cyclic group is acyclic (Pass 96)

For a group `G` acting on functions `G → C` (`C` any commutative group) by the regular
permutation action `(g • f) h = f (g⁻¹ h)` — `regularShift g`, built from Mathlib's
`MulEquiv.arrowCongr` — and a generator `g` of a finite `G`:

> **`regular_cyclic_exact`**: `im N = ker D` and `im D = ker N`

for the cyclic pair `N = cyclicNorm (regularShift g) |G|`, `D = cyclicDiff (regularShift g)`.
This is `Ĥ⁰ = Ĥ¹ = 0` for the induced module `C[G]` — the layer input of the Pass-95
design (the layers `V_i ⧸ V_{i+1}` of the lattice unit filtration are regular modules over
the base residue field).

The computation is elementary and needs no division by `|G|`:

* the norm is the constant function `∏_{k ∈ G} f k` (`cyclicNorm_regularShift_apply`) —
  `j ↦ g ^ j` enumerates `G` exactly once for `j < |G|` (`prod_range_card_pow`);
* fixed functions are constant, and a constant `c` is the norm of `Pi.mulSingle 1 c`;
* differences have trivial norm (reindex by `g⁻¹`), and a function of trivial norm is the
  difference of the "partial products along the cycle" `y (g ^ i) = ∏_{i < j < |G|} f (g ^ j)`
  (telescoping, with the wrap-around at `i = 0` supplied by `∏_{k ∈ G} f k = 1`).

## Honesty

Finite group theory only — **no reach toward R1–R3**. No new `structure`/`class`
(`regularShift` is a `def`); all hypotheses carried; no owed witness; D1/D2 N/A.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

variable {G C : Type*} [Group G] [CommGroup C]

/-- **The regular action** of `g : G` on `G → C`: `(regularShift g f) h = f (g⁻¹ * h)`. -/
def regularShift (g : G) : MulAut (G → C) :=
  MulEquiv.arrowCongr (Equiv.mulLeft g) (MulEquiv.refl C)

@[simp] theorem regularShift_apply (g : G) (f : G → C) (h : G) :
    regularShift g f h = f (g⁻¹ * h) := rfl

/-- Powers of the regular action: `(regularShift g ^ j) f h = f ((g ^ j)⁻¹ * h)`. -/
theorem regularShift_pow_apply (g : G) (j : ℕ) (f : G → C) (h : G) :
    (regularShift g ^ j) f h = f ((g ^ j)⁻¹ * h) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, regularShift_apply, ih, pow_succ', mul_inv_rev, mul_assoc]

/-- A generator's powers below `|G|` enumerate `G` exactly once. -/
theorem prod_range_card_pow [Fintype G] (g : G) (hgen : Subgroup.zpowers g = ⊤)
    (φ : G → C) : ∏ j ∈ Finset.range (Nat.card G), φ (g ^ j) = ∏ k, φ k := by
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_zpowers_eq_top hgen
  refine Finset.prod_nbij (fun j => g ^ j) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · rw [Finset.coe_range, ← hord]
    exact pow_injOn_Iio_orderOf
  · intro k _
    have hk : k ∈ Subgroup.zpowers g := by
      rw [hgen]
      exact Subgroup.mem_top k
    rw [← (isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff] at hk
    obtain ⟨i, rfl⟩ := hk
    refine ⟨i % Nat.card G, ?_, ?_⟩
    · rw [Finset.coe_range, Set.mem_Iio]
      exact Nat.mod_lt _ Nat.card_pos
    · rw [← hord]
      exact pow_mod_orderOf g i

/-- **The norm is the constant function `∏_{k ∈ G} f k`.** -/
theorem cyclicNorm_regularShift_apply [Fintype G] (g : G) (hgen : Subgroup.zpowers g = ⊤)
    (f : G → C) (h : G) :
    cyclicNorm (regularShift g) (Nat.card G) f h = ∏ k, f k := by
  rw [cyclicNorm_apply, Finset.prod_apply]
  simp only [regularShift_pow_apply]
  rw [prod_range_card_pow g hgen (fun k => f (k⁻¹ * h))]
  exact Fintype.prod_equiv ((Equiv.inv G).trans (Equiv.mulRight h)) _ _ (fun _ => rfl)

/-- **The regular module is acyclic** (Serre VIII §1: induced modules have trivial
Tate cohomology), in the cyclic-pair form: `im N = ker D` and `im D = ker N`. -/
theorem regular_cyclic_exact [Finite G] (g : G) (hgen : Subgroup.zpowers g = ⊤) :
    (cyclicNorm (regularShift (C := C) g) (Nat.card G)).range =
        (cyclicDiff (regularShift g)).ker ∧
      (cyclicDiff (regularShift (C := C) g)).range =
        (cyclicNorm (regularShift g) (Nat.card G)).ker := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_zpowers_eq_top hgen
  have hnpos : 0 < Nat.card G := Nat.card_pos
  -- every element is `g ^ i` with `i < |G|`, and the exponent is unique
  have hex : ∀ k : G, ∃ i, i < Nat.card G ∧ g ^ i = k := by
    intro k
    have hk : k ∈ Subgroup.zpowers g := by
      rw [hgen]
      exact Subgroup.mem_top k
    rw [← (isOfFinOrder_of_finite g).mem_powers_iff_mem_zpowers,
      Submonoid.mem_powers_iff] at hk
    obtain ⟨i, rfl⟩ := hk
    exact ⟨i % Nat.card G, Nat.mod_lt _ hnpos, by rw [← hord]; exact pow_mod_orderOf g i⟩
  choose idx hidx using hex
  have idx_eq : ∀ k i, i < Nat.card G → g ^ i = k → idx k = i := by
    intro k i hi hgi
    refine pow_injOn_Iio_orderOf ?_ ?_ ((hidx k).2.trans hgi.symm)
    · rw [Set.mem_Iio, hord]
      exact (hidx k).1
    · rw [Set.mem_Iio, hord]
      exact hi
  constructor
  · apply le_antisymm
    · -- norms are constant, hence fixed
      rintro _ ⟨f, rfl⟩
      rw [MonoidHom.mem_ker]
      funext h
      rw [cyclicDiff_apply, Pi.mul_apply, Pi.inv_apply, regularShift_apply,
        cyclicNorm_regularShift_apply g hgen, cyclicNorm_regularShift_apply g hgen,
        mul_inv_cancel, Pi.one_apply]
    · -- fixed functions are constant, and constants are norms
      intro f hf
      rw [MonoidHom.mem_ker] at hf
      have hfix : ∀ h, f (g⁻¹ * h) = f h := by
        intro h
        have h1 := congrFun hf h
        rw [cyclicDiff_apply, Pi.mul_apply, Pi.inv_apply, regularShift_apply, Pi.one_apply,
          mul_inv_eq_one] at h1
        exact h1
      have hpow : ∀ i, f (g ^ i) = f 1 := by
        intro i
        induction i with
        | zero => rw [pow_zero]
        | succ i ih =>
          rw [pow_succ', ← ih, ← hfix (g * g ^ i), inv_mul_cancel_left]
      have hconst : ∀ h, f h = f 1 := by
        intro h
        rw [← (hidx h).2]
        exact hpow _
      refine ⟨Pi.mulSingle 1 (f 1), ?_⟩
      funext h
      rw [cyclicNorm_regularShift_apply g hgen, Finset.prod_pi_mulSingle',
        ite_eq_left (Finset.mem_univ _)]
      exact (hconst h).symm
  · apply le_antisymm
    · -- differences have trivial norm
      rintro _ ⟨f, rfl⟩
      rw [MonoidHom.mem_ker]
      funext h
      rw [cyclicNorm_regularShift_apply g hgen, Pi.one_apply]
      simp only [cyclicDiff_apply, Pi.mul_apply, Pi.inv_apply, regularShift_apply]
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
        Fintype.prod_equiv (Equiv.mulLeft g⁻¹) (fun k => f (g⁻¹ * k)) f (fun _ => rfl),
        mul_inv_cancel]
    · -- trivial norm ⟹ a difference: the partial products along the cycle
      intro f hf
      rw [MonoidHom.mem_ker] at hf
      have hprod : ∏ k, f k = 1 := by
        have h1 := congrFun hf 1
        rwa [cyclicNorm_regularShift_apply g hgen, Pi.one_apply] at h1
      have hgn : g ^ (Nat.card G - 1) = g⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hnpos]
        exact pow_card_eq_one'
      refine ⟨fun k => ∏ j ∈ Finset.Ico (idx k + 1) (Nat.card G), f (g ^ j), ?_⟩
      funext h
      rw [cyclicDiff_apply, Pi.mul_apply, Pi.inv_apply, regularShift_apply]
      obtain ⟨hlt, hpow⟩ := hidx h
      rcases Nat.eq_zero_or_pos (idx h) with h0 | hpos'
      · -- the wrap-around: `h = 1`, `g⁻¹ = g ^ (|G| - 1)`
        have h1 : h = 1 := by rw [← hpow, h0, pow_zero]
        have hinv : idx (g⁻¹ * h) = Nat.card G - 1 := by
          apply idx_eq
          · omega
          · rw [h1, mul_one, hgn]
        rw [hinv, h0, Nat.sub_add_cancel hnpos, Finset.Ico_self, Finset.prod_empty, one_mul,
          zero_add, h1]
        apply inv_eq_of_mul_eq_one_left
        have h2 := hprod
        rw [← prod_range_card_pow g hgen f, Finset.range_eq_Ico,
          Finset.prod_eq_prod_Ico_succ_bot hnpos, pow_zero] at h2
        exact h2
      · -- the generic step: `h = g ^ (i+1)`, `g⁻¹ h = g ^ i`
        obtain ⟨i, hi⟩ : ∃ i, idx h = i + 1 := ⟨idx h - 1, by omega⟩
        have hinv : idx (g⁻¹ * h) = i := by
          apply idx_eq
          · omega
          · rw [← hpow, hi, pow_succ', inv_mul_cancel_left]
        rw [hinv, hi, Finset.prod_eq_prod_Ico_succ_bot (by omega : i + 1 < Nat.card G),
          mul_inv_cancel_right, ← hi, hpow]

-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms regularShift
#print axioms regularShift_pow_apply
#print axioms prod_range_card_pow
#print axioms cyclicNorm_regularShift_apply
#print axioms regular_cyclic_exact

end Anabelian
