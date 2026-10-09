/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.StableAction

/-!
# L3.1: exactness lifts through a complete filtration (Pass 96)

The dévissage brick of the Pass-95 design (NOTES Pass 95 §3), in pure algebra:

* **`ker_eq_range_of_filtration`** — for a pair `(f, g)` with `f ∘ g = 1` on a commutative
  group `M` and a filtration `F : ℕ → Subgroup M` with `F 0 = ⊤`, `g`-stable, whose layers
  satisfy the correction property `x ∈ F i, f x ∈ F (i+1) ⟹ ∃ y ∈ F i, x·(g y)⁻¹ ∈ F (i+1)`,
  and which is **separated** (`⋂ F i = 1`) and **complete** (every coherent sequence has a
  limit): `ker f = im g`. The proof is successive approximation — correct at each depth,
  take the limit of the partial products of the corrections, and let separation kill the
  residual error.
* **`layer_of_surjective`** — the correction property is inherited along a surjective
  equivariant map `θ : S →* W` with kernel `T` from `ker fW ≤ im gW` on `W`: the form in
  which the regular layers of the unit filtration will supply it.
* **`cyclic_exact_of_complete_filtration`** — the cyclic corollary: both range/kernel
  equalities for `(cyclicNorm σ n, cyclicDiff σ)` on `M` from the same equalities on every
  layer `F i ⧸ F (i+1)` (via `layerAut`), `σ ^ n = 1`, separation and completeness. This is
  the general lemma applied in both orders; Pass 94's naturality (through Pass 96's
  `cyclicNorm_layerAut_mk` etc.) supplies the equivariance of the layer projections.

Compared with the Pass-95 catalogue, `cyclic_exact_of_complete_filtration` carries **no**
`Antitone F` hypothesis: the proof never uses it (the layers are stated with `subgroupOf`).

## Honesty

Group theory only — **no reach toward R1–R3**. The local-field inputs (the lattice unit
subgroups, their regular layers, adic completeness) are *not* here; they are Passes 99–101
of the design. No new `structure`/`class`; all hypotheses carried; no owed witness; D1/D2
N/A.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

variable {M : Type*} [CommGroup M]

/-- **Successive approximation**: `ker f = im g` for a pair with `f ∘ g = 1` along a
`g`-stable filtration with the layer correction property, separated and complete. -/
theorem ker_eq_range_of_filtration (f g : M →* M) (hfg : ∀ x, f (g x) = 1)
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ i, ∀ x ∈ F i, g x ∈ F i)
    (hlayer : ∀ i, ∀ x ∈ F i, f x ∈ F (i + 1) → ∃ y ∈ F i, x * (g y)⁻¹ ∈ F (i + 1))
    (hsep : ∀ x, (∀ i, x ∈ F i) → x = 1)
    (hcomplete : ∀ z : ℕ → M, (∀ i, z (i + 1) * (z i)⁻¹ ∈ F i) →
      ∃ y, ∀ i, y * (z i)⁻¹ ∈ F i) :
    f.ker = g.range := by
  refine le_antisymm ?_ (range_le_ker f g hfg)
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  classical
  -- a correction at every depth, packaged as a total function
  obtain ⟨corr, hcorr⟩ : ∃ corr : ℕ → M → M, ∀ i x, x ∈ F i → f x = 1 →
      corr i x ∈ F i ∧ x * (g (corr i x))⁻¹ ∈ F (i + 1) := by
    refine ⟨fun i x => if h : x ∈ F i ∧ f x = 1 then
      Classical.choose (hlayer i x h.1 (by rw [h.2]; exact one_mem _)) else 1, ?_⟩
    intro i x hxi hfx
    have h : x ∈ F i ∧ f x = 1 := ⟨hxi, hfx⟩
    simp only [dite_eq_left h]
    exact Classical.choose_spec (hlayer i x h.1 (by rw [h.2]; exact one_mem _))
  -- the approximants `xs i ∈ F i ∩ ker f` and the partial products `zs i` of corrections
  obtain ⟨xs, hxs0, hxss⟩ : ∃ xs : ℕ → M, xs 0 = x ∧
      ∀ i, xs (i + 1) = xs i * (g (corr i (xs i)))⁻¹ :=
    ⟨fun i => Nat.rec x (fun j xj => xj * (g (corr j xj))⁻¹) i, rfl, fun _ => rfl⟩
  have hxs : ∀ i, xs i ∈ F i ∧ f (xs i) = 1 := by
    intro i
    induction i with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hxs0, hF0]
        exact Subgroup.mem_top x
      · rw [hxs0]
        exact hx
    | succ i ih =>
      rw [hxss]
      refine ⟨(hcorr i (xs i) ih.1 ih.2).2, ?_⟩
      rw [map_mul, map_inv, hfg, ih.2, inv_one, mul_one]
  obtain ⟨zs, hzs0, hzss⟩ : ∃ zs : ℕ → M, zs 0 = 1 ∧
      ∀ i, zs (i + 1) = corr i (xs i) * zs i :=
    ⟨fun i => Nat.rec 1 (fun j zj => corr j (xs j) * zj) i, rfl, fun _ => rfl⟩
  have hxz : ∀ i, xs i = x * (g (zs i))⁻¹ := by
    intro i
    induction i with
    | zero => rw [hxs0, hzs0, map_one, inv_one, mul_one]
    | succ i ih => rw [hxss, hzss, ih, map_mul, mul_inv_rev, mul_assoc]
  have hcoh : ∀ i, zs (i + 1) * (zs i)⁻¹ ∈ F i := by
    intro i
    rw [hzss, mul_inv_cancel_right]
    exact (hcorr i (xs i) (hxs i).1 (hxs i).2).1
  obtain ⟨y, hy⟩ := hcomplete zs hcoh
  refine ⟨y, ?_⟩
  -- the residual `x · (g y)⁻¹` lies in every `F i`, hence is `1`
  have key : ∀ i, x * (g y)⁻¹ ∈ F i := by
    intro i
    have h1 : x * (g y)⁻¹ = xs i * (g (y * (zs i)⁻¹))⁻¹ := by
      rw [hxz i, map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
    rw [h1]
    exact (F i).mul_mem (hxs i).1 ((F i).inv_mem (hstab i _ (hy i)))
  exact (mul_inv_eq_one.mp (hsep _ key)).symm

/-- **Layer transfer**: the correction property on `S` modulo `T` follows from `ker fW ≤ im gW`
on the target of a surjective equivariant map `θ : S →* W` with `ker θ = T`. -/
theorem layer_of_surjective {W : Type*} [CommGroup W]
    (f g : M →* M) (S T : Subgroup M)
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S)
    (θ : S →* W) (hθ : Function.Surjective θ)
    (hker : ∀ x : S, θ x = 1 ↔ (x : M) ∈ T)
    (fW gW : W →* W)
    (hfθ : ∀ x : S, θ ⟨f x, hfS x x.property⟩ = fW (θ x))
    (hgθ : ∀ x : S, θ ⟨g x, hgS x x.property⟩ = gW (θ x))
    (hW : fW.ker ≤ gW.range) :
    ∀ x ∈ S, f x ∈ T → ∃ y ∈ S, x * (g y)⁻¹ ∈ T := by
  intro x hx hfx
  have h1 : fW (θ ⟨x, hx⟩) = 1 := by
    rw [← hfθ ⟨x, hx⟩]
    exact (hker ⟨f x, hfS x hx⟩).mpr hfx
  obtain ⟨w, hw⟩ := hW (MonoidHom.mem_ker.mpr h1)
  obtain ⟨y, rfl⟩ := hθ w
  refine ⟨y, y.2, ?_⟩
  have h2 : θ (⟨x, hx⟩ * ⟨g y, hgS y y.2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hgθ, hw, mul_inv_cancel]
  exact (hker _).mp h2

/-- **The cyclic corollary**: both range/kernel equalities of the cyclic pair on `M` from
the same equalities on every layer of a `σ`-stable, separated, complete filtration. -/
theorem cyclic_exact_of_complete_filtration (σ : MulAut M) (n : ℕ) (hσ : σ ^ n = 1)
    (F : ℕ → Subgroup M) (hF : ∀ i, (F i).map σ.toMonoidHom = F i)
    (hzero : F 0 = ⊤) (hsep : (⨅ i, F i) = ⊥)
    (hcomplete : ∀ u : ℕ → M, (∀ i, u (i + 1) * (u i)⁻¹ ∈ F i) →
      ∃ x : M, ∀ i, x * (u i)⁻¹ ∈ F i)
    (hlayer : ∀ i,
      (cyclicNorm (layerAut σ F hF i) n).range = (cyclicDiff (layerAut σ F hF i)).ker ∧
      (cyclicDiff (layerAut σ F hF i)).range = (cyclicNorm (layerAut σ F hF i) n).ker) :
    (cyclicNorm σ n).range = (cyclicDiff σ).ker ∧
      (cyclicDiff σ).range = (cyclicNorm σ n).ker := by
  have hsep' : ∀ x, (∀ i, x ∈ F i) → x = 1 := by
    intro x hx
    have h1 : x ∈ ⨅ i, F i := Subgroup.mem_iInf.mpr hx
    rw [hsep] at h1
    exact Subgroup.mem_bot.mp h1
  have hker : ∀ i (x : F i),
      QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i)) x = 1 ↔ (x : M) ∈ F (i + 1) := by
    intro i x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · -- `Ĥ⁰`: `ker D = im N`
    refine (ker_eq_range_of_filtration (cyclicDiff σ) (cyclicNorm σ n)
      (cyclicDiff_cyclicNorm σ n hσ) F hzero
      (fun i x hx => cyclicNorm_mem_of_map_eq σ (F i) (hF i) n hx) ?_ hsep' hcomplete).symm
    intro i
    refine layer_of_surjective (cyclicDiff σ) (cyclicNorm σ n) (F i) (F (i + 1))
      (fun x hx => cyclicDiff_mem_of_map_eq σ (F i) (hF i) hx)
      (fun x hx => cyclicNorm_mem_of_map_eq σ (F i) (hF i) n hx)
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (hker i)
      (cyclicDiff (layerAut σ F hF i)) (cyclicNorm (layerAut σ F hF i) n) ?_ ?_
      (hlayer i).1.symm.le
    · intro x
      rw [cyclicDiff_layerAut_mk]
      exact congrArg _ (Subtype.ext (cyclicDiff_restrictAut_coe σ (F i) (hF i) x).symm)
    · intro x
      rw [cyclicNorm_layerAut_mk]
      exact congrArg _ (Subtype.ext (cyclicNorm_restrictAut_coe σ (F i) (hF i) n x).symm)
  · -- `Ĥ¹`: `ker N = im D`
    refine (ker_eq_range_of_filtration (cyclicNorm σ n) (cyclicDiff σ)
      (cyclicNorm_cyclicDiff σ n hσ) F hzero
      (fun i x hx => cyclicDiff_mem_of_map_eq σ (F i) (hF i) hx) ?_ hsep' hcomplete).symm
    intro i
    refine layer_of_surjective (cyclicNorm σ n) (cyclicDiff σ) (F i) (F (i + 1))
      (fun x hx => cyclicNorm_mem_of_map_eq σ (F i) (hF i) n hx)
      (fun x hx => cyclicDiff_mem_of_map_eq σ (F i) (hF i) hx)
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (hker i)
      (cyclicNorm (layerAut σ F hF i) n) (cyclicDiff (layerAut σ F hF i)) ?_ ?_
      (hlayer i).2.symm.le
    · intro x
      rw [cyclicNorm_layerAut_mk]
      exact congrArg _ (Subtype.ext (cyclicNorm_restrictAut_coe σ (F i) (hF i) n x).symm)
    · intro x
      rw [cyclicDiff_layerAut_mk]
      exact congrArg _ (Subtype.ext (cyclicDiff_restrictAut_coe σ (F i) (hF i) x).symm)

-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms ker_eq_range_of_filtration
#print axioms layer_of_surjective
#print axioms cyclic_exact_of_complete_filtration

end Anabelian
