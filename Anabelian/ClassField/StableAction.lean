/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.CyclicPair

/-!
# L3.1: stable subgroups — restricted, quotient and layer actions (Pass 96)

The field-free action layer of the Pass-95 design (NOTES Pass 95 §3). For a
`σ`-stable subgroup `S` of a commutative group `M` (`S.map σ = S`):

* `restrictAut σ S h : MulAut S` — the restricted action, with the carrier formula
  `restrictAut_coe : (restrictAut σ S h x : M) = σ x` (by `rfl`);
* `quotientAut σ S h : MulAut (M ⧸ S)` — the induced action on the quotient, with the
  projection formula `quotientAut_mk`;
* `Layer F i := F i ⧸ (F (i+1)).subgroupOf (F i)` for a filtration `F : ℕ → Subgroup M`
  of `σ`-stable subgroups, and `layerAut σ F hF i : MulAut (Layer F i)`, with `layerAut_mk`;
* the **naturality of the cyclic pair** along the inclusion and the projection: Pass 94's
  `map_cyclicNorm`/`map_cyclicDiff` at `S.subtype`, `QuotientGroup.mk'`, and the layer
  projection (`cyclicNorm_restrictAut_coe`, `cyclicNorm_quotientAut_mk`,
  `cyclicNorm_layerAut_mk`, and the `cyclicDiff` versions) — the four intertwinings that
  Pass 90's multiplicativity and Pass 95's `finite_acyclic_kernel_reduction` consume;
* `herbrandH_subsingleton_of_exact`: `im g = ker f` makes `Ĥ = ker f / im g` a
  subsingleton — the bridge from range/kernel equalities to the `Subsingleton` instances
  of the reduction.

## Honesty

Pure group theory over a commutative group with an automorphism — **no reach toward
R1–R3**, no field, no valuation. No new `structure`/`class` (`Layer` is an `abbrev`, the
two `MulAut`s are `def`s); every hypothesis is carried, none is claimed load-bearing; no
owed witness; D1/D2 N/A.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

variable {M : Type*} [CommGroup M]

section Stable

/-- Membership in a `σ`-stable subgroup is `σ`-invariant: `σ x ∈ S ↔ x ∈ S`. -/
theorem apply_mem_iff_of_map_eq (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (x : M) : σ x ∈ S ↔ x ∈ S := by
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : σ y = σ x := hyx
    rw [← σ.injective hyx']
    exact hy
  · intro hx
    rw [← h]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

/-- Every power of `σ` preserves a `σ`-stable subgroup. -/
theorem pow_apply_mem_of_map_eq (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (j : ℕ) {x : M} (hx : x ∈ S) : (σ ^ j) x ∈ S := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact (apply_mem_iff_of_map_eq σ S h _).mpr ih

/-- The cyclic norm preserves a `σ`-stable subgroup. -/
theorem cyclicNorm_mem_of_map_eq (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (n : ℕ) {x : M} (hx : x ∈ S) :
    cyclicNorm σ n x ∈ S := by
  rw [cyclicNorm_apply]
  exact S.prod_mem fun j _ => pow_apply_mem_of_map_eq σ S h j hx

/-- The cyclic difference preserves a `σ`-stable subgroup. -/
theorem cyclicDiff_mem_of_map_eq (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) {x : M} (hx : x ∈ S) : cyclicDiff σ x ∈ S := by
  rw [cyclicDiff_apply]
  exact S.mul_mem ((apply_mem_iff_of_map_eq σ S h x).mpr hx) (S.inv_mem hx)

/-- **The restricted action** of `σ` on a `σ`-stable subgroup `S`. -/
def restrictAut (σ : MulAut M) (S : Subgroup M) (h : S.map σ.toMonoidHom = S) :
    MulAut S :=
  (σ.subgroupMap S).trans (MulEquiv.subgroupCongr h)

/-- The carrier formula: `restrictAut σ S h` acts as `σ` on the underlying elements. -/
@[simp] theorem restrictAut_coe (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (x : S) : (restrictAut σ S h x : M) = σ x := rfl

/-- **The quotient action** of `σ` on `M ⧸ S` for a `σ`-stable subgroup `S`. -/
def quotientAut (σ : MulAut M) (S : Subgroup M) (h : S.map σ.toMonoidHom = S) :
    MulAut (M ⧸ S) :=
  QuotientGroup.congr S S σ h

/-- The projection formula: `quotientAut σ S h` acts as `σ` on representatives. -/
theorem quotientAut_mk (σ : MulAut M) (S : Subgroup M) (h : S.map σ.toMonoidHom = S)
    (x : M) :
    quotientAut σ S h (QuotientGroup.mk' S x) = QuotientGroup.mk' S (σ x) :=
  QuotientGroup.congr_mk' S S σ h x

/-- The `i`-th layer `F i ⧸ F (i+1)` of a filtration (as a quotient of `F i` by the
subgroup `F (i+1) ∩ F i`, so no monotonicity hypothesis is needed to state it). -/
abbrev Layer (F : ℕ → Subgroup M) (i : ℕ) :=
  (F i) ⧸ ((F (i + 1)).subgroupOf (F i))

/-- The restricted action on `F i` preserves the subgroup `F (i+1) ∩ F i`. -/
theorem subgroupOf_map_restrictAut (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i : ℕ) :
    ((F (i + 1)).subgroupOf (F i)).map (restrictAut σ (F i) (hF i)).toMonoidHom
      = (F (i + 1)).subgroupOf (F i) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    exact (apply_mem_iff_of_map_eq σ (F (i + 1)) (hF (i + 1)) _).mpr hx
  · intro hy
    refine ⟨(restrictAut σ (F i) (hF i)).symm y, ?_,
      (restrictAut σ (F i) (hF i)).apply_symm_apply y⟩
    rw [Subgroup.mem_subgroupOf]
    have h1 : σ (((restrictAut σ (F i) (hF i)).symm y : F i) : M) = (y : M) := by
      rw [← restrictAut_coe σ (F i) (hF i), MulEquiv.apply_symm_apply]
    rw [← apply_mem_iff_of_map_eq σ (F (i + 1)) (hF (i + 1)), h1]
    exact hy

/-- **The layer action**: `σ` on `F i ⧸ F (i+1)`. -/
def layerAut (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i : ℕ) : MulAut (Layer F i) :=
  quotientAut (restrictAut σ (F i) (hF i)) ((F (i + 1)).subgroupOf (F i))
    (subgroupOf_map_restrictAut σ F hF i)

/-- The layer projection formula. -/
theorem layerAut_mk (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i : ℕ) (x : F i) :
    layerAut σ F hF i (QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i)) x)
      = QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i)) (restrictAut σ (F i) (hF i) x) :=
  quotientAut_mk _ _ _ x

end Stable

section Naturality

/-! ### Naturality of the cyclic pair (Pass 94's `map_cyclicNorm`/`map_cyclicDiff`) -/

/-- The norm of the restricted action is the norm downstairs. -/
theorem cyclicNorm_restrictAut_coe (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (n : ℕ) (x : S) :
    ((cyclicNorm (restrictAut σ S h) n x : S) : M) = cyclicNorm σ n (x : M) :=
  map_cyclicNorm S.subtype (restrictAut σ S h) σ (restrictAut_coe σ S h) n x

/-- The difference of the restricted action is the difference downstairs. -/
theorem cyclicDiff_restrictAut_coe (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (x : S) :
    ((cyclicDiff (restrictAut σ S h) x : S) : M) = cyclicDiff σ (x : M) :=
  map_cyclicDiff S.subtype (restrictAut σ S h) σ (restrictAut_coe σ S h) x

/-- The norm of the quotient action on a representative. -/
theorem cyclicNorm_quotientAut_mk (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (n : ℕ) (x : M) :
    cyclicNorm (quotientAut σ S h) n (QuotientGroup.mk' S x)
      = QuotientGroup.mk' S (cyclicNorm σ n x) :=
  (map_cyclicNorm (QuotientGroup.mk' S) σ (quotientAut σ S h) (quotientAut_mk σ S h) n x).symm

/-- The difference of the quotient action on a representative. -/
theorem cyclicDiff_quotientAut_mk (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (x : M) :
    cyclicDiff (quotientAut σ S h) (QuotientGroup.mk' S x)
      = QuotientGroup.mk' S (cyclicDiff σ x) :=
  (map_cyclicDiff (QuotientGroup.mk' S) σ (quotientAut σ S h) (quotientAut_mk σ S h) x).symm

/-- The norm of the layer action on a representative. -/
theorem cyclicNorm_layerAut_mk (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i n : ℕ) (x : F i) :
    cyclicNorm (layerAut σ F hF i) n (QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i)) x)
      = QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i))
          (cyclicNorm (restrictAut σ (F i) (hF i)) n x) :=
  cyclicNorm_quotientAut_mk _ _ _ n x

/-- The difference of the layer action on a representative. -/
theorem cyclicDiff_layerAut_mk (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i : ℕ) (x : F i) :
    cyclicDiff (layerAut σ F hF i) (QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i)) x)
      = QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i))
          (cyclicDiff (restrictAut σ (F i) (hF i)) x) :=
  cyclicDiff_quotientAut_mk _ _ _ x

end Naturality

/-- **Exactness kills `Ĥ`**: if `im g = ker f` then `herbrandH f g = ker f / im g` is a
subsingleton — the form in which Pass 95's `finite_acyclic_kernel_reduction` consumes
acyclicity. -/
theorem herbrandH_subsingleton_of_exact (f g : M →* M) (h : g.range = f.ker) :
    Subsingleton (herbrandH f g) := by
  constructor
  intro a b
  induction a using QuotientGroup.induction_on with | _ a => ?_
  induction b using QuotientGroup.induction_on with | _ b => ?_
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf, h]
  exact (a⁻¹ * b).2

-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms restrictAut
#print axioms quotientAut
#print axioms layerAut
#print axioms layerAut_mk
#print axioms cyclicNorm_restrictAut_coe
#print axioms cyclicDiff_restrictAut_coe
#print axioms cyclicNorm_quotientAut_mk
#print axioms cyclicDiff_quotientAut_mk
#print axioms cyclicNorm_layerAut_mk
#print axioms cyclicDiff_layerAut_mk
#print axioms herbrandH_subsingleton_of_exact

end Anabelian
