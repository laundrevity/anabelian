/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Ramification.Filtration
import Anabelian.Ramification.Subgroup
import Mathlib

/-!
# The ascent: the quotient-restriction skeleton (toward Serre IV §3 Lemma 5) (Pass 50)

Pass 46 (`Anabelian/RamificationSubgroup.lean`) settled the *subgroup* half of the tower theory:
`H_u = H ∩ G_u` along `Gal(L/K') ↪ Gal(L/K)`. The road to **Herbrand's theorem** and
**`φ`-transitivity** runs through the *quotient* half — how the ramification data of `K'/K` sits
under the restriction `Gal(L/K) ↠ Gal(K'/K)` (Serre, *Local Fields*, IV §3 Lemma 5:
`(G/H)_{φ_{L/K'}(u)} = G_u H/H`). That is a multi-pass wall whose core is ramification
*arithmetic* (how `i_{K'/K}(σ̄)` relates to the `i_{L/K}` of the lifts of `σ̄`). **This pass builds
the group-theoretic skeleton it stands on — deliberately without the arithmetic.**

Throughout, `K ⊆ K' ⊆ L` is a tower with `K'/K` **normal** (the hypothesis under which
`Gal(K'/K)` receives a restriction map at all — Mathlib's `AlgEquiv.restrictNormalHom`), and the
valuation data of `K'` is `A ∩ K'` = `A.comap (algebraMap K' L)` (for `A = 𝒪_L` this is `𝒪_{K'}`,
and Pass 43's canonicity makes the choice unambiguous).

## What is proved (all axiom-free)

* `restrictNormalHom_smul_comap` — restriction to the normal subfield intertwines the pointwise
  actions on valuation subrings: `σ̄ • (A ∩ K') = (σ • A) ∩ K'`.
* `decompositionQuotient` — **the quotient restriction on decomposition groups**
  `D(A) ≤ Gal(L/K) →* D(A ∩ K') ≤ Gal(K'/K)`, the quotient counterpart of Pass 46's
  `decompositionRestrict`; action compatibility `algebraMap K' L (σ̄ • b) = σ (algebraMap K' L b)`
  (`algebraMap_decompositionQuotient_smul` — here via `restrictNormal_commutes`, *not* `rfl`:
  exactly why the quotient half is harder than the subgroup half).
* **`decompositionQuotient_ker`** — the headline: **exactness of
  `Gal(L/K') → Gal(L/K) → Gal(K'/K)` at the decomposition level** —
  `ker (decompositionQuotient) = range (decompositionRestrict)`. A `σ` killed by restriction
  fixes `K'` pointwise, hence *is* a `K'`-automorphism stabilizing `A`
  (`AlgEquiv.ofRingEquiv`); the converse is `decompositionQuotient_comp_decompositionRestrict`.
* `comapRingHom` + `mem_maximalIdeal_of_comapRingHom` — the ring map `A ∩ K' →+* A` and the
  transfer `x ∈ 𝔪_{A∩K'}` whenever its image lies in `𝔪_A` (units reflect along the inclusion —
  the valuation-subring dichotomy at work).
* `decompositionQuotient_mem_ramificationGroup_zero` / `ramificationGroup_zero_map_le` /
  `inertiaSubgroup_map_le` — **the quotient map preserves inertia**: the image of
  `G_0(L/K)` lands in `G_0(K'/K)` (equivalently for Mathlib's `inertiaSubgroup` via Pass 23's
  `ramificationGroup_zero`). The first genuinely ramification-flavored quotient fact — the `i = 0`
  case where no renumbering is needed.

## What is deliberately NOT here (the wall, unbuilt rather than half-built)

* **Surjectivity** of `decompositionQuotient` (Serre IV §1 Prop. 3 / conjugacy of extensions):
  Mathlib's `restrictNormalHom_surjective` lifts through `Gal(L/K)`, but landing the lift *inside
  the decomposition group* needs transitivity of `Gal` on the valuation subrings above a given
  one — real arithmetic content, deferred.
* **The higher-`i` image** — how `G_u(L/K)` maps for `u > 0` is precisely Serre's Lemma 5 with its
  `φ_{L/K'}`-renumbering, i.e. the `i_{K'/K}` vs `i_{L/K}` arithmetic. Not attempted here in
  either direction; the `i = 0` containment above is the renumbering-free base case
  (`φ_{L/K'}(0) = 0`).

## Honesty

Group-theoretic bookkeeping for a tower of given fields — **no reach toward R1–R3**; nothing
recovered from an abstract group. `[Normal K K']` is a *definitional prerequisite* (without it
`Gal(K'/K)` receives no restriction map and `decompositionQuotient` does not exist), not a
removable theorem hypothesis — no rule-2 witness obligation arises. No new `structure`/`class`
(`decompositionQuotient`/`comapRingHom` are `def`s of a `MonoidHom`/`RingHom`; the results are
about `Subgroup`s). No owed witness; D1 N/A; D2 N/A.

## Axiom status

Standard axioms only on every declaration (`#print axioms` below). Ledger: `0 FOUNDATIONAL /
0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing
open scoped Pointwise

namespace Anabelian

variable (K K' : Type*) [Field K] [Field K'] [Algebra K K']
variable {L : Type*} [Field L] [Algebra K' L] [Algebra K L] [IsScalarTower K K' L]
variable [Normal K K']
variable (A : ValuationSubring L)

/-- Restriction to the normal subfield intertwines the pointwise actions on valuation subrings:
`σ̄ • (A ∩ K') = (σ • A) ∩ K'`, where `σ̄ = restrictNormalHom K' σ` and `∩ K'` is
`comap (algebraMap K' L)`. The engine is `restrictNormal_commutes` applied to `σ⁻¹` (the
membership tests of both sides agree through `algebraMap`). -/
theorem restrictNormalHom_smul_comap (σ : L ≃ₐ[K] L) :
    AlgEquiv.restrictNormalHom K' σ • A.comap (algebraMap K' L)
      = (σ • A).comap (algebraMap K' L) := by
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_comap, mem_comap,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have key : algebraMap K' L ((AlgEquiv.restrictNormalHom K' σ)⁻¹ • x)
      = σ⁻¹ • algebraMap K' L x := by
    rw [← map_inv (AlgEquiv.restrictNormalHom K') σ]
    exact AlgEquiv.restrictNormal_commutes σ⁻¹ K' x
  rw [key]

/-- A `K`-automorphism of `L` stabilizing `A` restricts to a `K`-automorphism of the normal
subfield `K'` stabilizing `A ∩ K'`. -/
theorem mem_stabilizer_restrictNormalHom {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) A) :
    AlgEquiv.restrictNormalHom K' σ
      ∈ MulAction.stabilizer (K' ≃ₐ[K] K') (A.comap (algebraMap K' L)) := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [restrictNormalHom_smul_comap K K' A σ, hσ]

/-- **The quotient restriction on decomposition groups** `D(A) →* D(A ∩ K')` along
`Gal(L/K) ↠ Gal(K'/K)` (for `K'/K` normal) — the quotient counterpart of Pass 46's
`decompositionRestrict`, and the group-theoretic skeleton under Serre IV §3 Lemma 5. -/
noncomputable def decompositionQuotient :
    A.decompositionSubgroup K →* (A.comap (algebraMap K' L)).decompositionSubgroup K where
  toFun σ := ⟨AlgEquiv.restrictNormalHom K' σ.1,
    mem_stabilizer_restrictNormalHom K K' A σ.2⟩
  map_one' := Subtype.ext (map_one (AlgEquiv.restrictNormalHom K'))
  map_mul' σ τ := Subtype.ext (map_mul (AlgEquiv.restrictNormalHom K') σ.1 τ.1)

/-- Action compatibility for the quotient restriction: through `algebraMap K' L`, the restricted
automorphism acts as the original — `restrictNormal_commutes` at the decomposition level. (Unlike
Pass 46's subgroup half, this is *not* `rfl`: the quotient direction changes the underlying
field.) -/
@[simp] theorem algebraMap_decompositionQuotient_smul (σ : A.decompositionSubgroup K)
    (b : ↥(A.comap (algebraMap K' L))) :
    algebraMap K' L ↑(decompositionQuotient K K' A σ • b)
      = σ.1 (algebraMap K' L ↑b) :=
  AlgEquiv.restrictNormal_commutes σ.1 K' b.1

/-- The composite `D(A) ≤ Gal(L/K') → Gal(L/K) → Gal(K'/K)` is trivial: a `K'`-automorphism of
`L` restricts to the identity of `K'`. One half of the exactness `decompositionQuotient_ker`. -/
theorem decompositionQuotient_comp_decompositionRestrict :
    (decompositionQuotient K K' A).comp (decompositionRestrict K K' A) = 1 := by
  refine MonoidHom.ext fun σ => ?_
  refine Subtype.ext (AlgEquiv.ext fun x => ?_)
  apply (algebraMap K' L).injective
  calc algebraMap K' L (AlgEquiv.restrictNormalHom K' (σ.1.restrictScalars K) x)
      = (σ.1.restrictScalars K) (algebraMap K' L x) :=
        AlgEquiv.restrictNormal_commutes (σ.1.restrictScalars K) K' x
    _ = algebraMap K' L x := AlgEquiv.commutes σ.1 x
    _ = algebraMap K' L ((1 : K' ≃ₐ[K] K') x) := rfl

/-- **Exactness at the decomposition level**: the kernel of the quotient restriction
`D(A) → D(A ∩ K')` is exactly the image of `Gal(L/K')`'s decomposition group — the decomposition
groups inherit the exactness of `1 → Gal(L/K') → Gal(L/K) → Gal(K'/K)`. A `σ` restricting to
`1` on `K'` fixes `algebraMap K' L` pointwise, hence *is* a `K'`-algebra automorphism
(`AlgEquiv.ofRingEquiv`) stabilizing `A` (same underlying map); the reverse inclusion is
`decompositionQuotient_comp_decompositionRestrict`. -/
theorem decompositionQuotient_ker :
    (decompositionQuotient K K' A).ker = (decompositionRestrict K K' A).range := by
  ext σ
  constructor
  · intro hσ
    rw [MonoidHom.mem_ker] at hσ
    have h1 : AlgEquiv.restrictNormalHom K' σ.1 = 1 := congrArg Subtype.val hσ
    have hfix : ∀ x : K', σ.1 (algebraMap K' L x) = algebraMap K' L x := by
      intro x
      calc σ.1 (algebraMap K' L x)
          = algebraMap K' L (AlgEquiv.restrictNormalHom K' σ.1 x) :=
            (AlgEquiv.restrictNormal_commutes σ.1 K' x).symm
        _ = algebraMap K' L x := by rw [h1, AlgEquiv.one_apply]
    let τ : L ≃ₐ[K'] L := AlgEquiv.ofRingEquiv (f := σ.1.toRingEquiv) hfix
    have hτA : τ ∈ MulAction.stabilizer (L ≃ₐ[K'] L) A := by
      rw [MulAction.mem_stabilizer_iff]
      have hA : σ.1 • A = A := MulAction.mem_stabilizer_iff.mp σ.2
      refine SetLike.ext fun x => ?_
      have h2 : x ∈ τ • A ↔ τ⁻¹ • x ∈ A :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      have h3 : x ∈ σ.1 • A ↔ σ.1⁻¹ • x ∈ A :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      have h4 : τ⁻¹ • x = σ.1⁻¹ • x := rfl
      rw [h2, h4, ← h3, hA]
    refine ⟨⟨τ, hτA⟩, ?_⟩
    apply Subtype.ext
    exact AlgEquiv.ext fun x => rfl
  · rintro ⟨τ, rfl⟩
    rw [MonoidHom.mem_ker]
    simpa using DFunLike.congr_fun
      (decompositionQuotient_comp_decompositionRestrict K K' A) τ

/-- The inclusion `A ∩ K' →+* A` of valuation subrings along `algebraMap K' L`. -/
noncomputable def comapRingHom :
    ↥(A.comap (algebraMap K' L)) →+* ↥A where
  toFun x := ⟨algebraMap K' L x.1, mem_comap.mp x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- The inclusion `A ∩ K' →+* A` **reflects the maximal ideal**: if the image of `x` is a
non-unit of `A`, then `x` is a non-unit of `A ∩ K'` (a unit's inverse would map to an inverse).
The transfer that makes inertia-preservation a one-liner. -/
theorem mem_maximalIdeal_of_comapRingHom {x : ↥(A.comap (algebraMap K' L))}
    (hx : comapRingHom K' A x ∈ maximalIdeal ↥A) :
    x ∈ maximalIdeal ↥(A.comap (algebraMap K' L)) := by
  rw [mem_maximalIdeal, _root_.mem_nonunits_iff] at hx ⊢
  intro hu
  exact hx (hu.map (comapRingHom K' A))

/-- **The quotient restriction preserves inertia** (elementwise): if `σ ∈ G_0(L/K)` then
`σ̄ ∈ G_0(K'/K)`. For `b ∈ A ∩ K'`, `σ̄b − b` maps to `σ(b) − b ∈ 𝔪_A` under `comapRingHom`
(action compatibility), and the inclusion reflects `𝔪`. The `i = 0` (renumbering-free) base case
of Serre IV §3 Lemma 5: `φ_{L/K'}(0) = 0`. -/
theorem decompositionQuotient_mem_ramificationGroup_zero {σ : A.decompositionSubgroup K}
    (hσ : σ ∈ ramificationGroup K A 0) :
    decompositionQuotient K K' A σ
      ∈ ramificationGroup K (A.comap (algebraMap K' L)) 0 := by
  rw [mem_ramificationGroup_iff] at hσ ⊢
  intro b
  rw [zero_add, pow_one]
  have key : comapRingHom K' A (decompositionQuotient K K' A σ • b - b)
      = σ • comapRingHom K' A b - comapRingHom K' A b := by
    rw [map_sub]
    congr 1
    exact Subtype.ext (algebraMap_decompositionQuotient_smul K K' A σ b)
  apply mem_maximalIdeal_of_comapRingHom K' A
  rw [key]
  have h0 := hσ (comapRingHom K' A b)
  rwa [zero_add, pow_one] at h0

/-- `G_0(L/K)` maps into `G_0(K'/K)` under the quotient restriction, in `map ≤` form. -/
theorem ramificationGroup_zero_map_le :
    (ramificationGroup K A 0).map (decompositionQuotient K K' A)
      ≤ ramificationGroup K (A.comap (algebraMap K' L)) 0 := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact decompositionQuotient_mem_ramificationGroup_zero K K' A hσ

/-- The same for Mathlib's `inertiaSubgroup` (via Pass 23's `ramificationGroup_zero`): the image
of the inertia subgroup of `L/K` lies in the inertia subgroup of `K'/K`. -/
theorem inertiaSubgroup_map_le :
    (A.inertiaSubgroup K).map (decompositionQuotient K K' A)
      ≤ (A.comap (algebraMap K' L)).inertiaSubgroup K := by
  rw [← ramificationGroup_zero, ← ramificationGroup_zero]
  exact ramificationGroup_zero_map_le K K' A

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms restrictNormalHom_smul_comap
#print axioms mem_stabilizer_restrictNormalHom
#print axioms decompositionQuotient
#print axioms algebraMap_decompositionQuotient_smul
#print axioms decompositionQuotient_comp_decompositionRestrict
#print axioms decompositionQuotient_ker
#print axioms comapRingHom
#print axioms mem_maximalIdeal_of_comapRingHom
#print axioms decompositionQuotient_mem_ramificationGroup_zero
#print axioms ramificationGroup_zero_map_le
#print axioms inertiaSubgroup_map_le

end Anabelian
