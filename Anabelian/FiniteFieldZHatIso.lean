/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.FiniteFieldLevel
import Anabelian.ZHatProcyclic

/-!
# Rung L1: closing `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` — the first L1 whole of depth (Pass 10)

This pass **closes** the topological-group isomorphism `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` for a finite field `K`,
axiom-free. It is the capstone of the Pass 6–9 sub-plan and the project's **first closed L1 whole of
real depth** (Passes 1–4 were genuine but light; 5 took the one `FOUNDATIONAL` boundary; 6–9 were
honest halves/infrastructure).

## The four assembled ingredients (Passes 6–9)

* `zhatToGalois` + `zhatToGalois_surjective` (Pass 6): the canonical continuous `Ẑ → Gal(K̄/K)`,
  surjective.
* `orderOf_levelRestrict_frobenius` (Pass 9): `r_n (Frob)` has **order `n`** in `Gal(𝔽_{q^n}/K)`.
* `zhat_topologicalClosure_eq_top` (Pass 8): `Ẑ` is procyclic (`zhatGen = η(ofAdd 1)` generates).
* `exist_openNormalSubgroup_sub_open_nhds_of_one` (Mathlib; the engine behind Pass 8's
  `toLimit_injective`): open normal subgroups of a profinite group separate points.

## The injectivity argument (the one substantive rung this pass)

`zhatToGalois` is injective. With `χ_m := r_m ∘ zhatToGalois : Ẑ →* Gal(𝔽_{q^m}/K)` (here
`levelComp K m`): `χ_m zhatGen = r_m (Frob)` has **order `m`** (Pass 9), so for any `S` with
`zhatGen^m ∈ S` and `S` closed, `ker χ_m ≤ S` — because the dense `⟨zhatGen⟩` meets the
*open* `ker χ_m` in exactly `⟨zhatGen^m⟩` (`χ_m (zhatGen^k) = 1 ↔ m ∣ k`), so
`ker χ_m = closure⟨zhatGen^m⟩ ⊆ S` (`IsOpen.inter_closure` + `Dense`). Now if `zhatToGalois x = 1`
but `x ≠ 1`, separation gives an open normal `H ∌ x`; taking `m := |Ẑ ⧸ H|`, Lagrange puts
`zhatGen^m ∈ H`, so `x ∈ ker χ_m ≤ H` — contradiction. Hence `ker zhatToGalois = ⊥`.

This is exactly the "procyclic ⟹ unique open subgroup of each finite index, cofinal" mechanism, but
realised directly via `ker χ_m = closure⟨zhatGen^m⟩` — no separate uniqueness lemma needed; the
`DiscreteTopology Gal(𝔽_{q^m}/K)` instance (`krullTopology_discreteTopology_of_finiteDimensional`)
makes `ker χ_m` open, and that plus density does the work.

## The closed iso

`galoisContinuousMulEquivZHat : Gal(𝔽_q̄/𝔽_q) ≃ₜ* Ẑ` — `zhatToGalois` is a continuous bijection of
compact Hausdorff groups (injective above + surjective Pass 6), hence a homeomorphism
(`Continuous.homeoOfEquivCompactToT2`); bundling its `map_mul` gives the `ContinuousMulEquiv`, and
`.symm` gives the classical direction `Gal ≅ Ẑ`.

## Honesty / scope

This is a genuine **closed whole**, not a half or infrastructure: the full topological-group
isomorphism, standard-axioms-only, **nothing posited** anywhere in the Pass 6–10 chain. It is the
structure of a *given* finite field's absolute Galois group — **recovers nothing from an abstract
group**, no reach toward R1–R3. No new `structure`/`class` (no rule-2 obligation); no load-bearing
hypothesis beyond the finiteness of `K`. The remaining open L1 item is the residue-surjection
boundary discharge (`residueReduction_surjective`, Pass 5), still blocked on the absent valuation on
`K̄` (`ROADMAP.md`).

## Axiom status

Standard axioms only (`#print axioms` below). Pass-10 ledger delta: **0 / 0** (no `DEBT`, no new
`FOUNDATIONAL`). The one existing `FOUNDATIONAL` entry (`residueReduction_surjective`, Pass 5) is
untouched and unused here — the iso is earned, not posited.
-/

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion

namespace Anabelian

variable (K : Type) [Field K] [Fintype K]

/-- The canonical map sends `Ẑ`'s generator `zhatGen = η(ofAdd 1)` to the absolute Frobenius. -/
lemma zhatToGalois_zhatGen : (Hom.hom (zhatToGalois K)) zhatGen = absFrobenius K := by
  rw [zhatGen, zhatToGalois_etaFn]; exact zpow_one _

/-- The composite `χ_m := r_m ∘ zhatToGalois : Ẑ →* Gal(𝔽_{q^m}/K)`. -/
noncomputable def levelComp (m : ℕ) [NeZero m] :
    (ZHat : Type) →* (levelField K m ≃ₐ[K] levelField K m) :=
  (levelRestrict K m).comp (Hom.hom (zhatToGalois K))

/-- `χ_m` sends `zhatGen` to the Frobenius generator `r_m (Frob)` of `Gal(𝔽_{q^m}/K)`. -/
lemma levelComp_zhatGen (m : ℕ) [NeZero m] :
    levelComp K m zhatGen = levelRestrict K m (absFrobenius K) :=
  congrArg (levelRestrict K m) (zhatToGalois_zhatGen K)

/-- **The cofinality core.** For any closed subgroup `S` of `Ẑ` containing `zhatGen^m`, the (open)
kernel of `χ_m` is contained in `S`. Because dense `⟨zhatGen⟩` meets the open `ker χ_m` exactly
in `⟨zhatGen^m⟩` (as `χ_m (zhatGen^k) = 1 ↔ m ∣ k`, using `orderOf (r_m Frob) = m`), we get
`ker χ_m = closure⟨zhatGen^m⟩ ⊆ S`. -/
lemma ker_levelComp_le (m : ℕ) [NeZero m] {S : Subgroup ZHat}
    (hScl : IsClosed (S : Set ZHat)) (hmem : zhatGen ^ m ∈ S) :
    MonoidHom.ker (levelComp K m) ≤ S := by
  haveI : FiniteDimensional K (levelField K m) := Module.Finite.of_finite
  have hopen : IsOpen ((MonoidHom.ker (levelComp K m)) : Set ZHat) := by
    have hcont : Continuous ⇑(levelComp K m) := by
      rw [levelComp, MonoidHom.coe_comp]
      exact (InfiniteGalois.restrictNormalHom_continuous (levelField K m)).comp
        (Hom.hom (zhatToGalois K)).continuous
    rw [MonoidHom.coe_ker]; exact hcont.isOpen_preimage _ (isOpen_discrete _)
  have hdense : Dense ((Subgroup.zpowers zhatGen) : Set ZHat) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe,
        zhat_topologicalClosure_eq_top, Subgroup.coe_top]
  have hsub : ((MonoidHom.ker (levelComp K m)) : Set ZHat) ∩ (Subgroup.zpowers zhatGen : Set ZHat)
      ⊆ (Subgroup.zpowers (zhatGen ^ m) : Set ZHat) := by
    rintro y ⟨hyk, hyz⟩
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hyz
    obtain ⟨k, rfl⟩ := hyz
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_zpow, levelComp_zhatGen] at hyk
    have hdvd : (m : ℤ) ∣ k := by
      rw [← orderOf_levelRestrict_frobenius K m]; exact orderOf_dvd_iff_zpow_eq_one.mpr hyk
    obtain ⟨j, rfl⟩ := hdvd
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff]
    exact ⟨j, by rw [← zpow_natCast (zhatGen) m, ← zpow_mul]⟩
  rw [← SetLike.coe_subset_coe]
  calc ((MonoidHom.ker (levelComp K m)) : Set ZHat)
      = _ ∩ Set.univ := (Set.inter_univ _).symm
    _ = _ ∩ closure (Subgroup.zpowers zhatGen : Set ZHat) := by rw [hdense.closure_eq]
    _ ⊆ closure (((MonoidHom.ker (levelComp K m)) : Set ZHat) ∩ _) := hopen.inter_closure
    _ ⊆ closure (Subgroup.zpowers (zhatGen ^ m) : Set ZHat) := closure_mono hsub
    _ ⊆ (S : Set ZHat) := closure_minimal (by
          rintro y hy
          rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hy
          obtain ⟨j, rfl⟩ := hy; exact S.zpow_mem hmem j) hScl

/-- **`zhatToGalois` is injective.** If `zhatToGalois x = 1` but `x ≠ 1`, separation gives an open
normal `H` with `x ∉ H`; with `m := |Ẑ ⧸ H|`, `zhatGen^m ∈ H` (Lagrange) so `ker χ_m ≤ H`, yet
`x ∈ ker χ_m` — contradiction. -/
theorem zhatToGalois_injective : Function.Injective ⇑(Hom.hom (zhatToGalois K)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hne
  obtain ⟨H, hH⟩ := exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_compl_singleton (x := x)) (Set.mem_compl_singleton_iff.mpr (Ne.symm hne))
  set m := Nat.card (ZHat ⧸ H.toSubgroup)
  haveI : NeZero m := ⟨Nat.card_pos.ne'⟩
  have hxker : x ∈ MonoidHom.ker (levelComp K m) :=
    MonoidHom.mem_ker.mpr ((congrArg (levelRestrict K m) hx).trans (map_one _))
  have hgm : zhatGen ^ m ∈ H.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    exact pow_card_eq_one'
  exact hH (ker_levelComp_le K m H.toOpenSubgroup.isClosed hgm hxker) rfl

/-- **`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`** as topological groups — the first L1 whole of depth, closed axiom-free.
`zhatToGalois` is a continuous bijection of compact Hausdorff groups, hence a homeo; bundling
`map_mul` and taking `.symm` gives the classical direction `Gal ≅ Ẑ`. -/
noncomputable def galoisContinuousMulEquivZHat : galoisProfinite K ≃ₜ* ZHat :=
  (show (ZHat : Type) ≃ₜ* (galoisProfinite K) from
    { Continuous.homeoOfEquivCompactToT2
        (f := Equiv.ofBijective _ ⟨zhatToGalois_injective K, zhatToGalois_surjective K⟩)
        (Hom.hom (zhatToGalois K)).continuous with
      map_mul' := (Hom.hom (zhatToGalois K)).map_mul' }).symm

-- Reproducible axiom audit. Standard axioms only — the iso is earned, not posited.
#print axioms zhatToGalois_injective
#print axioms galoisContinuousMulEquivZHat

end Anabelian
