/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.GaloisIntegersLocal
import Anabelian.ResidueAlgClosed
import Mathlib
-- `import Mathlib` (sanctioned fallback, CLAUDE.md): the residue-identification bricks draw on the
-- `IsLocalRing.ResidueField`/`local_hom_TFAE`/`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`/
-- `IsAlgClosure`/`AlgEquiv.autCongr` APIs across many modules (uncertain transitive instances), so
-- the broad import is honest here.

/-!
# Rung L1, discharging the `DEBT`: the residue identification 𝓀̄ ≅ AlgebraicClosure 𝓀[K] (Pass 19)

The discharge of `residueReduction_surjective` (perfect case) applies
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` to `G = Gal(K̄/K)`,
`B = 𝒪[K̄] = integralClosure 𝒪[K] K̄`, `A = 𝒪[K]`, `Q = 𝔪[K̄]`, `P = 𝔪[K]`. Bricks done: 1, 1b, 2a,
2b, **3a** (`isLocalRing_galoisIntegers`: `𝒪[K̄]` local, so `𝔪[K̄]` is THE maximal ideal), **3c**
(`galoisResidueField_isAlgClosed`: the residue field at any maximal ideal is algebraically closed).

This pass builds the **residue identification** and the connective tissue *below* the keystone
application:

* `galoisIntegers_isLocalHom` — **connective tissue.** `algebraMap 𝒪[K] 𝒪[K̄]` is a **local hom**:
  the integral extension's `comap` of `𝔪[K̄]` is maximal
  (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`) hence `= 𝔪[K]` (local), which is
  `local_hom_TFAE`
  clause 4 ⟹ `IsLocalHom` (clause 0). This unlocks, **for free**, both `(𝔪[K̄]).LiesOver (𝔪[K])`
  (the keystone's `Q.LiesOver P`) and `Algebra 𝓀[K] 𝓀̄` (the residue-field functoriality).
* `galoisResidueEquiv` — **bricks 3b + 3d.** `𝓀̄ := ResidueField 𝒪[K̄] ≃ₐ[𝓀[K]] AlgebraicClosure
  𝓀[K]`.
  Brick **3b** (`Algebra.IsAlgebraic 𝓀[K] 𝓀̄`) is proved element-wise: a residue class `mk b` lifts
  to
  `b` integral over `𝒪[K]` (monic `q`), whose reduction `q.map (algebraMap 𝒪[K] 𝓀[K])` is monic and
  kills `mk b` (`aeval_map_algebraMap` + `aeval_algHom_apply`). With brick **3c** (`IsAlgClosed
  𝓀̄`),
  `IsAlgClosure 𝓀[K] 𝓀̄` holds, and `IsAlgClosure.equiv` gives the iso (uniqueness of algebraic
  closures).
* `galoisResidueAut` — **brick 3e.** `Aut(𝓀̄/𝓀[K]) ≃* Field.absoluteGaloisGroup 𝓀[K]`, the
  `AlgEquiv`
  group transported along `galoisResidueEquiv` (`AlgEquiv.autCongr`).

## `DEBT` status: OPEN — not discharged (this is a clean partial)

The `axiom residueReduction_surjective` is **still present**. This pass completes the **residue
identification** (3b/3c/3d/3e) + connective tissue (`IsLocalHom` ⟹ `LiesOver`); it does **not**
reach
**Step 4** (the keystone application). **Route-steps remaining for the discharge: [connective:
`stabilizer G 𝔪[K̄] = ⊤` (the unique maximal ideal of the local `𝒪[K̄]` is Galois-stable); **Step
4**:
instantiate `stabilizerHom_surjective_of_profinite` with `G/B/A/P/Q` and the assembled instances
(`G`
profinite via `[PerfectField K]`+`IsGalois K K̄`, discrete `B`, etc.), reinterpret `stabilizer G Q ↠
Aut((B/Q)/(A/P))` as `Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K]` (via
`stabilizer = ⊤`, `B/Q = 𝓀̄`, `A/P = 𝓀[K]`, and `galoisResidueAut`), **delete the axiom** for a
`[PerfectField K]` theorem].** Stopping here (rather than half-assembling Step 4) is the honest call
—
nothing is posited; all bricks are *proved*, the surjection is to be *applied* from a present
theorem.
Note these residue bricks need **no `PerfectField`** (only Step 4 does).

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2). D1 N/A; **D2** is 3a's localized incursion (in
`GaloisIntegersLocal`),
unchanged — this file introduces no further D2 (the residue-field/`IsAlgClosure` API is
`ValuativeRel`-
and quotient-native).
-/

open scoped ValuativeRel
open ValuativeRel IsLocalRing Polynomial

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

-- 3a (`isLocalRing_galoisIntegers`) registered as an instance so the residue-field statements below
-- elaborate (`ResidueField 𝒪[K̄]` requires `IsLocalRing 𝒪[K̄]`).
attribute [local instance] isLocalRing_galoisIntegers

/-- **Connective tissue.** The structure map `algebraMap 𝒪[K] 𝒪[K̄]` is a **local homomorphism**:
the
`comap` of `𝔪[K̄]` under the integral extension is maximal
(`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`), hence equals `𝔪[K]` (`𝒪[K]` local), which is
`local_hom_TFAE` clause 4 ⟹ `IsLocalHom`. This gives `(𝔪[K̄]).LiesOver (𝔪[K])` and `Algebra 𝓀[K] 𝓀̄`
for free. -/
instance galoisIntegers_isLocalHom :
    IsLocalHom (algebraMap ↥𝒪[K] ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) := by
  haveI : Algebra.IsIntegral ↥𝒪[K] ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) :=
    integralClosure.AlgebraIsIntegral
  exact ((local_hom_TFAE _).out 4 0).mp (eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (maximalIdeal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)))))

set_option synthInstance.maxHeartbeats 800000 in
-- `synthInstance.maxHeartbeats` raised: the `Module.IsTorsionFree`/`IsAlgClosure` searches for
-- `IsAlgClosure.equiv` are expensive under `import Mathlib` + the Anabelian instances; they resolve
-- just past the 20000 default. A search-cost matter, not logical (`#print axioms` stays standard).
/-- **Bricks 3b + 3d.** The residue field `𝓀̄ := ResidueField 𝒪[K̄]` is `𝓀[K]`-isomorphic to
`AlgebraicClosure 𝓀[K]`. Brick 3b (`Algebra.IsAlgebraic 𝓀[K] 𝓀̄`) is element-wise (reduce a lifted
monic minimal polynomial); with brick 3c (`IsAlgClosed 𝓀̄`), `IsAlgClosure 𝓀[K] 𝓀̄` holds and
`IsAlgClosure.equiv` supplies the iso. -/
noncomputable def galoisResidueEquiv :
    (ResidueField ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) ≃ₐ[𝓀[K]]
      AlgebraicClosure 𝓀[K] := by
  set B := ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) with hB
  haveI : Algebra.IsIntegral ↥𝒪[K] B := integralClosure.AlgebraIsIntegral
  haveI h3c : IsAlgClosed (ResidueField B) := galoisResidueField_isAlgClosed K (maximalIdeal B)
  haveI hst : IsScalarTower ↥𝒪[K] 𝓀[K] (ResidueField B) := by
    apply IsScalarTower.of_algebraMap_eq; intro a
    rw [IsScalarTower.algebraMap_apply ↥𝒪[K] B (ResidueField B)]; rfl
  haveI h3b : Algebra.IsAlgebraic 𝓀[K] (ResidueField B) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, hqm, hqa⟩ := Algebra.IsIntegral.isIntegral (R := ↥𝒪[K]) b
    refine ⟨q.map (algebraMap ↥𝒪[K] 𝓀[K]), (hqm.map _).ne_zero, ?_⟩
    rw [aeval_map_algebraMap 𝓀[K]]
    have hmk : (Ideal.Quotient.mk (maximalIdeal B)) b
        = (IsScalarTower.toAlgHom ↥𝒪[K] B (ResidueField B)) b := rfl
    rw [hmk, aeval_algHom_apply, aeval_def, hqa, map_zero]
  haveI : IsAlgClosure 𝓀[K] (ResidueField B) := ⟨h3c, h3b⟩
  exact IsAlgClosure.equiv 𝓀[K] (ResidueField B) (AlgebraicClosure 𝓀[K])

/-- **Brick 3e.** Transporting the `AlgEquiv` group along `galoisResidueEquiv` identifies
`Aut(𝓀̄/𝓀[K])` with `Field.absoluteGaloisGroup 𝓀[K]` — the residue Galois group the keystone's
output must become. -/
noncomputable def galoisResidueAut :
    ((ResidueField ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) ≃ₐ[𝓀[K]]
        (ResidueField ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)))) ≃*
      Field.absoluteGaloisGroup 𝓀[K] :=
  AlgEquiv.autCongr (galoisResidueEquiv K)

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms galoisIntegers_isLocalHom
#print axioms galoisResidueEquiv
#print axioms galoisResidueAut

end Anabelian
