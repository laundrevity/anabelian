/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueReductionIntegral
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.MulAction

/-!
# Rung L1, discharging the `DEBT`: Step 2b (`ContinuousSMul`) + the residue-iso verdict (Pass 15)

## Primary deliverable: the residue-identification tractability verdict

The discharge of `residueReduction_surjective` (perfect case) applies
`stabilizerHom_surjective_of_profinite` to `G = Gal(K̄/K)`, `B = 𝒪[K̄] = integralClosure 𝒪[K] K̄`,
`A = 𝒪[K]`, `Q = 𝔪[K̄]`. The one remaining hard step was the **residue identification** `𝒪[K̄]/𝔪[K̄]
≅
AlgebraicClosure 𝓀[K]` (Pass 14's pinpointed blocker). Front-loaded its tractability:

**Verdict — a BOUNDED multi-pass sub-plan, not a wall.** It decomposes into strictly-lower bricks:
- **3a. `𝒪[K̄]` local + `Q = 𝔪[K̄]`** — `𝒪[K̄] = integralClosure 𝒪[K] K̄` is the valuation ring of
the
  (unique, as `𝒪[K]` is complete/Henselian) extension of the valuation to `K̄`. **ABSENT as a direct
  lemma** (no `IsLocalRing (integralClosure …)` / valuation-extension-uniqueness-to-`K̄`); reachable
  via
  the valuation-integral-closure API (`RingTheory/Valuation/AlgebraInstances.lean`) or the Pass-11
  `spectralIntegers` valuation ring (the latter would re-introduce the `NormedField` bridge / **D2**
  —
  prefer the `ValuativeRel`-native route). **Substantial.**
- **3b. residue `𝓀̄ := 𝒪[K̄]/𝔪[K̄]` algebraic over `𝓀[K]`** — each residue class lifts to an element
  integral over `𝒪[K]`, hence algebraic. Moderate.
- **3c. `𝓀̄` algebraically closed** — **ABSENT** (no `IsAlgClosed`-of-residue-field API). Provable
  from-scratch: a monic poly over `𝓀̄` lifts to a monic poly over `𝒪[K̄] ⊆ K̄`, which has a root in
  the
  algebraically closed `K̄`; that root is integral (monic), hence in `𝒪[K̄]`, and reduces to a root
  in
  `𝓀̄`. (Note: this uses `K̄` algebraically closed + integral-closure, **not** Henselianness — `K̄`
  is
  *not* complete, so `𝒪[K̄]` is *not* Henselian; the naive Hensel route does not apply.)
  **Substantial.**
- **3d. `𝓀̄ ≅ AlgebraicClosure 𝓀[K]`** — from 3b+3c via `isAlgClosure_iff` (`IsAlgClosed ∧
  Algebra.IsAlgebraic ↔ IsAlgClosure`) + `IsAlgClosure.equiv` (uniqueness of algebraic closures).
  **PRESENT/supported.**
- **3e. `Aut(𝓀̄/𝓀[K]) ≅ Field.absoluteGaloisGroup 𝓀[K]`** — transport the `Aut` group along 3d's
iso.
  Moderate; supported.

So the residue iso is reachable but genuinely **multi-pass** (3a and 3c are the substantial
from-scratch
pieces; 3d/3e are supported). Discharge is ~2–3 further passes away. **Not a wall — but not one
pass.**

## Built this pass — Step 2b (`ContinuousSMul`, the keystone's other remaining hypothesis)

* `Anabelian.galoisStabilizer_isOpen` — for the Galois action on `𝒪[K̄] = integralClosure 𝒪[K] K̄`,
  every point's stabilizer in `Gal(K̄/K)` is **open** (Krull topology): the stabilizer of `b` equals
  that of `(b : K̄)`, open by `stabilizer_isOpen_of_isIntegral` (`K̄/K` integral).
* `Anabelian.continuousSMul_galoisIntegers` — hence, with the **discrete** topology on `𝒪[K̄]` (the
  keystone's choice, made explicit), the action `Gal(K̄/K) ↻ 𝒪[K̄]` is `ContinuousSMul`
  (`continuousSMul_iff_stabilizer_isOpen`). This is **Step 2b** — `DiscreteTopology B` +
  `ContinuousSMul
  G B`, two of the keystone's hypotheses — now discharged, strictly-lower, axiom-free.

## `DEBT` status: OPEN — not discharged

The `axiom residueReduction_surjective` is **still present**. **Route-steps remaining: [Step 3a–3c
(the
residue iso — `𝒪[K̄]` local + `𝔪[K̄]`, residue algebraic, residue algebraically-closed — the
substantial
remainder); Step 3d/3e (supported); Step 4 apply keystone + delete axiom, perfect-case narrowing].**
Done: steps 1, 1b, 2a (Passes 13–14), 2b (this pass). **Nothing cardinal-sin posited** — no sub-step
stubbed; the residue iso is to be *built*, the surjection *applied* from a present theorem. Ledger
unchanged at `0 FOUNDATIONAL / 1 DEBT`.

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2). D1 N/A; **D2 not incurred** (`ValuativeRel`/integral-closure route;
the
`spectralNorm` re-entry for 3a is noted as a D2 risk to avoid).
-/

open scoped ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- For the Galois action on `𝒪[K̄] = integralClosure 𝒪[K] K̄`, every stabilizer in `Gal(K̄/K)` is
**open** (Krull topology) — it equals the stabilizer of the underlying element of `K̄`, open since
`K̄/K` is integral (`stabilizer_isOpen_of_isIntegral`). -/
theorem galoisStabilizer_isOpen (b : ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) :
    IsOpen ((MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) b :
      Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))) := by
  have heq : (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) b :
        Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
      = (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (b : AlgebraicClosure K) : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
    ext σ
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [heq]
  exact stabilizer_isOpen_of_isIntegral (b : AlgebraicClosure K)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- **Step 2b:** with the discrete topology on `𝒪[K̄]` (the keystone's hypothesis), the Galois
action
`Gal(K̄/K) ↻ 𝒪[K̄]` is continuous — because every stabilizer is open
(`continuousSMul_iff_stabilizer_isOpen` + `galoisStabilizer_isOpen`). -/
theorem continuousSMul_galoisIntegers :
    letI : TopologicalSpace ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := ⊥
    ContinuousSMul (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
      ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := by
  letI : TopologicalSpace ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := ⊥
  haveI : DiscreteTopology ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) := ⟨rfl⟩
  rw [continuousSMul_iff_stabilizer_isOpen]
  exact galoisStabilizer_isOpen K

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms galoisStabilizer_isOpen
#print axioms continuousSMul_galoisIntegers

end Anabelian
