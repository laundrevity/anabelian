/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueReductionIntegral
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Rung L1, discharging the `DEBT`: the fixed-ring `𝒪[K̄]^Gal = 𝒪[K]` + the generality decision (Pass
14)

## Job B — the generality decision (investigated and documented; NOT optional)

The keystone `stabilizerHom_surjective_of_profinite` needs `G = Gal(K̄/K)` **profinite**, i.e.
`IsGalois K (AlgebraicClosure K)`, which holds **iff `K` is perfect** (`PerfectField K` ⟹ `IsGalois
K
K̄`). Mixed-characteristic / char-0 local fields (finite extensions of `ℚ_p`) are perfect; imperfect
equal-characteristic ones (`𝔽_q((t))`) are **not** (`K̄/K` is inseparable).

**Is `residueReduction_surjective` true *as stated* for imperfect `K`?** Investigated: **yes, it is
true** — but for a reason orthogonal to the keystone's hypothesis. `Field.absoluteGaloisGroup K =
Aut(K̄/K)`; for imperfect `K`, `K̄/K^sep` is purely inseparable, so every `K`-automorphism of `K̄`
is
determined by its (rigid) restriction to `K^sep`, giving `Aut(K̄/K) ≅ Gal(K^sep/K)` (profinite). The
residue field `𝓀[K]` is **finite, hence perfect**, so the residue reduction `Gal(K^sep/K) ↠
Gal(𝓀̄/𝓀)`
holds by the standard unramified theory. So the statement holds for all local fields — but the
keystone
*as applied here* only delivers it where `Gal(K̄/K)` is **literally** profinite via `IsGalois K K̄`
(the perfect case); the imperfect case needs the separable-closure framing.

**Decision: option (a) — narrow to the perfect case, track the imperfect case.** When the discharge
lands (a later pass, once the residue identification below is built), the replacing `theorem` will
carry `[PerfectField K]` (or `[IsGalois K (AlgebraicClosure K)]`), the narrowing will be documented
in
its docstring and the ledger, and the **imperfect equal-characteristic case will be a named tracked
remainder** (`ROADMAP.md`), never silently dropped. This pass does **not** remove the axiom, so no
narrowing is enacted yet — only decided and recorded.

## Job A — the fixed-ring identification (step 2 core, this pass, perfect case)

* `Anabelian.galoisIntegers_algebraIsInvariant` — **`Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal`** for
perfect
  `K`, i.e. the Galois-fixed subring of `𝒪[K̄] = integralClosure 𝒪[K] K̄` is exactly `𝒪[K]`
  (`𝒪[K̄]^Gal = 𝒪[K]`). Proof: a `Gal`-fixed `b` has `(b : K̄) ∈ fixedField ⊤ = (⊥ :
  IntermediateField
  K K̄) = K` (`InfiniteGalois.fixedField_fixingSubgroup`), and `b` is integral over `𝒪[K]`;
  integrality
  descends through the injective `K → K̄`, and `𝒪[K]` is integrally closed in its fraction field `K`
  (`IsIntegrallyClosed.isIntegral_iff`), so `b ∈ 𝒪[K]`. This is one of the keystone's hypotheses
  (`Algebra.IsInvariant A B G`), now discharged for the perfect case — strictly-lower, axiom-free.

## `DEBT` status: OPEN — not discharged; the blocker is the residue identification

The `axiom residueReduction_surjective` is **still present**. **The discharge blocker (re-confirmed
Pass
14): `𝒪[K̄]/𝔪[K̄] ≅ AlgebraicClosure 𝓀[K]`** — "the residue field of `K̄` is the algebraic closure
of
`𝓀[K]`" — is **ABSENT from Mathlib** (no `ResidueField`-of-algebraic-closure API) and a substantial
sub-construction. **Route-steps remaining:** [Step 2 (cont.): `DiscreteTopology` on `B` +
`ContinuousSMul G B` — the keystone's other hypotheses; Step 3: the residue iso + `Aut = Gal(𝓀̄/𝓀)`
+
`stabilizer 𝔪[K̄] = ⊤`; Step 4: apply the keystone, delete the axiom, with the perfect-case
narrowing
documented]. **Nothing cardinal-sin posited** — no sub-step is stubbed with a new `DEBT`; the
surjection
is a present theorem to be *applied*. Ledger unchanged at `0 FOUNDATIONAL / 1 DEBT`.

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2 obligation). D1 N/A; **D2 not incurred** (integral-closure route, no
`NormedField` bridge).
-/

open scoped ValuativeRel

namespace Anabelian

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [PerfectField K]

/-- **`𝒪[K̄]^Gal = 𝒪[K]`** (perfect `K`): the Galois-fixed subring of the integral closure
`𝒪[K̄] = integralClosure 𝒪[K] K̄` is exactly the ring of integers `𝒪[K]`. This is the keystone
hypothesis `Algebra.IsInvariant A B G` (step 2 core), discharged for the perfect case. A `Gal`-fixed
element lies in `fixedField ⊤ = K` and is integral over `𝒪[K]`, hence in `𝒪[K]` (integrally closed).
-/
instance galoisIntegers_algebraIsInvariant :
    Algebra.IsInvariant ↥𝒪[K] ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := by
  constructor
  intro b hb
  have hmem : (b : AlgebraicClosure K) ∈ (⊥ : IntermediateField K (AlgebraicClosure K)) := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K)),
        IntermediateField.fixingSubgroup_bot, IntermediateField.mem_fixedField_iff]
    intro g _
    exact congrArg Subtype.val (hb g)
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hmem
  have hkint : IsIntegral ↥𝒪[K] k := by
    apply (isIntegral_algebraMap_iff (B := AlgebraicClosure K)
      (FaithfulSMul.algebraMap_injective K (AlgebraicClosure K))).mp
    rw [hk]; exact b.2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkint
  refine ⟨a, ?_⟩
  apply Subtype.ext
  rw [← hk, ← ha]
  exact (IsScalarTower.algebraMap_apply ↥𝒪[K] K (AlgebraicClosure K) a).symm

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms galoisIntegers_algebraIsInvariant

end Anabelian
