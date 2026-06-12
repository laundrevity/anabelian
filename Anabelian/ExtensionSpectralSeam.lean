/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionLocalField
import Anabelian.ValuativeRelCongr

/-!
# The assembly, rung 3: the spectral seam (Pass 40)

The completeness conjunct of the compactness criterion lives on the rung-1 uniformity; the
completeness theorems live on the spectral norm. This file crosses the seam **as equalities**:

* **`mem_extensionIntegers_iff_mem_valued_integer`** — Pass 29's internal `hmem`, exported:
  `𝒪_L` is exactly the unit ball of the spectral norm (the proof is verbatim P29's, from
  inside the `extensionIntegers` definition — minpoly coefficients + `spectralValue_le_one_iff`).
* **`extensionValuativeRel_eq_spectral`** — therefore the rung-1 relation **equals**
  `ofValuation` of the spectral valuation (`ofValuation_eq_of_same_subring`): the topology
  identification downstream is an honest `rw`, not a homeomorphism argument.
* **`completeSpace_spectral`** — `L` is complete in the spectral norm: `spectralNorm.normedSpace`
  + `FiniteDimensional.complete` over the Pass-17 bridge (`Valued.toNontriviallyNormedField`).

## Honesty

NOT claimed: completeness on the rung-1 tower (needs the `IsValuativeTopology`-uniqueness
lemma — next rung, probed route), `CompactSpace`, `LocallyCompactSpace L`, the class assembly.
The `letI`-blocks are P29's spectral block verbatim (same `synthInstance.maxHeartbeats`
raise, same reason — search cost only, not logical). No new `structure`/`class`; no owed
witness; D1 N/A; D2 intact (no instances declared). Recovers nothing from an abstract group;
R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel NNReal
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

set_option synthInstance.maxHeartbeats 400000 in
-- `synthInstance.maxHeartbeats` raised exactly as in Pass 29: the `Valued.integer` instance
-- searches inside the spectral `letI` chain are expensive. Search cost only, not logical.
/-- **Pass 29's `hmem`, exported**: `𝒪_L` is the unit ball of the spectral norm. The proof is
verbatim the one inside the `extensionIntegers` definition. -/
theorem mem_extensionIntegers_iff_mem_valued_integer :
    letI := IsTopologicalAddGroup.rightUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    letI : NormedField L := spectralNorm.normedField K L
    haveI : IsUltrametricDist L :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
        (isNonarchimedean_spectralNorm (K := K) (L := L))
    letI : Valued L ℝ≥0 := NormedField.toValued
    ∀ x : L, x ∈ extensionIntegers K L ↔ x ∈ Valued.integer L := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI rk : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI nnf : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  letI nfL : NormedField L := spectralNorm.normedField K L
  haveI ultL : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  letI vL : Valued L ℝ≥0 := NormedField.toValued
  intro x
  have halg : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  rw [Valuation.mem_integer_iff]
  change IsIntegral ↥𝒪[K] x ↔ _
  rw [isIntegral_iff_minpoly_coeff_mem_findim K L x]
  have hvy : (Valued.v x ≤ (1 : ℝ≥0)) ↔ spectralNorm K L x ≤ 1 := by
    rw [show Valued.v x = ‖x‖₊ from rfl, show spectralNorm K L x = ‖x‖ from rfl]
    exact_mod_cast Iff.rfl
  rw [hvy, show spectralNorm K L x = spectralValue (minpoly K x) from rfl,
      spectralValue_le_one_iff (minpoly.monic halg)]
  refine forall_congr' (fun i => ?_)
  rw [Valued.toNormedField.norm_le_one_iff]
  exact Iff.rfl

set_option synthInstance.maxHeartbeats 400000 in
-- Same raise as above (the statement elaborates the same spectral `letI` chain).
/-- **The rung-1 relation equals the spectral relation**: same unit ball (`hmem`), hence
equal valuative relations — the seam crossed as an equality. -/
theorem extensionValuativeRel_eq_spectral :
    letI := IsTopologicalAddGroup.rightUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    letI : NormedField L := spectralNorm.normedField K L
    haveI : IsUltrametricDist L :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
        (isNonarchimedean_spectralNorm (K := K) (L := L))
    letI : Valued L ℝ≥0 := NormedField.toValued
    extensionValuativeRel K L = ValuativeRel.ofValuation (Valued.v (R := L)) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI rk : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI nnf : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  letI nfL : NormedField L := spectralNorm.normedField K L
  haveI ultL : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (isNonarchimedean_spectralNorm (K := K) (L := L))
  letI vL : Valued L ℝ≥0 := NormedField.toValued
  exact ofValuation_eq_of_same_subring (extensionIntegers K L) (Valued.v (R := L))
    (fun x => (Valuation.mem_integer_iff _ _).symm.trans
      ((mem_extensionIntegers_iff_mem_valued_integer K L x).symm))

set_option synthInstance.maxHeartbeats 400000 in
-- Same raise as above.
/-- **`L` is complete in the spectral norm**: finite-dimensional over the complete `K`
(`spectralNorm.normedSpace` + `FiniteDimensional.complete`). -/
theorem completeSpace_spectral :
    letI := IsTopologicalAddGroup.rightUniformSpace K
    haveI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    letI : NontriviallyNormedField K :=
      Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
    letI : NormedField L := spectralNorm.normedField K L
    CompleteSpace L := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI rk : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI nnf : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  letI nfL : NormedField L := spectralNorm.normedField K L
  letI nsL := spectralNorm.normedSpace K L
  exact FiniteDimensional.complete K L

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms mem_extensionIntegers_iff_mem_valued_integer
#print axioms extensionValuativeRel_eq_spectral
#print axioms completeSpace_spectral

end Anabelian
