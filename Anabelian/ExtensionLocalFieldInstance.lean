/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionSpectralSeam
import Anabelian.ExtensionValued
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Field.ProperSpace

/-!
# The assembly closes: `IsNonarchimedeanLocalField L` (Pass 41)

The capstone of the assembly opened at Pass 38. Mathlib defines `IsNonarchimedeanLocalField`
with three parents — `IsValuativeTopology`, `LocallyCompactSpace`, `ValuativeRel.IsNontrivial`
(everything else, DVR/finite-residue/completeness, is *derived* from these). Pass 38 discharged
parents 1 and 3 on the rung-1 valuative structure of `L`; this file discharges parent 2 and
assembles the class.

* **`isValuativeTopology_unique`** (abstract, reusable) — two topologies that are both valuative
  for the *same* valuative relation are equal. The neighborhood filters are pinned by the
  relation (`IsValuativeTopology.mem_nhds_iff`), independently of the topology.
* **`locallyCompactSpace_extensionValuativeRel`** — **parent 2, discharged**: `L` is locally
  compact in its rung-1 valuative topology. The proof is the honest conceptual one: `L` is a
  finite-dimensional normed space over the locally compact field `K` (spectral norm), hence
  *proper* (`FiniteDimensional.proper`), hence locally compact — and the rung-1 topology equals
  the spectral topology (`isValuativeTopology_unique`, using Pass 40's relation equality), so the
  property transports.
* **`isNonarchimedeanLocalField_extension`** — **the assembly theorem**: for finite separable
  `L/K` of nonarchimedean local fields, `IsNonarchimedeanLocalField L`.

## Honesty

The compactness criterion route (Passes 39–40 discharged all three of its conjuncts: DVR, finite
residue, completeness) would *also* assemble parent 2; this file takes the shorter
finite-dimensional-properness route for `LocallyCompactSpace` directly. The Pass 39/40 structural
theorems (`L` complete, `𝒪_L` a DVR with finite residue field) remain genuine and independently
useful — they are the local-field structure, recovered here for free *from* the class via Mathlib.

What is NOT claimed: base-independence of `extensionValuativeRel` across towers (the canonicity
obligation — the next pass; it gates `M/L/K` iteration). No new `structure`/`class`; no owed
witness; D1 N/A; D2 intact (the spectral structures live entirely inside proofs via `letI`, none
in any statement). Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel NNReal
open ValuativeRel IsLocalRing

/-- **`IsValuativeTopology` pins the topology**: two topologies on a commutative ring that are
both valuative for the *same* valuative relation coincide. The membership `s ∈ 𝓝 x` is
characterized by `IsValuativeTopology.mem_nhds_iff` purely in terms of the valuative relation —
the right-hand side does not mention the topology — so the neighborhood filters agree pointwise
and the topologies are equal (`TopologicalSpace.ext_nhds`). -/
theorem isValuativeTopology_unique {R : Type*} [CommRing R] [ValuativeRel R]
    {t₁ t₂ : TopologicalSpace R}
    (h₁ : @IsValuativeTopology R _ _ t₁) (h₂ : @IsValuativeTopology R _ _ t₂) : t₁ = t₂ := by
  refine TopologicalSpace.ext_nhds fun x => Filter.ext fun s => ?_
  rw [h₁.mem_nhds_iff, h₂.mem_nhds_iff]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

set_option synthInstance.maxHeartbeats 400000 in
-- `synthInstance.maxHeartbeats` raised exactly as in Passes 29/40: the `Valued.integer`/`Valued`
-- instance searches inside the spectral `letI` chain are expensive. Search cost only, not logical.
/-- **Parent 2 of `IsNonarchimedeanLocalField L`, discharged**: `L` is locally compact in its
rung-1 valuative topology. `L` is a finite-dimensional normed space over the locally compact
field `K` (spectral norm), hence proper, hence locally compact; the rung-1 topology equals the
spectral topology (Pass 40's relation equality + `isValuativeTopology_unique`), carrying the
property across. -/
theorem locallyCompactSpace_extensionValuativeRel [Algebra.IsSeparable K L] :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    LocallyCompactSpace L := by
  letI := extensionValuativeRel K L
  -- The spectral analytic structure on `K` and `L` (verbatim the Pass-40 chain), installing
  -- the spectral metric topology on `L` as the ambient `TopologicalSpace L`.
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
  letI nsL : NormedSpace K L := spectralNorm.normedSpace K L
  letI vL : Valued L ℝ≥0 := NormedField.toValued
  -- `L` is proper (finite-dimensional over the locally compact `K`), hence locally compact, in
  -- the spectral topology.
  haveI : ProperSpace L := FiniteDimensional.proper K L
  -- The rung-1 valuative topology equals the spectral topology.
  have hrel : extensionValuativeRel K L = ValuativeRel.ofValuation (Valued.v (R := L)) :=
    extensionValuativeRel_eq_spectral K L
  have h₂ : @IsValuativeTopology L _ (extensionValuativeRel K L) (by infer_instance) := by
    rw [hrel]
    letI : ValuativeRel L := ValuativeRel.ofValuation (Valued.v (R := L))
    haveI : (Valued.v (R := L)).Compatible := Valuation.Compatible.ofValuation _
    refine IsValuativeTopology.of_zero (fun s => ?_)
    rw [Valued.mem_nhds_zero]
    simpa using (Valued.v (R := L)).exists_setOf_restrict_le_iff 0 s
  have h₁ : @IsValuativeTopology L _ (extensionValuativeRel K L)
      (ValuativeRel.topologicalSpace L) := inferInstance
  have htop : (ValuativeRel.topologicalSpace L : TopologicalSpace L) = (by infer_instance) :=
    isValuativeTopology_unique h₁ h₂
  rw [htop]
  infer_instance

/-- **The assembly theorem**: every finite separable extension `L/K` of nonarchimedean local
fields is itself a nonarchimedean local field. The three parents of Mathlib's class are
discharged — `IsValuativeTopology` and `IsNontrivial` at Pass 38, `LocallyCompactSpace` here —
on the rung-1 valuative structure of `L` (`extensionValuativeRel`, induced by `𝒪_L`). -/
theorem isNonarchimedeanLocalField_extension [Algebra.IsSeparable K L] :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    IsNonarchimedeanLocalField L := by
  letI := extensionValuativeRel K L
  letI := ValuativeRel.topologicalSpace L
  haveI := isValuativeTopology_extensionValuativeRel K L
  haveI := isNontrivial_extensionValuativeRel K L
  haveI := locallyCompactSpace_extensionValuativeRel K L
  exact { }

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms isValuativeTopology_unique
#print axioms locallyCompactSpace_extensionValuativeRel
#print axioms isNonarchimedeanLocalField_extension

end Anabelian
