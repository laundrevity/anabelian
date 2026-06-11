/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.Topology.Algebra.Valued.ValuativeRel
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Anabelian.ExtensionLocalField
import Anabelian.ExtensionResidueFinite

/-!
# The assembly, rung 2: the `Valued` framework on `L` (Pass 39)

Toward `LocallyCompactSpace L` (the last parent of `IsNonarchimedeanLocalField L`). Mathlib's
locally-compactness characterization (`Topology/Algebra/Valued/LocallyCompact.lean`:
`CompactSpace 𝒪 ↔ CompleteSpace 𝒪 ∧ IsDiscreteValuationRing 𝒪 ∧ Finite 𝓀`) lives in the
`Valued` framework; Mathlib's porting helper makes `L` a `Valued` field **on the rung-1
structures** (the helper instance adopts the given uniformity, so no topology identification
is ever needed: `Valued.v = valuation L` is `rfl`). This file delivers the `Valued` side:

* **`valued_integer_eq_of_compatible`** (abstract, reusable) — the `Valued` integer ring of
  the helper structure is the compatible valuation subring.
* **`isDiscreteValuationRing_of_subring_eq`** / **`finite_residueField_of_subring_eq`**
  (abstract) — DVR-ness and residue-finiteness transport along subring equality
  (`RingEquiv.subringCongr`).
* **`valued_integer_extensionValuativeRel`** — concretely: under the rung-1 `letI`-tower,
  `L` is `Valued` and **its integer ring is `𝒪_L`** (as subrings of `L`).
* **`isDiscreteValuationRing_valued_integer`** / **`finite_residueField_valued_integer`** —
  two of the three conjuncts of the compactness criterion, transported from Pass 30 (DVR)
  and Pass 31 (finite residue field).

## Honesty

NOT claimed: the third conjunct (`CompleteSpace`), `CompactSpace` of the integer ring,
`LocallyCompactSpace L`, and the class assembly — the next rung (the completeness conjunct is
where the spectral norm finally enters, or an adic argument; inventoried, not done). No
spectral content appears in THIS file: the integer-ring identity is pure rung-1 bookkeeping
(`Compatible` + `valuation_le_one_iff`). The `letI`-tower in the statements is the
hypothesis-parametrized house pattern in topological clothing — still no global instances,
D2 intact. No new `structure`/`class`; no owed witness; D1 N/A. Recovers nothing from an
abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The `Valued` integer ring is the compatible valuation subring** (abstract, reusable):
under the porting-helper `Valued` structure of a valuative field, the integer ring is exactly
the valuation subring of any compatible valuation. -/
theorem valued_integer_eq_of_compatible {F : Type*} [Field F] [ValuativeRel F]
    [UniformSpace F] [IsUniformAddGroup F] [IsValuativeTopology F]
    (A : ValuationSubring F) [A.valuation.Compatible] :
    (Valued.v (R := F)).integer = A.toSubring := by
  have key : ∀ x : F, valuation F x ≤ valuation F 1 ↔ A.valuation x ≤ A.valuation 1 := fun x =>
    (Valuation.Compatible.vle_iff_le (v := valuation F) x 1).symm.trans
      (Valuation.Compatible.vle_iff_le (v := A.valuation) x 1)
  ext x
  rw [Valuation.mem_integer_iff, IsValuativeTopology.v_eq_valuation]
  constructor
  · intro hx
    have h2 := (key x).mp (by rwa [map_one])
    rw [map_one] at h2
    exact A.mem_of_valuation_le_one x h2
  · intro hx
    have h2 : A.valuation x ≤ A.valuation 1 := by
      rw [map_one]
      exact A.valuation_le_one ⟨x, hx⟩
    have h3 := (key x).mpr h2
    rwa [map_one] at h3

/-- DVR-ness transports along an equality of subrings. -/
theorem isDiscreteValuationRing_of_subring_eq {F : Type*} [Field F] {s t : Subring F}
    (h : s = t) [IsDiscreteValuationRing ↥s] : IsDiscreteValuationRing ↥t :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (RingEquiv.subringCongr h)

/-- Residue-field finiteness transports along an equality of (local) subrings. -/
theorem finite_residueField_of_subring_eq {F : Type*} [Field F] {s t : Subring F} (h : s = t)
    [IsLocalRing ↥s] [IsLocalRing ↥t] [Finite (ResidueField ↥s)] :
    Finite (ResidueField ↥t) :=
  Finite.of_equiv _ (ResidueField.mapEquiv (RingEquiv.subringCongr h)).toEquiv

/-- **`L` is `Valued` on the rung-1 structures, with integer ring `𝒪_L`**: under the
valuative relation, its topology, and its right uniformity, the porting-helper `Valued`
instance applies and its integer ring is exactly `extensionIntegers K L`. No topology
identification occurs — the helper adopts the given uniformity, and `Valued.v` is the
canonical valuation by `rfl`. -/
theorem valued_integer_extensionValuativeRel :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    letI := IsTopologicalAddGroup.rightUniformSpace L
    haveI := isUniformAddGroup_of_addCommGroup (G := L)
    (Valued.v (R := L)).integer = (extensionIntegers K L).toSubring := by
  letI := extensionValuativeRel K L
  letI := ValuativeRel.topologicalSpace L
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  haveI : (extensionIntegers K L).valuation.Compatible :=
    Valuation.Compatible.ofValuation (extensionIntegers K L).valuation
  exact valued_integer_eq_of_compatible (extensionIntegers K L)

/-- **Conjunct 2 of the compactness criterion**: the `Valued` integer ring of `L` is a DVR —
Pass 30's theorem, transported along the integer-ring identity. -/
theorem isDiscreteValuationRing_valued_integer [Algebra.IsSeparable K L] :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    letI := IsTopologicalAddGroup.rightUniformSpace L
    haveI := isUniformAddGroup_of_addCommGroup (G := L)
    IsDiscreteValuationRing ↥((Valued.v (R := L)).integer) := by
  letI := extensionValuativeRel K L
  letI := ValuativeRel.topologicalSpace L
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  haveI : IsDiscreteValuationRing ↥((extensionIntegers K L).toSubring) :=
    isDiscreteValuationRing_extensionIntegers K L
  exact isDiscreteValuationRing_of_subring_eq
    (valued_integer_extensionValuativeRel K L).symm

/-- **Conjunct 3 of the compactness criterion**: the residue field of the `Valued` integer
ring of `L` is finite — Pass 31's theorem, transported along the integer-ring identity. -/
theorem finite_residueField_valued_integer [Algebra.IsSeparable K L] :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    letI := IsTopologicalAddGroup.rightUniformSpace L
    haveI := isUniformAddGroup_of_addCommGroup (G := L)
    Finite (ResidueField ↥((Valued.v (R := L)).integer)) := by
  letI := extensionValuativeRel K L
  letI := ValuativeRel.topologicalSpace L
  letI := IsTopologicalAddGroup.rightUniformSpace L
  haveI := isUniformAddGroup_of_addCommGroup (G := L)
  haveI : IsDiscreteValuationRing ↥((extensionIntegers K L).toSubring) :=
    isDiscreteValuationRing_extensionIntegers K L
  haveI : IsDiscreteValuationRing ↥((Valued.v (R := L)).integer) :=
    isDiscreteValuationRing_of_subring_eq (valued_integer_extensionValuativeRel K L).symm
  haveI : Finite (ResidueField ↥((extensionIntegers K L).toSubring)) :=
    finite_residueField_extensionIntegers K L
  exact finite_residueField_of_subring_eq (valued_integer_extensionValuativeRel K L).symm

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms valued_integer_eq_of_compatible
#print axioms isDiscreteValuationRing_of_subring_eq
#print axioms finite_residueField_of_subring_eq
#print axioms valued_integer_extensionValuativeRel
#print axioms isDiscreteValuationRing_valued_integer
#print axioms finite_residueField_valued_integer

end Anabelian
