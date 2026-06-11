/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
import Anabelian.ExtensionUniformizer

/-!
# The assembly, rung 1: the valuative structure on `L` (Pass 38)

Toward `IsNonarchimedeanLocalField L` for finite separable `L/K` — the gate to towers
(`M/L/K`), to intermediate fields as base fields, and hence to Herbrand's theorem in the
ascent. Mathlib defines the class (`IsValuativeTopology` + `LocallyCompactSpace` +
`ValuativeRel.IsNontrivial`, everything else derived) but ships no finite-extension instance;
this file begins the assembly:

* **`extensionValuativeRel`** — the valuative relation on `L`, induced by the valuation of the
  valuation subring `𝒪_L = extensionIntegers K L` (Pass 29) via `ValuativeRel.ofValuation`.
* **`isNontrivial_ofValuation`** — the reusable bridge: any valuation on a field admitting an
  element of value strictly between `0` and `1` induces a *nontrivial* valuative relation
  (through the `Valuation.Compatible` API).
* **`isNontrivial_extensionValuativeRel`** — parent 3 of the class, discharged: the Pass-30
  uniformizer witnesses nontriviality.
* **`isValuativeTopology_extensionValuativeRel`** — parent 1, free: under the valuative
  topology (Mathlib's deliberately-local `ValuativeRel.topologicalSpace`), the topology is
  valuative by the upstream instance.

## Design (the D2 discipline)

**No global instances are declared.** `extensionValuativeRel` depends on the base `K`; for a
tower `M/L/K` the relations on `L` built from different bases agree only up to a
base-independence theorem (not yet proved — named here as the canonicity obligation of a later
pass). Global instances would make that propositional identity a diamond. Mathlib's own design
says the same: `ValuativeRel.topologicalSpace` is a `local instance` upstream "to avoid
diamonds", with by-hand discharge intended. All downstream theorems therefore take the
structures via `letI`, exactly as the abstract ramification theory takes its hypotheses.

## Honesty

What is NOT claimed: `LocallyCompactSpace L` (the remaining parent — the next rung, via the
finite-dimensional route over the Pass-17 normed bridge); `IsNonarchimedeanLocalField L`
itself; base-independence of `extensionValuativeRel` across towers. Rule-2 note for the
construction: the relation is pinned against the degenerate model — the *trivial* valuative
relation also exists on `L`, and `isNontrivial_extensionValuativeRel` is precisely the proof
that this construction is not it. No new `structure`/`class`; no owed witness; D1 N/A; D2
respected as above. Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The valuative relation on `L`**, induced by the valuation of `𝒪_L` (Pass 29's valuation
subring). Deliberately a `def`, not an instance — see the design note in the module docstring:
its base-independence across towers is a theorem owed to a later pass, and instances would turn
that propositional identity into a diamond. Marked `@[reducible]` (the linter's requirement
for definitions of class type) so `letI`-discharge and unification see through the wrapper —
the same reason upstream `ofValuation` is `@[implicit_reducible]`. -/
@[reducible] noncomputable def extensionValuativeRel : ValuativeRel L :=
  ValuativeRel.ofValuation (extensionIntegers K L).valuation

/-- **The nontriviality bridge** (reusable, abstract): a valuation on a field with an element
of value strictly between `0` and `1` induces a nontrivial valuative relation. -/
theorem isNontrivial_ofValuation {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) (π : F) (h0 : v π ≠ 0) (h1 : v π < 1) :
    letI := ValuativeRel.ofValuation v
    ValuativeRel.IsNontrivial F := by
  letI := ValuativeRel.ofValuation v
  haveI hc : v.Compatible := Valuation.Compatible.ofValuation v
  refine ⟨⟨valuation F π, ?_, ?_⟩⟩
  · intro h
    have h2 : v π ≤ v 0 := (v.vle_iff_le).mp (valuation_eq_zero_iff.mp h)
    rw [map_zero] at h2
    exact h0 (le_zero_iff.mp h2)
  · have hv : π <ᵥ (1 : F) := (v.vlt_iff_lt).mpr (by rwa [map_one])
    have hcan : valuation F π < valuation F 1 := ((valuation F).vlt_iff_lt).mp hv
    rw [map_one] at hcan
    exact ne_of_lt hcan

/-- **Parent 3 of `IsNonarchimedeanLocalField L`, discharged**: the valuative relation on `L`
is nontrivial — witnessed by a Pass-30 uniformizer of `𝒪_L`. -/
theorem isNontrivial_extensionValuativeRel [Algebra.IsSeparable K L] :
    letI := extensionValuativeRel K L
    ValuativeRel.IsNontrivial L := by
  obtain ⟨π, hspan, hπ0⟩ := exists_uniformizer_extensionIntegers K L
  have hπL : (π : L) ≠ 0 := by exact_mod_cast hπ0
  refine isNontrivial_ofValuation ((extensionIntegers K L).valuation) (π : L) ?_ ?_
  · exact ((extensionIntegers K L).valuation.ne_zero_iff).mpr hπL
  · exact (ValuationSubring.valuation_lt_one_iff (extensionIntegers K L) π).mp
      (by rw [hspan]; exact Ideal.mem_span_singleton_self π)

/-- **Parent 1 of `IsNonarchimedeanLocalField L`, free**: under the valuative topology, the
topology on `L` is valuative — Mathlib's upstream instance applies on the nose. -/
theorem isValuativeTopology_extensionValuativeRel :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    IsValuativeTopology L := by
  letI := extensionValuativeRel K L
  letI := ValuativeRel.topologicalSpace L
  infer_instance

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms extensionValuativeRel
#print axioms isNontrivial_ofValuation
#print axioms isNontrivial_extensionValuativeRel
#print axioms isValuativeTopology_extensionValuativeRel

end Anabelian
