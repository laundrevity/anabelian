/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ExtensionMonogenicGeneral

/-!
# The descent, rung 7 (first half): the inertia orbit polynomial (Pass 35)

Toward `hresid` (inertia-fixed integers cover the residue field — the one lemma the general
kernel theorem awaits). The engine of the proof is the **inertia orbit polynomial**
`∏_{σ ∈ G₀} (X − σ•b)` (Mathlib's `MulSemiringAction.charpoly`, over the subgroup `G₀`), with
the two bricks:

* **`coeff_inertiaCharpoly_mem`** — its coefficients are **inertia-fixed** (the coefficients
  are symmetric functions of the orbit, permuted by `G₀` — Mathlib's `smul_coeff_charpoly`).
* **`map_residue_inertiaCharpoly`** — its residue is **`(X − b̄)^{|G₀|}`** (inertia fixes
  residues — Pass 24's lemma — so every factor collapses).

Together: for any `b ∈ 𝒪_L` with residue `b̄`, every coefficient of `(X − b̄)^{|G₀|}` is the
residue of an inertia-fixed integer. The second half (`Anabelian/InertiaResidueCover.lean`,
Pass 36) extracts `m·b̄^{p^a}` from the right coefficient (`|G₀| = p^a·m`, freshman's dream) and
runs the cyclic-generator argument to conclude `hresid`.

## Honesty

Bricks only; `hresid` itself is NOT claimed here. No new `structure`/`class`; no owed witness;
D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel IsLocalRing Polynomial

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The coefficients of the inertia orbit polynomial are inertia-fixed**: `G₀` permutes the
orbit `{σ•b}`, hence fixes the symmetric functions (Mathlib's `smul_coeff_charpoly`). -/
theorem coeff_inertiaCharpoly_mem
    [Fintype ↥(ramificationGroup K (extensionIntegers K L) 0)]
    (b : ↥(extensionIntegers K L)) (n : ℕ) :
    (MulSemiringAction.charpoly ↥(ramificationGroup K (extensionIntegers K L) 0) b).coeff n
      ∈ inertiaFixedIntegers K L :=
  fun σ => MulSemiringAction.smul_coeff_charpoly b n σ

/-- **The residue of the inertia orbit polynomial is `(X − b̄)^{|G₀|}`**: inertia elements fix
residues (Pass 24), so every orbit factor collapses to `X − b̄`. -/
theorem map_residue_inertiaCharpoly
    [Fintype ↥(ramificationGroup K (extensionIntegers K L) 0)]
    (b : ↥(extensionIntegers K L)) :
    (MulSemiringAction.charpoly ↥(ramificationGroup K (extensionIntegers K L) 0) b).map
        (residue ↥(extensionIntegers K L))
      = (X - C (residue ↥(extensionIntegers K L) b))
          ^ (Fintype.card ↥(ramificationGroup K (extensionIntegers K L) 0)) := by
  rw [MulSemiringAction.charpoly, Polynomial.map_prod]
  have h1 : ∀ σ : ↥(ramificationGroup K (extensionIntegers K L) 0),
      ((X - C (σ • b)).map (residue ↥(extensionIntegers K L)))
        = X - C (residue ↥(extensionIntegers K L) b) := by
    intro σ
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    exact congrArg C (residue_smul_eq_of_mem_ramificationGroup_zero K σ.2 b)
  calc (∏ σ : ↥(ramificationGroup K (extensionIntegers K L) 0),
        ((X - C (σ • b)).map (residue ↥(extensionIntegers K L))))
      = ∏ _σ : ↥(ramificationGroup K (extensionIntegers K L) 0),
          (X - C (residue ↥(extensionIntegers K L) b)) :=
        Finset.prod_congr rfl (fun σ _ => h1 σ)
    _ = (X - C (residue ↥(extensionIntegers K L) b))
          ^ (Fintype.card ↥(ramificationGroup K (extensionIntegers K L) 0)) := by
        rw [Finset.prod_const, Finset.card_univ]

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms coeff_inertiaCharpoly_mem
#print axioms map_residue_inertiaCharpoly

end Anabelian
