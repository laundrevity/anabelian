/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Absolute.UpperNumbering
import Mathlib

/-!
# Brick B5: projection surjectivity — the L2 capstone closes (Pass 83)

**The upper numbering on the absolute Galois group is an inverse limit of the finite
levels.** For a nonarchimedean local `K`, Galois `E/K` (in particular `E = K^sep`), every
finite Galois subextension `L`, and every `v : ℝ`:

> **`(absoluteUpperRamificationGroup K E v).map (restrictNormalHom L) = G^v(L/K)`**
> (`map_absoluteUpperRamificationGroup_eq`)

With Pass 82's definition, membership, and closedness, this completes the Pass-79 ladder
(B1–B5) and with it the **L2 stratum**: `G^v(K^sep/K)` exists, is closed in the Krull
topology, and projects onto `G^v(L/K)` at every finite level — the object through which
local class field theory's ramification correspondence (L3) and the anabelian program's
local reconstruction (R1) read the ramification data of `Gal(K̄/K)`.

The proof is compactness on a directed family of closed fibers: nonemptiness of each fiber
comes from **Herbrand's theorem along the transitions** (Pass 81 — lifting `τ` up the
finite tower `L ≤ L ⊔ M`) plus `restrictNormalHom_surjective` (lifting to `Gal(E/K)`);
directedness from the FGIF lattice and the downward step; compactness of `Gal(E/K)` from
Mathlib's `InfiniteGalois` stack. Herbrand's theorem is thus used exactly where Serre uses
it: it is what makes the finite levels a compatible system.

## Honesty

The capstone of chapter-IV ramification theory for a **given** local base — **no reach
toward R1–R3**; nothing is recovered from an abstract group. Hasse–Arf (Serre ch. V) is a
separate rung, NOT claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2
untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {E : Type*} [Field E] [Algebra K E]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Restriction through an intermediate level: `restrict_M = restrict_{N→M} ∘ restrict_N`
for `M ≤ N` — Mathlib's `restrictNormalHom_comp_apply` under the Pass-81 pair package
(plus the `M ⊆ N ⊆ E` tower, which is `rfl`-cheap). -/
theorem restrictNormalHom_comp_of_le {M N : FiniteGaloisIntermediateField K E}
    (h : M ≤ N) (σ : E ≃ₐ[K] E) :
    letI := leAlgebra M N h
    haveI := leAlgebra_isScalarTower M N h
    AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M.toIntermediateField σ
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥N) M.toIntermediateField
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) N.toIntermediateField σ) := by
  let := leAlgebra M N h
  have := leAlgebra_isScalarTower M N h
  have : IsScalarTower ↥M ↥N E := IsScalarTower.of_algebraMap_eq' rfl
  exact IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply
    ↥M.toIntermediateField ↥N.toIntermediateField σ

/-- The downward step: if `σ` restricts into `G^v(N/K)` then it restricts into `G^v(M/K)`
for every `M ≤ N` — composition coherence + Herbrand along the transitions (Pass 81). -/
theorem mem_fullUpper_of_le [Algebra.IsSeparable K E]
    {M N : FiniteGaloisIntermediateField K E} (h : M ≤ N) {v : ℝ}
    {σ : E ≃ₐ[K] E}
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := E) N.toIntermediateField σ
      ∈ fullUpperRamificationGroup K ↥N v) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M.toIntermediateField σ
      ∈ fullUpperRamificationGroup K ↥M v := by
  let := leAlgebra M N h
  have := leAlgebra_isScalarTower M N h
  rw [restrictNormalHom_comp_of_le K h σ]
  rw [← map_fullUpperRamificationGroup_le K M N h v]
  exact Subgroup.mem_map_of_mem _ hσ

/-- **PROJECTION SURJECTIVITY** (the L2-capstone theorem): for Galois `E/K` and every
finite Galois subextension `L`,

`(G^v(E/K)).map (restrictNormalHom L) = G^v(L/K)`

— the absolute upper filtration projects ONTO every finite level: the `⨅`-definition is a
genuine inverse limit of the finite-level `G^v`s. Proof: `≤` is Pass 82; for `≥`, given
`τ ∈ G^v(L/K)`, the fibers `F_M = restrict_M⁻¹(G^v(M/K)) ∩ restrict_L⁻¹{τ}` are closed
(finite discrete levels), NONEMPTY (lift `τ` into `G^v((L ⊔ M)/K)` by Herbrand-surjectivity
(Pass 81), then to `Gal(E/K)` by `restrictNormalHom_surjective`), and directed (FGIF sups
+ the downward step); `Gal(E/K)` is compact (Krull), so the intersection is nonempty, and
any point of it is the required lift. -/
theorem map_absoluteUpperRamificationGroup_eq [IsGalois K E]
    (L : FiniteGaloisIntermediateField K E) (v : ℝ) :
    (absoluteUpperRamificationGroup K E v).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField)
      = fullUpperRamificationGroup K ↥L v := by
  refine le_antisymm (map_absoluteUpperRamificationGroup_le K E L v) ?_
  intro τ hτ
  -- the directed family of closed fibers
  set F : FiniteGaloisIntermediateField K E → Set (E ≃ₐ[K] E) := fun M =>
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) M.toIntermediateField) ⁻¹'
      (fullUpperRamificationGroup K ↥M v : Set _)
    ∩ (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField) ⁻¹' {τ}
    with hF
  have hdown : ∀ {M M' : FiniteGaloisIntermediateField K E}, M ≤ M' → F M' ⊆ F M := by
    intro M M' h σ hσ
    exact ⟨mem_fullUpper_of_le K h hσ.1, hσ.2⟩
  have hne : ∀ M, (F M).Nonempty := by
    intro M
    -- lift τ into G^v((L ⊔ M)/K), then to Gal(E/K)
    let := leAlgebra L (L ⊔ M) le_sup_left
    have := leAlgebra_isScalarTower L (L ⊔ M) le_sup_left
    have h81 := map_fullUpperRamificationGroup_le K L (L ⊔ M) le_sup_left v
    rw [← h81] at hτ
    obtain ⟨τ', hτ'mem, hτ'⟩ := Subgroup.mem_map.mp hτ
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := (L ⊔ M).toIntermediateField) (E := E) τ'
    refine ⟨σ, ?_, ?_⟩
    · have h1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := E)
          M.toIntermediateField σ
          ∈ fullUpperRamificationGroup K ↥M v := by
        apply mem_fullUpper_of_le K (le_sup_right : M ≤ L ⊔ M)
        rw [hσ]
        exact hτ'mem
      exact h1
    · have h2 : AlgEquiv.restrictNormalHom (F := K) (K₁ := E)
          L.toIntermediateField σ = τ := by
        rw [restrictNormalHom_comp_of_le K (le_sup_left : L ≤ L ⊔ M) σ, hσ, hτ']
      exact h2
  have hclosed : ∀ M, IsClosed (F M) := by
    intro M
    apply IsClosed.inter
    · exact (isClosed_discrete _).preimage
        (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField)
    · exact (isClosed_discrete _).preimage
        (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)
  have hdir : Directed (· ⊇ ·) F := fun M₁ M₂ =>
    ⟨M₁ ⊔ M₂, hdown le_sup_left, hdown le_sup_right⟩
  have : Nonempty (FiniteGaloisIntermediateField K E) := ⟨⊥⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    F hdir hne (fun M => (hclosed M).isCompact) hclosed
  refine Subgroup.mem_map.mpr ⟨σ, ?_, ?_⟩
  · rw [mem_absoluteUpperRamificationGroup_iff]
    intro M
    exact (Set.mem_iInter.mp hσ M).1
  · exact (Set.mem_iInter.mp hσ L).2


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms restrictNormalHom_comp_of_le
#print axioms mem_fullUpper_of_le
#print axioms map_absoluteUpperRamificationGroup_eq

end Anabelian
