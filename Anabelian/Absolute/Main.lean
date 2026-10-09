/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.Absolute.Surjectivity
import Mathlib

/-!
# The Absolute package: `G^v` on the absolute Galois group, consolidated (Pass 84)

One-stop summary and audit for the L2 capstone (Passes 79–83), plus its first structural
dividends. **The stratum's product**: for a nonarchimedean local `K` and any Galois `E/K`
(in particular `E = K^sep`), the upper ramification filtration

> `absoluteUpperRamificationGroup K E v ≤ Gal(E/K)`

which is (each with the pass that proved it):

* **defined** as the preimage-intersection over all finite Galois subextensions (B3,
  Pass 82), on Mathlib's `FiniteGaloisIntermediateField` presentation;
* **closed** in the Krull topology (Pass 82);
* an **inverse limit**: it projects ONTO the finite-level `G^v(L/K)` at every level
  (B5, Pass 83 — via Herbrand's theorem along the transitions, B1–B2/B4, Passes 80–81);
* **antitone** in `v`, **constant on `v ≤ 0`** (this pass);
* **separating**: `⨅_v G^v(E/K) = ⊥` (this pass — the finite levels are eventually `⊥`
  and every element of `E` lives in a finite Galois subextension).

Underneath sits the finite-tower theory consolidated in `Anabelian/Herbrand/Main.lean`
(Prop. 2 → Prop. 3 → Lemma 5 → Prop. 15 → Herbrand's theorem, Passes 46–78). Together:
Serre, *Local Fields*, chapter IV, from the definition of `G_i` to the ramification
filtration of the absolute Galois group — axiom-free.

## Honesty

Consolidation + four structural lemmas for a given base — **no reach toward R1–R3**;
nothing is recovered from an abstract group (that reconstruction — which of these
filtrations is group-theoretically detectable — is the R1 question, untouched). Hasse–Arf
is NOT claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

The audit block below covers the WHOLE Absolute stratum (B1–B5 + this pass) — all
standard-axioms-only. Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

open ValuationSubring IsLocalRing Set
open scoped Pointwise ValuativeRel
open ValuativeRel

namespace Anabelian


section FiniteLevel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The full-group upper filtration is antitone in `v` (Pass 45's decomposition-level
antitonicity, mapped). -/
theorem fullUpperRamificationGroup_antitone :
    Antitone (fullUpperRamificationGroup K L) := fun _ _ hvw =>
  Subgroup.map_mono (upperRamificationGroup_antitone K
    (extensionIntegers K L) hvw)

/-- For `v ≤ 0` the full-group upper filtration is constant (`ψ = id` there, `⌈·⌉₊ = 0`):
`G^v = G^0` — Serre's normalization. -/
theorem fullUpperRamificationGroup_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    fullUpperRamificationGroup K L v
      = fullUpperRamificationGroup K L 0 := by
  unfold fullUpperRamificationGroup upperRamificationGroup
  rw [herbrandPsi_eq_id K (extensionIntegers K L) hv,
      herbrandPsi_zero K (extensionIntegers K L),
      Nat.ceil_eq_zero.mpr hv, Nat.ceil_zero]

end FiniteLevel

section Absolute

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (E : Type*) [Field E] [Algebra K E]

/-- **The absolute upper filtration is antitone**: `v ≤ w ⟹ G^w(E/K) ≤ G^v(E/K)`. -/
theorem absoluteUpperRamificationGroup_antitone :
    Antitone (absoluteUpperRamificationGroup K E) := fun _ _ hvw =>
  iInf_mono fun L => Subgroup.comap_mono (fullUpperRamificationGroup_antitone K ↥L hvw)

/-- For `v ≤ 0` the absolute filtration is constant: `G^v(E/K) = G^0(E/K)`. -/
theorem absoluteUpperRamificationGroup_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    absoluteUpperRamificationGroup K E v
      = absoluteUpperRamificationGroup K E 0 := by
  unfold absoluteUpperRamificationGroup
  exact iInf_congr fun L => by rw [fullUpperRamificationGroup_of_nonpos K ↥L hv]

/-- **THE SEPARATION THEOREM**: the absolute upper filtration separates the Galois group —
`⨅_v G^v(E/K) = ⊥`. A `σ ≠ 1` moves some `x ∈ E`; the finite Galois subextension
`L = adjoin K {x}` sees it, the finite-level filtration is eventually `⊥` there (Pass 45,
under the Noetherian separation at `𝒪_L` — Pass 29), so `σ` leaves `G^v(E/K)` for `v`
large. The filtration is thus a genuine (separating, closed, antitone, exhaustive-at-`0`)
filtration of `Gal(K^sep/K)` — the ramification data the anabelian program reads. -/
theorem iInf_absoluteUpperRamificationGroup_eq_bot [IsGalois K E]
    [Algebra.IsSeparable K E] :
    (⨅ v : ℝ, absoluteUpperRamificationGroup K E v) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_iInf] at hσ
  rw [Subgroup.mem_bot]
  -- σ fixes every x : E, via the finite Galois subextension it generates
  ext x
  have hfin : Finite ({x} : Set E) := Set.finite_singleton x |>.to_subtype
  set L : FiniteGaloisIntermediateField K E :=
    FiniteGaloisIntermediateField.adjoin K ({x} : Set E) with hL
  -- the restriction of σ to L lies in every G^v(L/K), which is eventually ⊥
  have := isNoetherianRing_extensionIntegers K ↥L
  have hsep : (⨅ n : ℕ, IsLocalRing.maximalIdeal
      ↥(extensionIntegers K ↥L) ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
  obtain ⟨v, hv⟩ := upperRamificationGroup_eventually_bot K
    (extensionIntegers K ↥L) hsep
  have h1 : AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField σ
      ∈ fullUpperRamificationGroup K ↥L v :=
    (mem_absoluteUpperRamificationGroup_iff K E).mp (hσ v) L
  rw [fullUpperRamificationGroup, hv, Subgroup.map_bot,
      Subgroup.mem_bot] at h1
  -- now transfer triviality of the restriction to σ itself at x
  have hxL : x ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K _ (Set.mem_singleton x)
  have h2 := AlgEquiv.restrictNormal_commutes σ ↥L.toIntermediateField
    (⟨x, hxL⟩ : ↥L.toIntermediateField)
  rw [show AlgEquiv.restrictNormal σ ↥L.toIntermediateField
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := E) L.toIntermediateField σ
      from rfl, h1] at h2
  simpa using h2.symm

end Absolute


-- The one-stop audit of the Absolute stratum (re-runs on every `lake build`).
-- All standard-axioms-only: [propext, Classical.choice, Quot.sound].
#print axioms fullRamificationGroup                          -- B1 def   (Pass 80)
#print axioms fullUpperRamificationGroup                     -- B1 def   (Pass 80)
#print axioms map_fullUpperRamificationGroup_eq              -- B1 Herbrand (Pass 80)
#print axioms map_fullUpperRamificationGroup_le              -- B2/B4    (Pass 81)
#print axioms absoluteUpperRamificationGroup                 -- B3 def   (Pass 82)
#print axioms isClosed_absoluteUpperRamificationGroup        -- B3 closed (Pass 82)
#print axioms map_absoluteUpperRamificationGroup_eq          -- B5 limit (Pass 83)
#print axioms fullUpperRamificationGroup_antitone            -- (Pass 84)
#print axioms fullUpperRamificationGroup_of_nonpos           -- (Pass 84)
#print axioms absoluteUpperRamificationGroup_antitone        -- (Pass 84)
#print axioms absoluteUpperRamificationGroup_of_nonpos       -- (Pass 84)
#print axioms iInf_absoluteUpperRamificationGroup_eq_bot     -- separation (Pass 84)

end Anabelian
