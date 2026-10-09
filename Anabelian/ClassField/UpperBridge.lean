/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.Bridge

/-!
# The upper-numbering bridge: `G^t` identified, upper jumps integral (Pass 99)

Pass 98 identified ClassFieldTheory's Herbrand theory with the project's at a common
valuation subring, and left two items open: transporting the **upper** groups across
`valuationSubring_extensionValuativeRel_eq` (the two developments index `G^t` by
different-but-equal valuation subrings of `L`), and comparing their jump notion
`IsUpperRamificationJump` with the project's. This file closes both.

## Results

* `upperRamificationGroup_of_nonpos` / `upperRamificationGroup_eq_iSup_of_neg` — for any
  `(K, A)`: the project's `G^v = G_0` for `v ≤ 0`, so the project's upper filtration has **no
  jump at any `t < 0`** (`G^t = ⨆_{s > t} G^s`).
* `inverseHerbrandFunction_eq` — their `ψ_{L/K}` is the project's `herbrandPsi` at the canonical
  valuation subring (both are `Function.invFun` of the same function, Pass 98).
* `upperRamificationGroup_eq_of_neg_one_lt` — **for `-1 < t`, their `G^t` IS the project's**
  `upperRamificationGroup K A t` at `A = (valuation L).valuationSubring`; and
  `upperRamificationGroup_extensionIntegers_eq_of_neg_one_lt` — the same at the project's
  `𝒪_L = extensionIntegers K L`, stated as an equality of subgroups of `L ≃ₐ[K] L` (both sides
  pushed forward along the decomposition-subgroup inclusion), which is the transport across
  `valuationSubring_extensionValuativeRel_eq`.
* `upperRamificationGroup_eq_top_of_le_neg_one` — **where they differ**: for `t ≤ -1` their
  `G^t = ⊤` (Serre's `G_{-1} = ⊤` convention, carried through `ψ(t) = t`), while the project's
  `G^t = G_0`. So the two filtrations agree exactly on `(-1, ∞)`, and differ on `(-∞, -1]` iff
  `G_0 ≠ ⊤` (i.e. iff `L/K` is not totally ramified) — recorded, not forced.
* `isUpperRamificationJump_iff` — for `-1 < t`, their `IsUpperRamificationJump K L t` is the
  project's `G^t ≠ ⨆_{s > t} G^s` at the canonical valuation subring.
* **`upperRamificationGroup_extensionIntegers_jump_int`** — Hasse–Arf in upper numbering, in
  project vocabulary with **no instance on `L` in the statement**: if the project's
  `G^t(𝒪_L) ≠ ⨆_{s>t} G^s(𝒪_L)` then `t ∈ ℤ`. For `t < 0` the hypothesis is contradictory
  (no jumps there); for `-1 < t` it transports to their jump and
  `ClassFieldTheory.isUpperRamificationJump_int` applies. Stated at universe `Type` because the
  imported theorem is (`K L : Type`).

## The jump convention, compared

ClassFieldTheory: a jump at `t` means `G^t ≠ ⨆_{s>t} G^s` (right limit). The project never
defined an upper-jump predicate; its lower jump is `G_n ≠ G_{n+1}` (`hasseArf_herbrandPhi`).
The natural upper analogue is the same right-limit condition, which this file uses verbatim —
so there is **no convention mismatch on `(-1, ∞)`**; the only difference is the endpoint `-1`,
where their filtration can jump (`⊤ ≠ G_0`) and the project's cannot. Their theorem's phrase
"including the possible endpoint `-1`" is exactly this.

## Honesty

Everything is standard-only and consumes `hasseArf`/`isUpperRamificationJump_int` from the
external dependency (ledger "External dependencies"); the integrality is **imported**, the
identification and the convention analysis are the project's. No `structure`/`class`; no owed
witness (no necessity claim: the abelian hypothesis is theirs). D2 respected: `L`-instances
occur only under statement-level `letI`/`haveI`, and the headline jump theorem has none.
Recovers nothing from an abstract group; R1–R3 untouched. Ledger `0 FOUNDATIONAL / 0 DEBT`.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel

section General

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
variable [Finite (A.decompositionSubgroup K)]

/-- For `v ≤ 0`, the project's `G^v = G_0` (`ψ(v) = v ≤ 0`, so `⌈ψ v⌉₊ = 0`). -/
theorem upperRamificationGroup_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    upperRamificationGroup K A v = ramificationGroup K A 0 := by
  unfold upperRamificationGroup
  rw [herbrandPsi_eq_id K A hv, Nat.ceil_eq_zero.mpr hv]

omit [Finite (A.decompositionSubgroup K)] in
theorem upperRamificationGroup_le_zero (v : ℝ) :
    upperRamificationGroup K A v ≤ ramificationGroup K A 0 :=
  ramificationGroup_antitone K A (Nat.zero_le _)

/-- **No jump at `t < 0`**: the project's upper filtration is constant (`= G_0`) on `(-∞, 0]`,
so it equals its own right limit there. -/
theorem upperRamificationGroup_eq_iSup_of_neg {t : ℝ} (ht : t < 0) :
    upperRamificationGroup K A t = ⨆ s : {s : ℝ // t < s}, upperRamificationGroup K A s := by
  apply le_antisymm
  · rw [upperRamificationGroup_of_nonpos K A ht.le]
    refine le_iSup_of_le ⟨t / 2, by linarith⟩ ?_
    rw [upperRamificationGroup_of_nonpos K A (by linarith)]
  · exact iSup_le fun s =>
      (upperRamificationGroup_le_zero K A s).trans (upperRamificationGroup_of_nonpos K A ht.le).ge

end General

section Transport

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- ClassFieldTheory's inverse Herbrand function is the project's `herbrandPsi` at the canonical
valuation subring of `L` (Pass 98's `herbrandPsi_eq_invFun_herbrandFunction`). -/
theorem inverseHerbrandFunction_eq (t : ℝ) :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    ClassFieldTheory.inverseHerbrandFunction K L t =
      herbrandPsi K (ValuativeRel.valuation L).valuationSubring t := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hA := valuationSubring_extensionValuativeRel_eq K L
  rw [hA, ClassFieldTheory.inverseHerbrandFunction, hA, herbrandPsi_eq_invFun_herbrandFunction]

/-- **For `-1 < t`, ClassFieldTheory's `G^t` is the project's**, at the canonical valuation
subring of `L`. -/
theorem upperRamificationGroup_eq_of_neg_one_lt {t : ℝ} (ht : -1 < t) :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    ClassFieldTheory.upperRamificationGroup K L t =
      upperRamificationGroup K (ValuativeRel.valuation L).valuationSubring t := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hA := valuationSubring_extensionValuativeRel_eq K L
  rw [ClassFieldTheory.upperRamificationGroup, inverseHerbrandFunction_eq K L t]
  unfold upperRamificationGroup
  rw [hA]
  refine realLowerRamificationGroup_eq K _ ?_
  have h1 : herbrandPsi K (extensionIntegers K L) (-1) = -1 :=
    herbrandPsi_eq_id K _ (by norm_num)
  rw [← h1]
  exact herbrandPsi_strictMono K _ ht

/-- **Where they differ**: for `t ≤ -1`, ClassFieldTheory's `G^t = ⊤` (Serre's `G_{-1} = ⊤`),
while the project's is `G_0` (`upperRamificationGroup_of_nonpos`). -/
theorem upperRamificationGroup_eq_top_of_le_neg_one {t : ℝ} (ht : t ≤ -1) :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    ClassFieldTheory.upperRamificationGroup K L t = ⊤ := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hA := valuationSubring_extensionValuativeRel_eq K L
  rw [ClassFieldTheory.upperRamificationGroup, inverseHerbrandFunction_eq K L t]
  rw [hA]
  rw [herbrandPsi_eq_id K _ (ht.trans (by norm_num))]
  exact ClassFieldTheory.realLowerRamificationGroup_eq_top_of_le_neg_one K _ ht

/-- **The transport across `valuationSubring_extensionValuativeRel_eq`**: for `-1 < t`,
ClassFieldTheory's `G^t` and the project's `G^t(𝒪_L)` are the same subgroup of `L ≃ₐ[K] L`. -/
theorem upperRamificationGroup_extensionIntegers_eq_of_neg_one_lt {t : ℝ} (ht : -1 < t) :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    (ClassFieldTheory.upperRamificationGroup K L t).map
        ((ValuativeRel.valuation L).valuationSubring.decompositionSubgroup K).subtype =
      (upperRamificationGroup K (extensionIntegers K L) t).map
        ((extensionIntegers K L).decompositionSubgroup K).subtype := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hA := valuationSubring_extensionValuativeRel_eq K L
  rw [upperRamificationGroup_eq_of_neg_one_lt K L ht, hA]

/-- For `-1 < t`, ClassFieldTheory's jump predicate is the project's right-limit jump
`G^t ≠ ⨆_{s>t} G^s` at the canonical valuation subring. -/
theorem isUpperRamificationJump_iff {t : ℝ} (ht : -1 < t) :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    ClassFieldTheory.IsUpperRamificationJump K L t ↔
      upperRamificationGroup K (ValuativeRel.valuation L).valuationSubring t ≠
        ⨆ s : {s : ℝ // t < s},
          upperRamificationGroup K (ValuativeRel.valuation L).valuationSubring s := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  rw [ClassFieldTheory.IsUpperRamificationJump, ClassFieldTheory.upperRamificationGroupAfter,
    upperRamificationGroup_eq_of_neg_one_lt K L ht,
    iSup_congr fun s : {s : ℝ // t < s} =>
      upperRamificationGroup_eq_of_neg_one_lt K L (ht.trans s.2)]

end Transport

section Integrality

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- **Upper ramification jumps are integers, in project vocabulary** (Hasse–Arf, upper form;
`ClassFieldTheory.isUpperRamificationJump_int` transported to `𝒪_L`): for `L/K` finite abelian
over a nonarchimedean local field, if the project's `G^t(𝒪_L)` differs from its right limit
`⨆_{s>t} G^s(𝒪_L)` then `t ∈ ℤ`. No instance on `L` appears in the statement. For `t ≤ -1`
the project's filtration cannot jump (`upperRamificationGroup_eq_iSup_of_neg`); for `-1 < t` the
jump is ClassFieldTheory's (`isUpperRamificationJump_iff`). Universe `Type`, as upstream. -/
theorem upperRamificationGroup_extensionIntegers_jump_int {t : ℝ}
    (ht : upperRamificationGroup K (extensionIntegers K L) t ≠
      ⨆ s : {s : ℝ // t < s}, upperRamificationGroup K (extensionIntegers K L) s) :
    ∃ z : ℤ, t = (z : ℝ) := by
  rcases le_or_gt t (-1) with hle | hlt
  · exact absurd (upperRamificationGroup_eq_iSup_of_neg K _ (by linarith)) ht
  · let := extensionValuativeRel K L
    let := ValuativeRel.topologicalSpace L
    have := isNonarchimedeanLocalField_extension K L
    have := hasExtension_extensionValuativeRel K L
    have hA := valuationSubring_extensionValuativeRel_eq K L
    refine ClassFieldTheory.isUpperRamificationJump_int K L
      ((isUpperRamificationJump_iff K L hlt).mpr ?_)
    rw [hA]
    exact ht

end Integrality

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms upperRamificationGroup_of_nonpos
#print axioms upperRamificationGroup_eq_iSup_of_neg
#print axioms inverseHerbrandFunction_eq
#print axioms upperRamificationGroup_eq_of_neg_one_lt
#print axioms upperRamificationGroup_eq_top_of_le_neg_one
#print axioms upperRamificationGroup_extensionIntegers_eq_of_neg_one_lt
#print axioms isUpperRamificationJump_iff
#print axioms upperRamificationGroup_extensionIntegers_jump_int

end Anabelian
