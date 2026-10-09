/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import ClassFieldTheory.Theorems.All
import Anabelian.LocalField.Canonical
import Anabelian.Herbrand.UpperNumbering
import Anabelian.Herbrand.Formula

/-!
# The ClassFieldTheory bridge: Hasse–Arf at `𝒪_L` (Pass 98)

The project now depends on `n-yamaguchi-0729/ClassFieldTheory` (commit `7713795`), an external
Lean 4 library proving local and global class field theory and the Hasse–Arf theorem with
standard axioms only (every imported headline is re-audited by `#print axioms` at the end of
this file; the ledger records the dependency). This file is the **bridge**: it instantiates
their results at the project's own structures, so that downstream passes consume Hasse–Arf
in project vocabulary (`ramificationGroup`, `herbrandPhi`, `extensionIntegers`) with no
`ValuativeRel L` instance in any statement — the D2 discipline of Passes 38–43 is kept.

* **`extensionIntegers_comap_algebraMap_eq`** — `𝒪_L ∩ K = 𝒪_K`: the base-field elements
  integral over `𝒪[K]` are exactly `𝒪[K]` (a valuation ring is integrally closed in its
  fraction field, `Valuation.Integers.mem_of_integral`).
* **`hasExtension_extensionValuativeRel`** — hence Mathlib's `Valuation.HasExtension
  (valuation K) (valuation L)` holds for the rung-1 valuative relation on `L`
  (`Valuation.HasExtension.ofComapInteger` over Pass 43's `integer_extensionValuativeRel_eq`).
* **`valuationSubring_extensionValuativeRel_eq`** — the canonical valuation subring of `L`
  under `extensionValuativeRel K L` is `extensionIntegers K L`.
* **`hasseArf_extension`** — `ClassFieldTheory.hasseArf` at the project's structures:
  `L/K` finite abelian, `K` a nonarchimedean local field, *no* hypothesis on `L` beyond
  `[Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]`; the local-field structure
  on `L` is Pass 41's `isNonarchimedeanLocalField_extension`, discharged inside the proof.
* **`hasseArf_herbrandPhi`** — the same theorem in project vocabulary: if
  `G_n ≠ G_{n+1}` (the project's `ramificationGroup`), then `φ_{L/K}(n) ∈ ℤ` for the project's
  `herbrandPhi`.

## The Herbrand identification (deliverable 2)

ClassFieldTheory's `lowerRamificationGroup K A n` has carrier
`{σ | ∀ x : A, σ • x - x ∈ 𝔪_A^(n+1)}`; the project's `ramificationGroup K A n` is
`(𝔪_A^(n+1)).inertia (A.decompositionSubgroup K)`, whose carrier is the same set. The two are
equal by `Subgroup.ext` + `Iff.rfl` (`lowerRamificationGroup_eq_ramificationGroup`). Their
`herbrandFunctionAtLowerIndex K A n : ℚ` is `(∑_{i ∈ Icc 1 n} |G_i|) / |G_0|`; the project's
`herbrandPhi K A n` is Serre's integral `∫₀ⁿ dt/(G_0 : G_t)`, which Pass 48's
`herbrandPhi_natCast` evaluates to `(∑_{i < n} |G_{i+1}|) / |G_0|`; reindexing `range n` to
`Icc 1 n` identifies them (`herbrandPhi_natCast_eq`). Their real `herbrandFunction` is
piecewise linear from those values with slope `|G_{m+1}|/|G_0|` on `[m, m+1]` and the identity
on `s < 0`; Pass 48's `herbrandPhi_eq_affine_formula` and Pass 44's `herbrandPhi_eq_id` give
the same, so **the real Herbrand functions are equal as functions**
(`herbrandPhi_eq_herbrandFunction`). Consequently their `inverseHerbrandFunction K L` —
`Function.invFun` of their `herbrandFunction` at the canonical valuation subring — is the
project's `herbrandPsi` (`herbrandPsi_eq_invFun_herbrandFunction`).

**Where the two differ (recorded, not forced):** their `realLowerRamificationGroup K A s`
has carrier `{σ | ∀ x, σ • x - x ∈ 𝔪_A^(⌈s+1⌉.toNat)}` — Serre's `G_u = G_{⌈u⌉}` with
`G_{-1} = ⊤` on `s ≤ -1`; the project's `upperRamificationGroup K A v = G_{⌈ψ v⌉₊}` is
ℕ-truncated, so `G^v = G_0` for `v ≤ -1` where theirs is `⊤`. For `-1 < s` they agree
(`realLowerRamificationGroup_eq`), hence their `upperRamificationGroup K L t` equals the
project's `upperRamificationGroup K 𝒪_L t` for `-1 < t`, modulo transporting along
`valuationSubring_extensionValuativeRel_eq` (the two live over different-but-equal valuation
subrings; the transport is not performed here — a next-pass item, as is the comparison of
their `IsUpperRamificationJump`/`isUpperRamificationJump_int` with the project's `G^v`).

## Honesty

Hasse–Arf is **imported**, not proved: the project's contribution is the instantiation and the
identification. The dependency is a `FOUNDATIONAL`-style boundary recorded in
`AXIOM_LEDGER.md`'s "External dependencies" section — not as a ledger axiom (the import carries
no axioms: every imported headline is standard-only, re-checked below), but as an honest
statement of what the project now takes from outside. No new `structure`/`class`; no owed
witness (no load-bearing-hypothesis claim is made: the abelian hypothesis is theirs, and its
necessity — Hasse–Arf fails for non-abelian extensions — is not claimed here as a theorem).
D2 respected: `extensionValuativeRel` and its topology appear in no statement except the two
`letI`-stated bricks. Recovers nothing from an abstract group; R1–R3 untouched.

## Axiom status

Standard axioms only on every declaration, project and imported (`#print axioms` below).
Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **`𝒪_L ∩ K = 𝒪_K`**: an element of the base field is integral over `𝒪[K]` iff it lies in
`𝒪[K]` — `𝒪[K]` is integrally closed in `K` (`Valuation.Integers.mem_of_integral`), and
integrality of `algebraMap K L x` over `𝒪[K]` descends to `x` along `K ↪ L`
(`isIntegral_algebraMap_iff`). -/
theorem extensionIntegers_comap_algebraMap_eq :
    (extensionIntegers K L).toSubring.comap (algebraMap K L) = (𝒪[K] : Subring K) := by
  ext x
  rw [Subring.mem_comap]
  change IsIntegral ↥𝒪[K] (algebraMap K L x) ↔ _
  rw [isIntegral_algebraMap_iff]
  constructor
  · intro hx
    exact (Valuation.mem_integer_iff _ _).mpr
      ((Valuation.integer.integers (valuation K)).mem_of_integral hx)
  · intro hx
    exact isIntegral_algebraMap (x := (⟨x, hx⟩ : ↥𝒪[K]))

/-- **The canonical valuation of `L` extends that of `K`** (Mathlib's `Valuation.HasExtension`)
under the project's rung-1 valuative structure on `L`: by `ofComapInteger`, from Pass 43's
`𝒪[L] = 𝒪_L` and `𝒪_L ∩ K = 𝒪_K`. -/
theorem hasExtension_extensionValuativeRel :
    letI := extensionValuativeRel K L
    Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L) := by
  let := extensionValuativeRel K L
  refine Valuation.HasExtension.ofComapInteger ?_
  rw [show (ValuativeRel.valuation L).integer = (extensionIntegers K L).toSubring from
    integer_extensionValuativeRel_eq K L]
  exact extensionIntegers_comap_algebraMap_eq K L

/-- The canonical valuation subring of `L` (rung-1 structure) is `𝒪_L = extensionIntegers K L`
— Pass 43's `integer_extensionValuativeRel_eq` read at the `ValuationSubring` level. -/
theorem valuationSubring_extensionValuativeRel_eq :
    letI := extensionValuativeRel K L
    (ValuativeRel.valuation L).valuationSubring = extensionIntegers K L := by
  let := extensionValuativeRel K L
  have h := integer_extensionValuativeRel_eq K L
  ext x
  change x ∈ (ValuativeRel.valuation L).integer ↔ _
  rw [h]
  rfl

/-- **Hasse–Arf at the project's structures** (`ClassFieldTheory.hasseArf`, instantiated): for
`L/K` finite abelian over a nonarchimedean local field `K`, every lower ramification jump `n`
of `𝒪_L` has integral Herbrand value `φ(n) ∈ ℤ`. The hypotheses are the project's: nothing is
assumed on `L` — its local-field structure (`extensionValuativeRel`, the valuative topology,
Pass 41's `isNonarchimedeanLocalField_extension`) and the `HasExtension` compatibility are
discharged inside the proof via `letI`. Stated in ClassFieldTheory's vocabulary at
`extensionIntegers K L`; see `hasseArf_herbrandPhi` for the project-vocabulary form. -/
theorem hasseArf_extension [IsAbelianGalois K L] {n : ℕ}
    (hn : ClassFieldTheory.IsLowerRamificationJump K (extensionIntegers K L) n) :
    ∃ z : ℤ,
      ClassFieldTheory.herbrandFunctionAtLowerIndex K (extensionIntegers K L) n = (z : ℚ) := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hA := valuationSubring_extensionValuativeRel_eq K L
  rw [← hA] at hn ⊢
  exact ClassFieldTheory.hasseArf K L hn

section Identification

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]

variable {L} (A : ValuationSubring L)

/-- ClassFieldTheory's lower ramification group **is** the project's: the carriers are the same
set `{σ | ∀ x : A, σ • x - x ∈ 𝔪_A^(i+1)}` (`AddSubgroup.mem_inertia` is `Iff.rfl`). -/
theorem lowerRamificationGroup_eq_ramificationGroup (i : ℕ) :
    ClassFieldTheory.lowerRamificationGroup K A i = ramificationGroup K A i := by
  ext σ
  exact Iff.rfl

/-- **The Herbrand values at integers agree**: the project's `φ(n) = ∫₀ⁿ dt/(G_0:G_t)` equals
ClassFieldTheory's `(∑_{i ∈ Icc 1 n} |G_i|) / |G_0|` (Pass 48's integer-point formula, with
`range n` reindexed to `Icc 1 n`). -/
theorem herbrandPhi_natCast_eq [Finite (A.decompositionSubgroup K)] (n : ℕ) :
    herbrandPhi K A (n : ℝ) = (ClassFieldTheory.herbrandFunctionAtLowerIndex K A n : ℝ) := by
  rw [herbrandPhi_natCast, ClassFieldTheory.herbrandFunctionAtLowerIndex]
  push_cast
  simp only [ramificationOrders, lowerRamificationGroup_eq_ramificationGroup]
  congr 1
  rw [Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun i => (Nat.card (ramificationGroup K A i) : ℝ)) 0 n 1]
  rfl

/-- **The real Herbrand functions agree**: the project's `herbrandPhi` (Serre's integral
`∫₀ᵘ dt/(G_0:G_t)`) and ClassFieldTheory's piecewise-linear `herbrandFunction` are the same
function `ℝ → ℝ` — affine with slope `|G_{m+1}|/|G_0|` on `[m, m+1]` (Pass 48), the identity on
`u ≤ 0` (Pass 44). -/
theorem herbrandPhi_eq_herbrandFunction [Finite (A.decompositionSubgroup K)] :
    herbrandPhi K A = ClassFieldTheory.herbrandFunction K A := by
  funext s
  unfold ClassFieldTheory.herbrandFunction
  split_ifs with hs
  · dsimp only
    rw [← herbrandPhi_natCast_eq,
      herbrandPhi_eq_affine_formula K A (n := ⌊s⌋₊)
        ⟨Nat.floor_le hs, (Nat.lt_floor_add_one s).le⟩,
      herbrandPhi_natCast]
    simp only [ramificationOrders, lowerRamificationGroup_eq_ramificationGroup]
    rw [add_div, mul_div_assoc]
  · exact herbrandPhi_eq_id K A (not_le.mp hs).le

/-- **The inverse Herbrand functions agree**: the project's `herbrandPsi` is `Function.invFun`
of ClassFieldTheory's `herbrandFunction` — which is literally the body of their
`inverseHerbrandFunction K L` at the canonical valuation subring. -/
theorem herbrandPsi_eq_invFun_herbrandFunction [Finite (A.decompositionSubgroup K)] :
    herbrandPsi K A = Function.invFun (ClassFieldTheory.herbrandFunction K A) := by
  rw [← herbrandPhi_eq_herbrandFunction]
  rfl

/-- **The real-indexed lower groups agree for `-1 < s`**: ClassFieldTheory's
`realLowerRamificationGroup K A s` (carrier `σ • x - x ∈ 𝔪_A^(⌈s+1⌉.toNat)`, Serre's
`G_u = G_{⌈u⌉}` with `G_{-1} = ⊤`) is the project's `G_{⌈s⌉₊}`. The two differ exactly on
`s ≤ -1`, where theirs is `⊤` and the ℕ-indexed project filtration bottoms out at `G_0`. -/
theorem realLowerRamificationGroup_eq {s : ℝ} (hs : -1 < s) :
    ClassFieldTheory.realLowerRamificationGroup K A s = ramificationGroup K A ⌈s⌉₊ := by
  have hceil : (⌈s + 1⌉).toNat = ⌈s⌉₊ + 1 := by
    have h0 : (-1 : ℤ) < ⌈s⌉ := Int.lt_ceil.mpr (by exact_mod_cast hs)
    rw [Int.ceil_add_one, ← Int.ceil_toNat]
    omega
  ext σ
  rw [mem_ramificationGroup_iff]
  change (∀ x : ↥A, σ • x - x ∈ IsLocalRing.maximalIdeal ↥A ^ (⌈s + 1⌉).toNat) ↔ _
  rw [hceil]

end Identification

/-- **Hasse–Arf in project vocabulary**: for `L/K` finite abelian over a nonarchimedean local
field, if `G_n ≠ G_{n+1}` in the project's lower-numbering filtration at `𝒪_L`, then the
project's Herbrand function takes an integer value at `n`. -/
theorem hasseArf_herbrandPhi [IsAbelianGalois K L] {n : ℕ}
    (hn : ramificationGroup K (extensionIntegers K L) n
      ≠ ramificationGroup K (extensionIntegers K L) (n + 1)) :
    ∃ z : ℤ, herbrandPhi K (extensionIntegers K L) (n : ℝ) = (z : ℝ) := by
  have hn' : ClassFieldTheory.IsLowerRamificationJump K (extensionIntegers K L) n := by
    unfold ClassFieldTheory.IsLowerRamificationJump
    rwa [lowerRamificationGroup_eq_ramificationGroup, lowerRamificationGroup_eq_ramificationGroup]
  obtain ⟨z, hz⟩ := hasseArf_extension K L hn'
  refine ⟨z, ?_⟩
  rw [herbrandPhi_natCast_eq, hz]
  exact Rat.cast_intCast z

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms extensionIntegers_comap_algebraMap_eq
#print axioms hasExtension_extensionValuativeRel
#print axioms valuationSubring_extensionValuativeRel_eq
#print axioms hasseArf_extension
#print axioms lowerRamificationGroup_eq_ramificationGroup
#print axioms herbrandPhi_natCast_eq
#print axioms herbrandPhi_eq_herbrandFunction
#print axioms herbrandPsi_eq_invFun_herbrandFunction
#print axioms realLowerRamificationGroup_eq
#print axioms hasseArf_herbrandPhi

-- The imported ClassFieldTheory headlines the project now relies on (ledger: "External
-- dependencies"). Re-audited here so a future bump of the dependency cannot silently
-- introduce an axiom. All standard-only at commit `7713795`.
#print axioms ClassFieldTheory.hasseArf
#print axioms ClassFieldTheory.isUpperRamificationJump_int
#print axioms ClassFieldTheory.finiteAbelianLocalReciprocity
#print axioms ClassFieldTheory.finiteAbelianLocalExistence
#print axioms ClassFieldTheory.profiniteLocalReciprocity
#print axioms ClassFieldTheory.finiteAbelianGlobalReciprocity
#print axioms ClassFieldTheory.topologicalGlobalReciprocity
#print axioms ClassFieldTheory.kroneckerWeber

end Anabelian
