/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import ClassFieldTheory.Theorems.LocalClassFieldTheory.All
import Anabelian.ClassField.UnitFiltration
import Anabelian.Herbrand.UpperNumbering
import Anabelian.Extension.Integers

/-!
# Statement ledger — `L34`: the ramification correspondence `θ(Uⁿ) = Gⁿ` (Pass 99)

This file is the first entry of the project's **statement ledger** (`Anabelian/Statements/`):
a `Prop`-valued `def`, with no theorem and no proof, whose only job is to be *the* statement
of a target theorem, audited for correctness **before** any proof is attempted. The mechanism
exists because a formal statement can elaborate, compile, and still be the wrong theorem — the
cautionary exhibit is the Bogomolov–Pop formalization in `openai/math`, which states the
reconstruction result as *uniqueness only* (an isomorphism, if one exists, is unique up to the
expected ambiguity), omitting the existence half that carries the anabelian content. The
`#print axioms` discipline cannot catch that: the statement is the hole. So each statement here
records its sources, every convention choice, and the reason it is the right statement;
`scripts/preflight.sh` checks that every file in this directory elaborates on its own.

## The mathematics

Serre, *Local Fields* (GTM 67), XV §2, Theorem 1 and Corollary 3; equivalently Neukirch,
*Algebraic Number Theory*, V (6.2) / Cassels–Fröhlich VI §4. For `L/K` a finite abelian
extension of nonarchimedean local fields with local reciprocity (Artin) map
`θ_{L/K} : Kˣ → Gal(L/K)` (surjective, kernel `N_{L/K} Lˣ`), and `Uⁿ_K` the higher unit groups
(`U⁰ = 𝒪_Kˣ`, `Uⁿ = 1 + 𝔪_K^n`):

  **`θ_{L/K}(Uⁿ_K) = Gⁿ(L/K)` for every `n ≥ 0`**, with `Gⁿ` the upper-numbering filtration.

This is the statement that makes the **unit filtration of `K` — hence `v_K`, hence (with the
Pass-24/27 characters) the residue field and ultimately the field — visible inside
`Gal(K^ab/K)` through its upper filtration**; it is the R1-relevant piece of local class field
theory (ROADMAP L3.4), because R1 needs the Galois group to *determine* the local field's
arithmetic invariants, and `Gⁿ` is Galois-theoretic while `Uⁿ` is field-theoretic.

## The formal statement, and every convention choice

* **Finite level only.** The statement quantifies over ClassFieldTheory's
  `FiniteAbelianLocalExtension K` (finite abelian `E ⊆ K^sep`, Mathlib's `SeparableClosure`),
  not over `K^ab`: upstream's profinite reciprocity `profiniteLocalReciprocity` is a
  `Nonempty` of some isomorphism, **not** the canonical map, and is deliberately not used. The
  `K^ab`-level statement `θ(Uⁿ) = Gⁿ(K^ab/K)` is the inverse limit of these over `E`
  (Pass 83's `G^v(K^sep/K)` as a closed inverse limit; L3.0's `K^ab`), to be stated later.
* **Which Artin map.** `artin` ranges over families satisfying `IsNormalizedArtinFamily K`:
  the three clauses of upstream's `finiteAbelianLocalReciprocity_family_arithmeticFrobenius`
  (surjective with kernel the norm subgroup; coherent under inclusion `E ≤ F`; and on
  unramified `E` the **inverse** of a uniformizer maps to the arithmetic `q`-Frobenius). By
  upstream's `finiteAbelianLocalReciprocity_family_ext` such a family is **unique**
  (`isNormalizedArtinFamily_unique`), and it exists (`exists_isNormalizedArtinFamily`); so
  "for every normalized family" is "for the canonical family", with no choice hidden in the
  statement. The normalization matters: a surjection with the right kernel is only determined
  up to `Aut(Gal(E/K))`, which need not preserve `Gⁿ`.
* **Frobenius orientation.** Upstream normalizes `π⁻¹ ↦ Frob_arith` (so `π ↦ Frob_arith⁻¹`,
  the geometric-Frobenius convention of Deligne), whereas Serre normalizes `π ↦ Frob_arith`.
  The two Artin maps differ by inversion on `Kˣ`; since `Uⁿ` is a subgroup, `θ(Uⁿ)` is the
  same subgroup under either convention. **The statement is convention-independent here.**
* **`Uⁿ`.** `unitFiltration K n : Subgroup Kˣ` (Pass 99): `U⁰ = 𝒪_Kˣ`, `Uⁿ = 1 + 𝔪^n`
  (Serre IV §2). Its image is `Subgroup.map` along the underlying monoid hom of the
  continuous hom `artin E : Kˣ →ₜ* (E ≃ₐ[K] E)`.
* **`Gⁿ(E/K)`.** The project's `upperRamificationGroup K (extensionIntegers K E) (n : ℝ)` —
  `G^v = G_{⌈ψ(v)⌉₊}` at the project's canonical valuation ring `𝒪_E = extensionIntegers K E`
  (Pass 45; identified with ClassFieldTheory's `upperRamificationGroup` for `-1 < t` in
  Pass 99's `UpperBridge`, so for every `n : ℕ` in particular). It is a subgroup of the
  decomposition subgroup `D(𝒪_E) ≤ E ≃ₐ[K] E`, pushed forward along `Subgroup.subtype` to
  compare with the image of `Uⁿ`; `D(𝒪_E) = ⊤` (Pass 52), so nothing is lost. The project's
  `G_{-1} = G_0` truncation is invisible at `n ≥ 0`.
* **Index `n : ℕ`.** Serre states the correspondence for integer `n ≥ 0`; by Hasse–Arf
  (imported, Pass 98) the upper jumps of an abelian extension are integers, so the integer
  statement determines the real-indexed one (`G^v = G^{⌈v⌉}` for `v > -1`). Not stated here.
* **Universe.** `K : Type` (universe `0`), because upstream's family theorems are stated at
  `Type`; `E.1 : Type` follows.

## What this file does **not** do

It proves nothing about `L34`; `L34` is a `def`, not a `theorem`, and no `sorry` exists. The
two theorems present (`exists_isNormalizedArtinFamily`, `isNormalizedArtinFamily_unique`) only
certify that the predicate the statement quantifies over is upstream's, inhabited and unique.
Standard axioms only; ledger `0 FOUNDATIONAL / 0 DEBT`.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel ClassFieldTheory

/-- **The Frobenius-normalized coherent family of finite local Artin maps** — upstream's
`finiteAbelianLocalReciprocity_family_arithmeticFrobenius` conclusion as a predicate on the
family: (i) each `artin E : Kˣ →ₜ* Gal(E/K)` is surjective with kernel the norm subgroup
`N_{E/K} Eˣ`; (ii) the maps are coherent under inclusions `E ≤ F`; (iii) for unramified `E`,
a uniformizer's **inverse** maps to the unique automorphism inducing the arithmetic
`q`-Frobenius on residues. Unique by `isNormalizedArtinFamily_unique`. -/
def IsNormalizedArtinFamily (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (artin : (E : FiniteAbelianLocalExtension K) → Kˣ →ₜ* (E.1 ≃ₐ[K] E.1)) : Prop :=
  (∀ E : FiniteAbelianLocalExtension K,
    Function.Surjective (artin E) ∧ (artin E).toMonoidHom.ker = E.normSubgroup) ∧
  (∀ (E F : FiniteAbelianLocalExtension K) (hEF : E.1 ≤ F.1) (x : Kˣ) (y : E.1),
    IntermediateField.inclusion hEF ((artin E x) y) =
      (artin F x) (IntermediateField.inclusion hEF y)) ∧
  ∀ (E : FiniteAbelianLocalExtension K)
    [ValuativeRel E.1] [UniformSpace E.1] [IsUniformAddGroup E.1]
    [IsNonarchimedeanLocalField E.1]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation E.1)],
    (𝓂[E.1] : Ideal 𝒪[E.1]).ramificationIdx 𝒪[K] = 1 →
    ∀ (π : 𝒪[K]) (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) (σ : E.1 ≃ₐ[K] E.1),
      (∀ x : 𝒪[E.1], ∃ z : 𝒪[E.1],
        (z : E.1) = σ (x : E.1) ∧
          IsLocalRing.residue 𝒪[E.1] z = (IsLocalRing.residue 𝒪[E.1] x) ^ Nat.card 𝓀[K]) ↔
        σ = artin E ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)

/-- The normalized family exists (upstream). -/
theorem exists_isNormalizedArtinFamily (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ artin : (E : FiniteAbelianLocalExtension K) → Kˣ →ₜ* (E.1 ≃ₐ[K] E.1),
      IsNormalizedArtinFamily K artin :=
  finiteAbelianLocalReciprocity_family_arithmeticFrobenius K

/-- The normalized family is unique (upstream's `finiteAbelianLocalReciprocity_family_ext`). -/
theorem isNormalizedArtinFamily_unique (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {f g : (E : FiniteAbelianLocalExtension K) → Kˣ →ₜ* (E.1 ≃ₐ[K] E.1)}
    (hf : IsNormalizedArtinFamily K f) (hg : IsNormalizedArtinFamily K g) : f = g :=
  finiteAbelianLocalReciprocity_family_ext K f g (fun E => (hf.1 E).2) (fun E => (hg.1 E).2)
    hf.2.1 hg.2.1
    (fun E _ _ _ _ _ hUnram π hπ x => (hf.2.2 E hUnram π hπ _).mpr rfl x)
    (fun E _ _ _ _ _ hUnram π hπ x => (hg.2.2 E hUnram π hπ _).mpr rfl x)

/-- **`L34` — the ramification correspondence `θ_{E/K}(Uⁿ_K) = Gⁿ(E/K)`** (Serre, *Local
Fields*, XV §2 Cor. 3), at finite level, for the Frobenius-normalized Artin family: for every
nonarchimedean local field `K`, every finite abelian `E ⊆ K^sep`, and every `n : ℕ`, the image
of the higher unit group `Uⁿ_K ≤ Kˣ` under `artin E` is the project's upper-numbering group
`Gⁿ(E/K) = G^n(𝒪_E)`, as subgroups of `Gal(E/K)`. See the module docstring for every
convention choice. A statement, not a theorem. -/
def L34 : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (artin : (E : FiniteAbelianLocalExtension K) → Kˣ →ₜ* (E.1 ≃ₐ[K] E.1)),
    IsNormalizedArtinFamily K artin →
    ∀ (E : FiniteAbelianLocalExtension K) (n : ℕ),
      (unitFiltration K n).map (artin E).toMonoidHom =
        (upperRamificationGroup K (extensionIntegers K E.1) (n : ℝ)).map
          ((extensionIntegers K E.1).decompositionSubgroup K).subtype

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms IsNormalizedArtinFamily
#print axioms exists_isNormalizedArtinFamily
#print axioms isNormalizedArtinFamily_unique
#print axioms L34

-- The imported ClassFieldTheory theorems this statement's predicate rests on (ledger: "External
-- dependencies"), re-audited so a bump of the dependency cannot silently introduce an axiom.
#print axioms ClassFieldTheory.finiteAbelianLocalReciprocity_family_arithmeticFrobenius
#print axioms ClassFieldTheory.finiteAbelianLocalReciprocity_family_ext

end Anabelian
