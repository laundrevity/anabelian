/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.InertiaField
import Anabelian.Statements.L34

/-!
# `L34` at `n = 0`: the image of the units under the Artin map is the inertia group (Pass 100)

For `K` a nonarchimedean local field, `artin` the Frobenius-normalized Artin family
(`IsNormalizedArtinFamily K artin`, Pass 99), and `E ⊆ K^sep` finite abelian:

  **`θ_{E/K}(U⁰_K) = G⁰(E/K)`** — `L34_inertia`, exactly the `n = 0` instance of the ledgered
  statement `L34` (`L34Case_zero`), with `L34` recovered from the family of its instances
  (`L34_of_forall_L34Case`). Classical reading: `θ_{E/K}(𝒪_Kˣ)` **is the inertia subgroup**
  (`map_unitFiltration_zero_eq_inertiaSubgroup`, via Pass 45's `G^0 = G_0` and Pass 23's
  `G_0 = inertiaSubgroup`).

## Route (Serre, *Local Fields*, XV §2, the unramified half)

Write `G = Gal(E/K)`, `I = G_0(𝒪_E)` (`inertiaImage`), `E₀ = E^I` lifted into `K^sep`
(`inertiaFixedExtension`, a member of the family), `H = θ(U⁰)`.

* **`H ≤ I`** (`map_unitFiltration_zero_le_inertiaImage`). `E₀/K` is unramified
  (`ramificationIdx_eq_one_of_fieldRange_eq_fixedField`), so `U⁰ ≤ N_{E₀/K} E₀ˣ = ker θ_{E₀}`
  (`unitFiltration_zero_le_fieldNormSubgroup`); by the family's coherence under `E₀ ≤ E`,
  `θ_E(u)` restricts to `θ_{E₀}(u) = 1` on `E₀`, i.e. `θ_E(u) ∈ Gal(E/E₀) = I`
  (`IntermediateField.fixingSubgroup_fixedField`).
* **`|H| = |I|`** (`card_map_unitFiltration_zero`). `θ` is surjective with kernel `N = N_{E/K}Eˣ`,
  so `[G : H] = [Kˣ : U⁰·N]`; `U⁰ = ker v` and `v(N) = f·ℤ` (ClassFieldTheory's
  `valuationMap_comp_normUnits_range_eq_zmultiples_of_isSeparable`), so `[Kˣ : U⁰·N] = f`
  (`index_unitFiltration_zero_sup_fieldNormSubgroup`); and `|G| = |I|·f` (bridge). Hence
  `|H| = |I|`.
* **`H = I`** from `H ≤ I` and `|I| ≤ |H|` (`Subgroup.eq_of_le_of_card_ge`).

The `⊇` half is thus a *count*, not a second fixed-field argument: no "norm group ⊇ `U⁰` ⟹
unramified" brick is needed. Every ClassFieldTheory input is listed in the ledger's
"External dependencies"; the normalization clause (iii) of the family is **not** used here —
only surjectivity, the norm kernel and coherence (clauses (i)–(ii)) — so the `n = 0` case holds
for *any* coherent norm-kernel family, as it must (`U⁰` is a subgroup).

## Honesty

Finite level only; `n = 0` only — `L34` at `n ≥ 1` (the totally-ramified half, Hasse–Arf and
the norm-index computation `N(Uⁿ_L) = U^{ψ(n)}_K`) is open (ROADMAP L3.4). No `structure`/`class`;
no load-bearing-hypothesis claim is made (the family's clauses are upstream's), hence no owed
witness. Standard axioms only; ledger `0 FOUNDATIONAL / 0 DEBT`.
-/

namespace Anabelian

open scoped ValuativeRel
open ValuativeRel ClassFieldTheory

section Index

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

open LocalFieldTheory.IsNonarchimedeanLocalField in
/-- **`U⁰ · N_{L/K}Lˣ = v⁻¹(f ℤ)`** (as additive subgroups of `Additive Kˣ`): `U⁰ = ker v`,
and the normalized valuations of norms are exactly the multiples of the residue degree
`f = [𝓀_L : 𝓀_K]`. -/
theorem toAddSubgroup_unitFiltration_zero_sup_fieldNormSubgroup :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    Subgroup.toAddSubgroup (unitFiltration K 0 ⊔ fieldNormSubgroup K L) =
      AddSubgroup.comap (valuationMap K)
        (AddSubgroup.zmultiples (Module.finrank 𝓀[K] 𝓀[L] : ℤ)) := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
  have hrange :=
    LocalClassFieldTheory.valuationMap_comp_normUnits_range_eq_zmultiples_of_isSeparable K L
  have hU : ∀ u : Kˣ, u ∈ unitFiltration K 0 ↔ valuationMap K (Additive.ofMul u) = 0 := by
    intro u
    rw [unitFiltration_zero, ← integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero]
    exact Iff.rfl
  ext x
  rw [Additive.mem_toAddSubgroup, AddSubgroup.mem_comap, ← hrange, AddMonoidHom.mem_range,
    Subgroup.mem_sup]
  constructor
  · rintro ⟨u, hu, n, hn, rfl⟩
    change n ∈ (LocalFieldTheory.normUnits K L).range at hn
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hn
    refine ⟨Additive.ofMul y, ?_⟩
    change valuationMap K (Additive.ofMul (LocalFieldTheory.normUnits K L y)) =
      valuationMap K (Additive.ofMul (u * LocalFieldTheory.normUnits K L y))
    rw [valuationMap_ofMul_mul, (hU u).mp hu, zero_add]
  · rintro ⟨y, hy⟩
    change valuationMap K (Additive.ofMul (LocalFieldTheory.normUnits K L (Additive.toMul y))) =
      valuationMap K x at hy
    refine ⟨Additive.toMul x * (LocalFieldTheory.normUnits K L (Additive.toMul y))⁻¹, ?_,
      LocalFieldTheory.normUnits K L (Additive.toMul y), ⟨Additive.toMul y, rfl⟩,
      inv_mul_cancel_right _ _⟩
    rw [hU, valuationMap_ofMul_mul, valuationMap_ofMul_inv, hy]
    exact sub_self _

open LocalFieldTheory.IsNonarchimedeanLocalField in
/-- **`[Kˣ : U⁰ · N_{L/K}Lˣ] = f`**, the residue degree of `L/K`. -/
theorem index_unitFiltration_zero_sup_fieldNormSubgroup :
    letI := extensionValuativeRel K L
    letI := ValuativeRel.topologicalSpace L
    haveI := isNonarchimedeanLocalField_extension K L
    haveI := hasExtension_extensionValuativeRel K L
    (unitFiltration K 0 ⊔ fieldNormSubgroup K L).index = Module.finrank 𝓀[K] 𝓀[L] := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  rw [← Subgroup.index_toAddSubgroup, toAddSubgroup_unitFiltration_zero_sup_fieldNormSubgroup K L,
    AddSubgroup.index_comap_of_surjective _ (valuationMap_surjective K), Int.index_zmultiples,
    Int.natAbs_natCast]

/-- **`|θ(U⁰)| = |G_0(L/K)|` for any surjective `θ : Kˣ →* Gal(L/K)` with kernel the norms**:
`[Gal(L/K) : θ(U⁰)] = [Kˣ : U⁰·N] = f` (`index_unitFiltration_zero_sup_fieldNormSubgroup`) and
`|Gal(L/K)| = |G_0|·f` (`card_galoisGroup_eq_card_ramificationGroup_zero_mul`). Stated for an
abstract `L` so that it is instantiated once at the family member `E.1`. -/
theorem card_map_unitFiltration_zero_of_ker (θ : Kˣ →* (L ≃ₐ[K] L))
    (hsurj : Function.Surjective θ) (hker : θ.ker = fieldNormSubgroup K L) :
    Nat.card ((unitFiltration K 0).map θ) = Nat.card (inertiaImage K L) := by
  let := extensionValuativeRel K L
  let := ValuativeRel.topologicalSpace L
  have := isNonarchimedeanLocalField_extension K L
  have := hasExtension_extensionValuativeRel K L
  have hmap : (unitFiltration K 0 ⊔ θ.ker).map θ = (unitFiltration K 0).map θ := by
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq]
  have hidx : ((unitFiltration K 0).map θ).index = Module.finrank 𝓀[K] 𝓀[L] := by
    rw [← hmap, Subgroup.index_map_eq _ hsurj le_sup_right, hker]
    exact index_unitFiltration_zero_sup_fieldNormSubgroup K L
  have h1 := Subgroup.card_mul_index ((unitFiltration K 0).map θ)
  have h2 := card_galoisGroup_eq_card_ramificationGroup_zero_mul K L
  rw [hidx, h2, ← card_inertiaImage] at h1
  have : Module.Finite 𝓀[K] 𝓀[L] := Module.Finite.of_finite
  have hpos : 0 < Module.finrank 𝓀[K] 𝓀[L] := Module.finrank_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end Index

section Main

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (artin : (E : FiniteAbelianLocalExtension K) → Kˣ →ₜ* (E.1 ≃ₐ[K] E.1))
variable (E : FiniteAbelianLocalExtension K)

/-- **The inertia field of `E`, as a member of the family**: the fixed field `E^{G_0}` of the
inertia group, lifted from an intermediate field of `E` to an intermediate field of `K^sep`.
Finite and abelian over `K` as a subextension of `E`. -/
noncomputable def inertiaFixedExtension : FiniteAbelianLocalExtension K :=
  ⟨IntermediateField.lift (IntermediateField.fixedField (inertiaImage K E.1)),
    LinearEquiv.finiteDimensional
      (IntermediateField.liftAlgEquiv
        (IntermediateField.fixedField (inertiaImage K E.1))).toLinearEquiv,
    IsAbelianGalois.of_algHom (IntermediateField.inclusion
      (IntermediateField.lift_le (IntermediateField.fixedField (inertiaImage K E.1))))⟩

theorem inertiaFixedExtension_le : (inertiaFixedExtension K E).1 ≤ E.1 :=
  IntermediateField.lift_le _

variable {artin} (hartin : IsNormalizedArtinFamily K artin)
include hartin

/-- **`θ_{E/K}(U⁰) ≤ G_0(E/K)`**: the inertia field `E₀ = E^{G_0}` is unramified, so units are
norms from `E₀`, so `θ_{E₀}(u) = 1`; by coherence `θ_E(u)` fixes `E₀`, hence lies in
`Gal(E/E₀) = G_0`. -/
theorem map_unitFiltration_zero_le_inertiaImage :
    (unitFiltration K 0).map (artin E).toMonoidHom ≤ inertiaImage K E.1 := by
  set F := IntermediateField.fixedField (inertiaImage K E.1) with hF
  set E₀ : FiniteAbelianLocalExtension K := inertiaFixedExtension K E with hE₀
  have hle : E₀.1 ≤ E.1 := inertiaFixedExtension_le K E
  let : Algebra E₀.1 E.1 := (IntermediateField.inclusion hle).toAlgebra
  have : IsScalarTower K E₀.1 E.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hle).commutes x).symm
  have hrange : (IsScalarTower.toAlgHom K E₀.1 E.1).fieldRange = F := by
    ext x
    rw [AlgHom.mem_fieldRange]
    constructor
    · rintro ⟨y, rfl⟩
      exact (IntermediateField.mem_lift _).mp y.2
    · intro hx
      exact ⟨⟨x, (IntermediateField.mem_lift x).mpr hx⟩, Subtype.ext rfl⟩
  have hunr := ramificationIdx_eq_one_of_fieldRange_eq_fixedField K E.1 E₀.1 hrange
  have hnorm := unitFiltration_zero_le_fieldNormSubgroup K E₀.1 hunr
  rintro σ ⟨u, hu, rfl⟩
  have hker : artin E₀ u = 1 := by
    have hmem : u ∈ (artin E₀).toMonoidHom.ker := by
      rw [(hartin.1 E₀).2]; exact hnorm hu
    exact hmem
  rw [← IntermediateField.fixingSubgroup_fixedField (inertiaImage K E.1),
    IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : (x : SeparableClosure K) ∈ E₀.1 := (IntermediateField.mem_lift x).mpr hx
  have hcoh := hartin.2.1 E₀ E hle u ⟨x, hx'⟩
  rw [hker, AlgEquiv.one_apply] at hcoh
  have h1 : IntermediateField.inclusion hle ⟨x, hx'⟩ = x := Subtype.ext rfl
  rw [h1] at hcoh
  exact hcoh.symm

/-- **`|θ_{E/K}(U⁰)| = |G_0(E/K)|`**: the abstract count (`card_map_unitFiltration_zero_of_ker`)
at the family's map, whose kernel is `E.normSubgroup = N_{E/K}Eˣ` (clause (i)). -/
theorem card_map_unitFiltration_zero :
    Nat.card ((unitFiltration K 0).map (artin E).toMonoidHom) = Nat.card (inertiaImage K E.1) :=
  card_map_unitFiltration_zero_of_ker K E.1 (artin E).toMonoidHom (hartin.1 E).1 (hartin.1 E).2

/-- **`θ_{E/K}(U⁰) = G_0(E/K)`**: the `≤` and the cardinality equality. -/
theorem map_unitFiltration_zero_eq_inertiaImage :
    (unitFiltration K 0).map (artin E).toMonoidHom = inertiaImage K E.1 :=
  Subgroup.eq_of_le_of_card_ge (map_unitFiltration_zero_le_inertiaImage K E hartin)
    (card_map_unitFiltration_zero K E hartin).ge

/-- **`L34` at `n = 0`, verbatim**: the image of `U⁰_K = 𝒪_Kˣ` under the normalized Artin map
of `E` is the project's upper ramification group `G⁰(E/K)` pushed into `Gal(E/K)` — the
`n = 0` instance of the statement `L34` (Pass 99), with the index written `((0 : ℕ) : ℝ)` as
there. -/
theorem L34_inertia :
    (unitFiltration K 0).map (artin E).toMonoidHom =
      (upperRamificationGroup K (extensionIntegers K E.1) ((0 : ℕ) : ℝ)).map
        ((extensionIntegers K E.1).decompositionSubgroup K).subtype := by
  rw [Nat.cast_zero, upperRamificationGroup_zero]
  exact map_unitFiltration_zero_eq_inertiaImage K E hartin

/-- The same with the real index `0`. -/
theorem map_unitFiltration_zero_eq_upperRamificationGroup_zero :
    (unitFiltration K 0).map (artin E).toMonoidHom =
      (upperRamificationGroup K (extensionIntegers K E.1) 0).map
        ((extensionIntegers K E.1).decompositionSubgroup K).subtype := by
  rw [upperRamificationGroup_zero]
  exact map_unitFiltration_zero_eq_inertiaImage K E hartin

/-- **Classical reading: the image of `𝒪_Kˣ` under the Artin map is the inertia subgroup**
(Mathlib's `ValuationSubring.inertiaSubgroup` of `𝒪_E`, via Pass 23's `G_0 = inertiaSubgroup`). -/
theorem map_unitFiltration_zero_eq_inertiaSubgroup :
    (unitFiltration K 0).map (artin E).toMonoidHom =
      ((extensionIntegers K E.1).inertiaSubgroup K).map
        ((extensionIntegers K E.1).decompositionSubgroup K).subtype := by
  rw [← ramificationGroup_zero]
  exact map_unitFiltration_zero_eq_inertiaImage K E hartin

end Main

section Cases

/-- **The `n`-th instance of `L34`**: `θ_{E/K}(Uⁿ) = Gⁿ(E/K)` for this one `n`, quantified
exactly as `L34` is. `L34` is the conjunction over `n` (`L34_of_forall_L34Case`). -/
def L34Case (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (artin : (E : FiniteAbelianLocalExtension K) → Kˣ →ₜ* (E.1 ≃ₐ[K] E.1)),
    IsNormalizedArtinFamily K artin →
    ∀ E : FiniteAbelianLocalExtension K,
      (unitFiltration K n).map (artin E).toMonoidHom =
        (upperRamificationGroup K (extensionIntegers K E.1) (n : ℝ)).map
          ((extensionIntegers K E.1).decompositionSubgroup K).subtype

/-- `L34` follows from the family of its instances. -/
theorem L34_of_forall_L34Case (h : ∀ n, L34Case n) : L34 :=
  fun K _ _ _ _ artin hartin E n => h n K artin hartin E

/-- **The `n = 0` instance of `L34` holds.** -/
theorem L34Case_zero : L34Case 0 :=
  fun K _ _ _ _ _ hartin E => L34_inertia K E hartin

end Cases

-- Reproducible axiom audit (re-runs on every `lake build`). All standard-axioms-only.
#print axioms toAddSubgroup_unitFiltration_zero_sup_fieldNormSubgroup
#print axioms index_unitFiltration_zero_sup_fieldNormSubgroup
#print axioms card_map_unitFiltration_zero_of_ker
#print axioms inertiaFixedExtension
#print axioms map_unitFiltration_zero_le_inertiaImage
#print axioms card_map_unitFiltration_zero
#print axioms map_unitFiltration_zero_eq_inertiaImage
#print axioms L34_inertia
#print axioms map_unitFiltration_zero_eq_upperRamificationGroup_zero
#print axioms map_unitFiltration_zero_eq_inertiaSubgroup
#print axioms L34_of_forall_L34Case
#print axioms L34Case_zero

-- The imported ClassFieldTheory theorem consumed here (ledger: "External dependencies").
#print axioms LocalClassFieldTheory.valuationMap_comp_normUnits_range_eq_zmultiples_of_isSeparable

end Anabelian
