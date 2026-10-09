# HANDOFF.md — session bootstrap (written after Pass 100, 2026-10-08)

**State:** L2 is complete (Pass 83), consolidated with separation in Pass 84. L3: `K^ab`
(Pass 86); the Herbrand-quotient calculus and its generic layer (Passes 87–96, kept in the tree
as machinery); the Mathlib bump (Pass 97); **the ClassFieldTheory bridge (Pass 98)** — the
project depends on `n-yamaguchi-0729/ClassFieldTheory @ 7713795`, L3.1–L3.3 and Hasse–Arf are
**imported, not earned** (ledger "External dependencies"); **Pass 99** — the unit filtration
`Uⁿ`, the upper-group transport, and the statement ledger opening with `L34 : Prop`
(`θ(Uⁿ) = Gⁿ(E/K)` at finite level for the Frobenius-normalized Artin family). **Pass 100 proved
the `n = 0` case**: `ClassField/L34Inertia.lean`'s `L34_inertia` — the image of `U⁰ = 𝒪_Kˣ` under
the normalized Artin map of any finite abelian `E ⊆ K^sep` is `G⁰(E/K) = G_0 = ` inertia
(`L34Case_zero`; `L34_of_forall_L34Case : (∀ n, L34Case n) → L34`), on top of
`ClassField/InertiaBridge.lean` (upstream's inertia subgroup = the project's `G_0(𝒪_L)`;
`|G_0| = e`; `e·f = [L:K]`) and `ClassField/InertiaField.lean` (the fixed field of inertia is
unramified — via Pass 73's inertia-fixed residue cover, no `G_0 ↠ G_0` surjectivity; units are
norms from it). Ledger: **`0 FOUNDATIONAL / 0 DEBT`**; 104 project files; no open owed witnesses;
branch `master`. **The next task is Pass 101 (below).** L3.4 is IN-PROGRESS: `n = 0` proved,
general `n` open; the `K^ab`-level statement is still not ledgered (deferred twice).

Read `CLAUDE.md` (note the `Anabelian/Statements/` convention), the active table and the
**"External dependencies" section** of `AXIOM_LEDGER.md` (seven implementation-tree rows added
in Pass 100), the Pass-100 status header and the L3 ladder in `ROADMAP.md`, the
[Pass-100 entry](NOTES.md#pass-100) in `NOTES.md` (the upstream inventory table, the route, the
verbatim statements, the house idioms), the [Pass-99 entry](NOTES.md#pass-99) (the three statement
sets, the upper-group verdict, the statement-ledger rationale), and the
[Pass-98 entry](NOTES.md#pass-98) (the bridge and the identification table). Start with
`git status`; work on your own parley branch. `scripts/preflight.sh` enforces the pre-commit
checks, including the statement-ledger clauses 3b/5.

## What Pass 100 supplies

- `ClassField/InertiaBridge.lean` (package on `L` under statement-level `letI`/`haveI`;
  `[Algebra.IsSeparable K L]` or `[IsGalois K L]`): `inertia_eq_map_ramificationGroup_zero`
  (their `galoisGroupMaximalIdealInertiaOfIsIntegralClosure K L` = `(G_0(𝒪_L)).map subtype`),
  `card_ramificationGroup_zero_eq_ramificationIdx` (`|G_0(𝒪_L)| = 𝓂[L].ramificationIdx 𝒪[K]`),
  `ramificationIdx_mul_finrank_residueField` (`e · [𝓀_L:𝓀_K] = [L:K]`),
  `card_galoisGroup_eq_card_ramificationGroup_zero_mul` (`|Gal(L/K)| = |G_0|·f`).
- `ClassField/InertiaField.lean`: `inertiaImage K L : Subgroup (L ≃ₐ[K] L)` (`G_0(𝒪_L)` pushed
  into the Galois group) + `card_inertiaImage`; for `M` abstract with `[Algebra M L]
  [IsScalarTower K M L]`: `integersInclusion : 𝒪_M →+* 𝒪_L` (local),
  `residueField_map_integersInclusion_surjective`, `finrank_residueField_eq` (`f(M/K) = f(L/K)`),
  `finrank_eq_card_ramificationGroup_zero` (`[L:M] = |G_0|`),
  **`ramificationIdx_eq_one_of_fieldRange_eq_fixedField`** (`M ↦ L^{G_0}` ⟹ `e(M/K) = 1`),
  **`unitFiltration_zero_le_fieldNormSubgroup`** (`e(M/K) = 1` ⟹ `U⁰ ≤ N_{M/K}Mˣ`).
- `ClassField/L34Inertia.lean`: `toAddSubgroup_unitFiltration_zero_sup_fieldNormSubgroup`
  (`U⁰·N = v⁻¹(fℤ)`), `index_unitFiltration_zero_sup_fieldNormSubgroup` (`[Kˣ : U⁰·N] = f`),
  `card_map_unitFiltration_zero_of_ker` (abstract `θ`), `inertiaFixedExtension K E` (the lift of
  `E^{G_0}` as a family member) + `_le`, `map_unitFiltration_zero_le_inertiaImage` (`⊆`),
  `card_map_unitFiltration_zero`, `map_unitFiltration_zero_eq_inertiaImage`, **`L34_inertia`**,
  `map_unitFiltration_zero_eq_upperRamificationGroup_zero` (real index `0`),
  `map_unitFiltration_zero_eq_inertiaSubgroup` (classical), `L34Case n : Prop`,
  `L34_of_forall_L34Case`, `L34Case_zero`.

House idioms learned (P100): `open Foo in` goes *before the docstring*; **instantiate
package-`letI` lemmas at an abstract `L` with the hom/kernel as hypotheses, then once at `E.1`**
(instantiating at the subtype-coerced `E.1` inside a proof can exhaust the `isDefEq` budget);
`inferInstanceAs (IsLocalRing ↥A)` for `IsLocalRing ↥A.toSubring`; `(Subgroup.map_eq_bot_iff _).mpr`;
give `Module.Finite 𝓀[K] 𝓀[L] := Module.Finite.of_finite` before `Module.finrank_pos`. Earlier:
statement-level `haveI := isNonarchimedeanLocalField_extension K L` after the two `letI`s makes
upstream's `L`-instance constants usable in a statement; `rw [hA]` with
`hA : (valuation L).valuationSubring = extensionIntegers K L` moves goals to `𝒪_L`.

## Next task — Pass 101: `L34` at `n ≥ 1` (the ramified half), first rung `n = 1`

The `n = 0` case used only clauses (i)–(ii) of the family (surjective + norm kernel; coherence);
`n ≥ 1` is where the Frobenius normalization (iii), Hasse–Arf and the norm computations enter.

1. **Fix the route for `n ≥ 1`** (Serre XV §2 Thm 1 / Cor. 3). Serre: reduce to `E/K` totally
   ramified via `E₀` (Pass 100's `inertiaFixedExtension`, with `θ_E(Uⁿ) ≤ Gal(E/E₀) = G_0` already
   known), then on the totally ramified `E/E₀` use Hasse–Arf (`hasseArf_herbrandPhi`, Pass 98) and
   the norm-index computation `N_{E/E₀}(U^{ψ(n)}_E) ⊆ Uⁿ_{E₀}` with the unit layers
   `Uⁿ/Uⁿ⁺¹ ≃ 𝓀⁺` (Pass 99's `unitLayerQuotEquiv`) against the Pass-24/27 characters
   `G_i/G_{i+1} ↪ 𝓀⁺` (Serre V §3 Props 5–7 / XV §2 Prop. 4). Alternative: the conductor route —
   inventory upstream's `Theorems/ConductorsAndRayClassFields/IsAbelianConductor.*`
   (`AbelianConductorFiniteNormCriterion`, `…TameCriterion`, `…RealRamification`,
   `ExistsUniqueAbelianConductor`) and `Theorems/HasseArf/` to see whether "`θ(Uⁿ) ≤ Gⁿ`" or the
   conductor–discriminant relation is already there in some form. Record the inventory (names →
   role) in NOTES before proving.
2. **First ramified rung, `n = 1`**: `θ(U¹) = G¹ = G_1` (equivalently `θ` induces
   `U⁰/U¹ ≃ 𝓀ˣ ↠ G_0/G_1`, the tame quotient, compatibly with Pass 25's tame character). State it
   as `L34Case 1`.
3. **Ledger the `K^ab`-level statement** (deferred from Passes 99 and 100): a second
   `Anabelian/Statements/` entry — the inverse limit over `E` of `L34` against Pass 83's absolute
   `G^v` and L3.0's `K^ab`, quantifying over the finite-level family (never the `Nonempty`
   profinite object).
4. Optional: the real-indexed form `θ(Uⁿ) = G^v` for `v ∈ (n-1, n]` from Hasse–Arf
   (`upperRamificationGroup_extensionIntegers_jump_int`).

Standard axioms only; ledger stays 0/0; statement-preserving for existing results;
`Statements/L34.lean` is frozen (prove cases of it, never edit it); no
`sorry`/`axiom`/`native_decide`/heartbeat changes. Fresh files; `lake env lean` probes from the
project root; look upstream names up in `.lake/packages/ClassFieldTheory/Lean4/` (both
`ClassFieldTheory/Theorems/` and the implementation trees), never guess.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (Lean `v4.35.0-rc2`, Mathlib `0653561`, since
  Pass 97). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, statement-ledger checks
  (3b: imported/`def … : Prop`/no `axiom`; 5: standalone elaboration), warning-free build.
- **Slow rebuild:** `Anabelian/Quotient/LiftDvd.lean` can take approximately **15 minutes**
  to elaborate when rebuilt (P58). Preserve the cache; this delay alone is not a hang.
- **`scripts/refactor.sh`**: EXECUTED at Pass 64 (flat→folders, nine folders). Do not run
  it again; it is kept as the record of the mapping.

## House idioms (recent vintage; older in NOTES P25–41)

- Probes from the project root only (P60). `modByMonic_add_div (p q)` is hypothesis-free
  (P62). `congrArg Subtype.val` under polynomial `ext` (P58/P62). `rw [h]` stales
  pre-substitution `have`s (P59). `Irreducible.not_isUnit` (P59).
  `IsGalois.card_aut_eq_finrank` is Nat.card-valued (P61). Coercion forms must match
  syntactically; hand-rolled subtype equivs; plain-defeq structure fields (P57).
  `show`→`change` (P56). `𝒪[K]` is a `Subring` (P55). `ℕ∞` casts explicit; `Nat.card` API;
  narrow `variable` blocks; `push Not` (P50–54).
- DVR/`ℕ∞` toolkit: P51 cofinality, P53 bridge, P54 span-brick + binomial tail, P57
  DVR-on-`B`, P59 `addVal_neg`/`addVal_prod`/dilation.
- D2 lives entirely inside proofs; D2 at statement level only via anonymous `letI`/`haveI`
  (P98/P99). Upstream's reciprocity at `Type` only (P99).

## Retired (Pass 99) — kept for the record

Design rows P98–P102 of the Pass-95 unit-quotient program (local action / period / adic
transport / field norm; the small normal lattice; its unit subgroups and complete filtration;
regular layers and acyclicity; `q(𝒪ˣ) = 1` and `q(Lˣ) = [L:K]`). Their payoff — reciprocity —
is imported. The proved Passes 87–96 layer remains available. See ROADMAP L3.1.
