# HANDOFF.md — session bootstrap (written after Pass 99, 2026-10-08)

**State:** L2 is complete (Pass 83), consolidated with separation in Pass 84. L3: `K^ab`
(Pass 86); the Herbrand-quotient calculus and its generic layer (Passes 87–96, kept in the tree
as machinery); the Mathlib bump (Pass 97); **the ClassFieldTheory bridge (Pass 98)** — the
project depends on `n-yamaguchi-0729/ClassFieldTheory @ 7713795`, L3.1–L3.3 and Hasse–Arf are
**imported, not earned** (ledger "External dependencies"). **Pass 99** took the HANDOFF
decision — the in-project unit-quotient route to reciprocity (Pass-95 rows P98–P102) is
**retired**, only the unit filtration kept — and delivered: `ClassField/UnitFiltration.lean`
(`Uⁿ ≤ Kˣ`, `U⁰/U¹ ≃* 𝓀ˣ`, `Uⁿ/Uⁿ⁺¹ ≃* 𝓀⁺` for `n ≥ 1`), `ClassField/UpperBridge.lean`
(upstream's `G^t` = the project's for `t > -1`, `⊤` vs `G_0` on `t ≤ -1`, jump predicates
identified on `(-1, ∞)`, **upper-jump integrality for the project's `G^v(𝒪_L)` with no instance
on `L`**), and the **statement ledger** `Anabelian/Statements/` opening with `L34 : Prop` — the
ramification correspondence `θ(Uⁿ) = Gⁿ(E/K)` at finite level for the Frobenius-normalized
Artin family (proved to exist and be unique from upstream). Ledger: **`0 FOUNDATIONAL / 0
DEBT`**; 101 project files; no open owed witnesses; branch `master`.
**The next task is Pass 100 (below).** L3.4 is IN-PROGRESS: stated, not proved.

Read `CLAUDE.md` (note the new `Anabelian/Statements/` convention), the active table and the
**"External dependencies" section** of `AXIOM_LEDGER.md`, the Pass-99 status header and the L3
ladder in `ROADMAP.md`, the [Pass-99 entry](NOTES.md#pass-99) in `NOTES.md` (the three statement
sets verbatim, the upper-group verdict, the statement-ledger rationale), the
[Pass-98 entry](NOTES.md#pass-98) (the bridge and the identification table), and the
[Pass-97 entry](NOTES.md#pass-97) (the bump's rename/pattern list — the house idioms for the new
Mathlib). Start with `git status`; work on your own parley branch. `scripts/preflight.sh`
enforces the pre-commit checks, now including the statement-ledger clauses 3b/5.

## What Pass 99 supplies

- `ClassField/UnitFiltration.lean`: `integerUnitFiltration K m : Subgroup 𝒪[K]ˣ`
  (`ker (𝒪ˣ → (𝒪/𝓂^m)ˣ)`), `unitFiltration K m : Subgroup Kˣ` (its image),
  `integerUnitsEquiv K m` between them; `mem_unitFiltration_iff`, `unitFiltration_antitone`,
  `unitFiltration_zero_eq_unitGroup`, `unitsQuotEquivResidueUnits : U⁰/U¹ ≃* 𝓀ˣ`; for a
  uniformizer `π` (`hπ : 𝓂[K] = span {π}`) and `1 ≤ m`: `unitCoeff`, `unitLayerHom`,
  `ker_unitLayerHom = Uᵐ⁺¹`, `unitLayerHom_surjective`, `unitLayerQuotEquiv : Uᵐ/Uᵐ⁺¹ ≃*
  Multiplicative 𝓀`, `unitLayerQuotHom_injective`, `unitLayerQuotAddHom_injective`.
- `ClassField/UpperBridge.lean`: `upperRamificationGroup_of_nonpos`,
  `upperRamificationGroup_eq_iSup_of_neg` (no project jump at `t < 0`),
  `inverseHerbrandFunction_eq`, `upperRamificationGroup_eq_of_neg_one_lt`,
  `upperRamificationGroup_eq_top_of_le_neg_one`,
  `upperRamificationGroup_extensionIntegers_eq_of_neg_one_lt` (the transport, as subgroups of
  `L ≃ₐ[K] L`), `isUpperRamificationJump_iff`,
  `upperRamificationGroup_extensionIntegers_jump_int` (universe `Type`, like upstream).
- `Statements/L34.lean`: `IsNormalizedArtinFamily K artin : Prop` (upstream's family
  conclusion as a predicate), `exists_isNormalizedArtinFamily`, `isNormalizedArtinFamily_unique`,
  and `def L34 : Prop`. Every convention choice is in the module docstring (finite level only;
  upstream's geometric Frobenius orientation, irrelevant for subgroup images; `Gⁿ` at
  `extensionIntegers K E` pushed along `Subgroup.subtype`; `n : ℕ`; universe `Type`).

House idioms learned: statement-level `haveI := isNonarchimedeanLocalField_extension K L`
after the two `letI`s *does* make upstream's `L`-instance-dependent constants usable in a
statement (the `Prop`-class instance is found through the `let`); `rw [hA]` with
`hA : (valuation L).valuationSubring = extensionIntegers K L` moves a goal to `𝒪_L` where the
`Finite (D(𝒪_L))` instance lives; `le_or_lt` is now `le_or_gt`; a `RingHom` coerced inside
`Units.map` is handled by `change … Ideal.Quotient.mk … = 1 ↔ _`.

## Next task — Pass 100: open the `L34` proof program (L3.4)

Nothing of `L34` is proved. The pass should produce a dependency map and the first rung:

1. **Inventory upstream toward `θ(Uⁿ) = Gⁿ`** (read, don't guess:
   `.lake/packages/ClassFieldTheory/Lean4/ClassFieldTheory/Theorems/LocalClassFieldTheory/*` —
   in particular `FiniteAbelianLocalReciprocityIndex`, `MemFieldNormSubgroupIff`,
   `FieldNormSubgroupTower`, the `Unramified*` normalization files — and
   `Theorems/ConductorsAndRayClassFields/*` (`IsAbelianConductor.*`), plus whatever in
   `LocalClassFieldTheory/Finite/` and `ValuedFieldTheory/` computes norm indices
   `(Uⁿ : Uⁿ ∩ N Lˣ)` or unit norms). Record in NOTES what exists, with names.
2. **Fix the route.** Serre XV §2 proves `θ(Uⁿ) = Gⁿ` from (a) the unramified case
   (`θ(U⁰) = G_0`: norms from the maximal unramified subextension are exactly `U⁰ · ⟨π^f⟩`), and
   (b) the totally ramified case via Hasse–Arf and the norm-index computation of `Uⁿ`
   (`N(Uⁿ_L) = Uᵐ_K` for `n = ψ(m)`, Serre V §3 / XV §2 Prop. 4), with the general case by the
   tower `L ⊇ L₀ ⊇ K`. Lubin–Tate is the alternative (not in upstream's `Theorems/`). Choose,
   write the dependency map with each rung marked present/absent.
3. **First rung — the `n = 0` case**: `θ_{E/K}(U⁰) = G₀(E/K)` (the image of the units is the
   inertia group). Likely inputs: upstream's unramified normalization (`artin E` on the
   maximal unramified subextension), `E.normSubgroup ⊇` the units iff unramified, and the
   project's `ramificationGroup K 𝒪_E 0` = inertia (Pass 23/Pass 50 `decompositionQuotient`).
   State it as a theorem about `IsNormalizedArtinFamily` families, in the `L34` shape at `n = 0`.
4. **Ledger the `K^ab` form** as a second statements entry (`L34ab` or similar): the inverse
   limit over `E` of the finite-level statement against Pass 83's absolute `G^v` and L3.0's
   `K^ab`, with the same care about which reciprocity object is being quantified over (never
   the `Nonempty` profinite one).

Standard axioms only; ledger stays 0/0; statement-preserving for existing results; no
`sorry`/`axiom`/`native_decide`/heartbeat changes. Fresh files; `lake env lean` probes from the
project root.

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
