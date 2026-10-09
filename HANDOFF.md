# HANDOFF.md — session bootstrap (written after Pass 97, 2026-10-08)

**State:** L2 is complete (Pass 83), consolidated with separation in Pass 84. L3 is
in progress: `K^ab` (Pass 86), the Herbrand-quotient calculus (Passes 87–90), the cyclic
pair and `q(ℤ) = n` (Passes 91–92), and the equivariant DVR valuation sequence with
**`q(Kˣ) = q(Rˣ) · n` under explicit hypotheses** (Passes 93–94). Pass 95 proves
the finite-acyclic-kernel reduction and records the complete local unit proof design;
Pass 96 proves that design's field-free layer (stable actions, the regular module,
filtration lifting). Pass 97 is a governance pass: the Mathlib bump `v4.30.0` →
`0653561` (Lean `v4.35.0-rc2`), ported statement-preserving on branch `mathlib-bump`.
Ledger: **`0 FOUNDATIONAL / 0 DEBT`**; 97 project files; no open owed witnesses.
**The next task is Pass 98: the abstract DVR unit filtration `U^m` and its finite
quotients (the Pass-95 design's P97 row).** The local-field formula `q(Rˣ) = 1` remains
unproved.

Read `CLAUDE.md`, the active table and Pass-96/97 entries in `AXIOM_LEDGER.md`, the Pass-97
status header and L3 ladder in `ROADMAP.md`, the [Pass-97 entry](NOTES.md#pass-97) in
`NOTES.md` (the bump's rename/pattern list — the house idioms for the new Mathlib), the [Pass-95 entry](NOTES.md#pass-95)
in `NOTES.md` (complete signatures, dependency map, and P96–P102 order), and the
[Pass-96 entry](NOTES.md#pass-96) (what of it is now proved, and the deviations).
Start with `git status`; work on your own parley branch. `scripts/preflight.sh`
enforces the pre-commit checks. Historical pass records are in NOTES and the ledger.

## What Pass 94 supplies

- `ClassField/UnitsValuation.lean`: `intValuation_irreducible`, now the shared
  multiplicity proof used by Pass 93's kernel calculation.
- `ClassField/CyclicPair.lean`: `map_mulAut_pow`, `map_cyclicDiff`, and
  `map_cyclicNorm`, with no periodicity hypothesis.
- `ClassField/TrivialAction.lean`: `multiplicative_int_pow_eq_one` and
  `finite_herbrandH_norm_diff_int` (finiteness from cardinality one).
- `ClassField/UnitsValuationEquivariance.lean`: `intValuation_ringEquiv`, injectivity
  and equivariance of the units inclusion, `dvrUnitsValuation_equivariant`, the
  cyclic norm/difference valuation formulas, and `cyclicHerbrandQuotient_units`.

The headline takes a DVR `R`, its fraction field `K`, `s : R ≃+* R`, `t : K ≃+* K`,
and `hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r)`. With induced unit actions
`σR`, `σK`, it carries `n ≠ 0`, `σK ^ n = 1`, and `Finite (herbrandH N D)` on each of
`Rˣ` and `Kˣ`. The value-group action is trivial and its `Ĥ¹` finiteness is derived.
No separate periodicity hypothesis on `Rˣ` is supplied. No necessity or sharpness
claim is made for these carried hypotheses.

## What Pass 95 supplies

`ClassField/FiniteAcyclic.lean` proves `finite_acyclic_kernel_reduction`: for a
pair-equivariant SES with both kernel cohomology groups subsingletons and finite
quotient, both middle cohomology groups are finite and the middle Herbrand quotient
is one. The proof derives middle finiteness using `snake_exact_mid` in both orders
before invoking multiplicativity. Audit: `[propext, Classical.choice, Quot.sound]`.

The adopted design uses Mathlib's `IsGalois.normalBasis`, integral scaling and a
small normal lattice `B`, unit subgroups `V_i = 1 + π^i B`, regular graded actions,
and transport of `IsAdicComplete` to the extension integers. It derives both P94
`Ĥ¹` instances and separately identifies the cyclic norm with `Algebra.norm`.
P24–27 supply action/coefficient calculations, not a unit filtration or its limit
step. No field-normal-basis theorem is missing. All arithmetic statements in
NOTES remain future targets; the reduction is the only new proved theorem.

## What Pass 96 supplies

- `ClassField/StableAction.lean`: `apply_mem_iff_of_map_eq`, `cyclicNorm_mem_of_map_eq`,
  `cyclicDiff_mem_of_map_eq`; `restrictAut` (`restrictAut_coe` is `rfl`), `quotientAut`
  (`quotientAut_mk`), `Layer`, `layerAut` (`layerAut_mk`); the cyclic-pair naturality
  along inclusion/projection/layer projection (`cyclicNorm_restrictAut_coe`,
  `cyclicNorm_quotientAut_mk`, `cyclicNorm_layerAut_mk` and the `cyclicDiff` versions);
  `herbrandH_subsingleton_of_exact`.
- `ClassField/FiltrationLifting.lean`: `ker_eq_range_of_filtration` (successive
  approximation), `layer_of_surjective`, `cyclic_exact_of_complete_filtration` (no
  `Antitone` hypothesis — the catalogue's is the weaker instance).
- `ClassField/RegularModule.lean`: `regularShift` (= `MulEquiv.arrowCongr (Equiv.mulLeft g)
  (MulEquiv.refl C)`, application `rfl`), `regularShift_pow_apply`, `prod_range_card_pow`,
  `cyclicNorm_regularShift_apply` (the norm is the constant `∏_{k ∈ G} f k`),
  `regular_cyclic_exact`.

How they chain in P101–P102: for `V₀ ≤ 𝒪_Lˣ` with `F i := (V i).subgroupOf V₀` and the
restricted action, `lattice_unit_layer_regular` + `regular_cyclic_exact` give the layer
input of `cyclic_exact_of_complete_filtration` (transport the range/kernel equalities along
the layer `MulEquiv`); its output through `herbrandH_subsingleton_of_exact` is the pair of
`Subsingleton` instances for `finite_acyclic_kernel_reduction` on `1 → V₀ → 𝒪_Lˣ → 𝒪_Lˣ/V₀ → 1`,
whose four intertwinings are the `restrictAut_coe`/`quotientAut_mk` naturality lemmas.

## What Pass 97 supplies

A governance pass: Mathlib `v4.30.0` → commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`
(Lean `v4.35.0-rc2`). No new mathematics; 55 files edited inside proofs/imports; the one
statement-text change is the constant rename `Ideal.ramificationIdx` →
`Ideal.ramificationIdx'` in `ramificationIdx_comapRingHom` (identical definition). New house
idioms forced by the bump (details in NOTES Pass 97): `have`/`let` for `Prop`-valued binders
(the `haveILetI` linter), `change` not `show` for goal changes, term-mode application instead
of `rw` when a `def` wrapping a quotient/bundled carrier has been unfolded, TFAE indices from 1,
`isIntegral_algebraMap_iff (B := _)`, `ite_eq_left`/`ite_eq_right`, `Set.mem_ofPred_eq`,
`MonoidHom.domRestrict`. Mathlib now supplies `Algebra (ResidueField R) (ResidueField S)` and
its scalar towers from `IsLocalHom (algebraMap R S)`, and the two-ideal ramification index is
`ramificationIdx'` while `q.ramificationIdx R` is a new localization-length definition.

## Next task — Pass 98: the abstract unit filtration (design row P97)

Implement NOTES Pass 95 §4 (its P97 row — numbered Pass 98 after the governance Pass 97),
in the abstract DVR context
`(R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` — no local field:

- `unitFiltration R m := (Units.map (Ideal.Quotient.mk (maximalIdeal R ^ m)).toMonoidHom).ker`
  with `mem_unitFiltration`, `unitFiltration_zero`, `unitFiltration_antitone`,
  `unitFiltration_separated` (Krull: `Ideal.iInf_pow_eq_bot_of_isLocalRing`),
  `unitFiltration_stable` (any `s : R ≃+* R`, in the `map`-equality form that
  `restrictAut`/`quotientAut` consume).
- `finite_unitQuotient [Finite (ResidueField R)] m` and `finite_units_quotient_of_le`
  (`Ideal.finite_quotient_pow` + the unit map into the finite quotient ring; the
  residue-field instance must be supplied as `Finite (R ⧸ maximalIdeal R)` by a named
  `haveI`, as in P95's probe).
- `unitsResidueEquiv : (Rˣ ⧸ unitFiltration R 1) ≃* (ResidueField R)ˣ`
  (`IsLocalRing.surjective_units_map_of_local_ringHom`), and the depth-`m` coefficient map
  `unitCoeff π hπ m hm : unitFiltration R m →* Multiplicative (ResidueField R)` with
  `unitCoeff_spec`, `unitCoeff_exact` (surjective, kernel `U^(m+1)`), and
  `unitCoeff_action` (the twisted formula `residue (s a) * residue c ^ m`).

Exact signatures are in NOTES Pass 95 §4; the `unitCoeff` lemmas are the only ones with
real content (well-definedness of the coefficient uses that `π ^ m` is a nonzerodivisor).
No local-field arithmetic, no Hilbert 90, no reciprocity, no R1–R3 work. Standard axioms
only; ledger remains 0/0. Fresh file(s); `lake env lean` probes from the project root.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (Lean `v4.35.0-rc2`, Mathlib `0653561`, since
  Pass 97). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
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
- D2 lives entirely inside proofs; P52–63 consumed only `IsIntegral`-level API.

## Queue after Pass 98 (design rows P98–P102, i.e. Passes 99–103)

Row P98: local action, period, adic transport, and field norm. Row P99: the small normal
lattice. Row P100: its unit subgroups and complete filtration. Row P101: regular layers and
acyclicity. Row P102: unit quotient one, both finiteness discharges, and the P94 field
quotient formula. The detailed dependencies and scope are in NOTES Pass 95; boundaries
may split.

The remaining L3.1 bridges (`Rep`, Hilbert 90), L3.2 unramified
cohomology, and L3.3 reciprocity precede L3.4's ramification correspondence.
Hasse–Arf remains a separate deferred rung. See ROADMAP for the dependency ladder.
