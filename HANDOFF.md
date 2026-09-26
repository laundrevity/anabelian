# HANDOFF.md — session bootstrap (written after Pass 97, 2026-09-26)

**State:** L2 is complete (Pass 83), consolidated with separation in Pass 84. L3 is
in progress: `K^ab` (Pass 86), the Herbrand-quotient calculus (Passes 87–90), the cyclic
pair and `q(ℤ) = n` (Passes 91–92), and the equivariant DVR valuation sequence with
**`q(Kˣ) = q(Rˣ) · n` under explicit hypotheses** (Passes 93–94). Pass 95 proves
the finite-acyclic-kernel reduction and records the complete local unit proof design;
Pass 96 proves that design's field-free layer (stable actions, the regular module,
filtration lifting). Pass 97 proves the abstract DVR unit filtration, finite quotients
under finite residue, the residue equivalence, and the exact coefficient hom with
twisted action. Ledger: **`0 FOUNDATIONAL / 0 DEBT`**; 98 project files; no open
owed witnesses. **The next task is Pass 98: local action and period, adic-completeness
transport, and field-norm comparison.** The local-field formula `q(Rˣ) = 1` remains unproved.

Read `CLAUDE.md`, the active table and Pass-97 entry in `AXIOM_LEDGER.md`, the Pass-97
status header and L3 ladder in `ROADMAP.md`, the [Pass-95 entry](NOTES.md#pass-95)
in `NOTES.md` (complete signatures, dependency map, and P96–P102 order), and the
[Pass-96](NOTES.md#pass-96) and [Pass-97](NOTES.md#pass-97) entries (what is now proved).
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
step. No field-normal-basis theorem is missing. P95 introduced no arithmetic proofs;
its only new proved theorem was the reduction.

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

`ClassField/UnitFiltration.lean` implements NOTES Pass 95 §4 (the P97 row), in the DVR context
`(R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` — no local field:

- `unitFiltration R m := (Units.map (Ideal.Quotient.mk (maximalIdeal R ^ m)).toMonoidHom).ker`
  with `mem_unitFiltration`, `unitFiltration_zero`, `unitFiltration_antitone`,
  `unitFiltration_separated` (Krull: `Ideal.iInf_pow_eq_bot_of_isLocalRing`),
  `unitFiltration_stable` (any `s : R ≃+* R`, in the `map`-equality form that
  `restrictAut`/`quotientAut` consume).
- `finite_unitQuotient [Finite (ResidueField R)] m` and `finite_units_quotient_of_le`
  (`Ideal.finite_quotient_pow` + the unit map into the finite quotient ring; the
  residue-field instance is supplied as `Finite (R ⧸ maximalIdeal R)` by a named
  proof-local `haveI`, as in P95's probe).
- `unitsResidueEquiv : (Rˣ ⧸ unitFiltration R 1) ≃* (ResidueField R)ˣ`
  (`IsLocalRing.surjective_units_map_of_local_ringHom`), with `unitsResidueEquiv_mk`,
  and the depth-`m` coefficient map
  `unitCoeff π hπ m hm : unitFiltration R m →* Multiplicative (ResidueField R)` with
  `unitCoeff_spec`, `unitCoeff_exact` (surjective, kernel `U^(m+1)`), and
  `unitCoeff_action` (the twisted formula `residue (s a) * residue c ^ m`).

The four coefficient helpers are `unitFiltration_exists_coeff`, `unitCoeffLift`,
`unitCoeffLift_spec`, and `unitCoeffLift_eq`. The lift is the unique exact coefficient
in `u = 1 + π^m*a`; cancellation of `π^m` proves uniqueness. All eighteen declarations
audit `[propext, Classical.choice, Quot.sound]`. The statement catalogue is unchanged;
the residue projection formula and coefficient helpers are additional API.

## Next task — Pass 98: local action, completeness, and field norm

Implement NOTES Pass 95 §§5–6 (the P98 row). The local statements explicitly assume
`K` is a nonarchimedean local field and `L/K` is finite Galois. Write
`R := ↥(extensionIntegers K L)`; use the scalar action from `extensionAlgebraMap K L`.

- `integerAut K L g : R ≃+* R`, using
  `decompositionSubgroup_extensionIntegers_eq_top` and `MulSemiringAction.toRingEquiv`.
  Prove `integerAut_coe`: its image in `L` is `g (r : L)`, giving P94's compatibility.
- With `σR` and `σL` the induced unit automorphisms, prove `generator_period` for
  `hgen : Subgroup.zpowers g = ⊤`: `Module.finrank K L ≠ 0`, and both unit actions
  raised to that degree are one. Mathlib's generator/order/cardinality API and
  `IsGalois.card_aut_eq_finrank` supply the enumeration and period.
- `isAdicComplete_extensionIntegers : IsAdicComplete (maximalIdeal R) R`.
  Install the extension valuation, topology, local-field instance, and the P41
  additive uniformity instances. Transport Mathlib's `IsAdicComplete 𝓂[L] 𝒪[L]`
  across `valued_integer_extensionValuativeRel K L`; no completeness is inferred
  from a bare DVR. The instance path was probed in P95; the transport is still work.
- In the separate finite-Galois field context, prove `cyclicNorm_eq_fieldNorm` on
  `x : Lˣ` and `cyclicNorm_eq_fieldNorm_units` as an equality of monoid homs.
  Reindex `Algebra.norm_eq_prod_automorphisms` by powers of the specified generator.
  P96's `prod_range_card_pow` is now available. The target norm hom is
  `(Units.map (algebraMap K L).toMonoidHom).comp (Units.map (Algebra.norm K))`.

Full signatures and the transport instance names are in NOTES Pass 95 §§5–6.
P98 does not construct the small lattice or discharge either `Ĥ¹` finiteness input.
Standard axioms only, ledger 0/0; no Hilbert 90, reciprocity, or R1–R3 work.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
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

## Queue after P98

P99: the small normal lattice. P100: its unit subgroups and complete filtration.
P101: regular layers and acyclicity. P102: unit quotient one, both finiteness discharges,
and the P94 field quotient formula. The detailed dependencies and scope are in
NOTES Pass 95; boundaries may split.

The remaining L3.1 bridges (`Rep`, Hilbert 90), L3.2 unramified
cohomology, and L3.3 reciprocity precede L3.4's ramification correspondence.
Hasse–Arf remains a separate deferred rung. See ROADMAP for the dependency ladder.
