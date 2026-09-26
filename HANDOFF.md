# HANDOFF.md — session bootstrap (written after Pass 95, 2026-09-26)

**State:** L2 is complete (Pass 83), consolidated with separation in Pass 84. L3 is
in progress: `K^ab` (Pass 86), the Herbrand-quotient calculus (Passes 87–90), the cyclic
pair and `q(ℤ) = n` (Passes 91–92), and the equivariant DVR valuation sequence with
**`q(Kˣ) = q(Rˣ) · n` under explicit hypotheses** (Passes 93–94). Pass 95 proves
the finite-acyclic-kernel reduction and records the complete local unit proof design.
Ledger: **`0 FOUNDATIONAL / 0 DEBT`**; 94 project files; no open owed witnesses.
**The next task is Pass 96: generic actions, regular cyclic exactness, and two-map
filtration lifting.** The local-field formula `q(Rˣ) = 1` remains unproved.

Read `CLAUDE.md`, the active table and Pass-95 entry in `AXIOM_LEDGER.md`, the Pass-95
status header and L3 ladder in `ROADMAP.md`, and the [Pass-95 entry](NOTES.md#pass-95)
in `NOTES.md` (complete signatures, dependency map, and P96–P102 order).
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

## Next task — Pass 96 implementation

Implement the field-free part of NOTES Pass 95, sections 3 and the P96 row:

- `restrictAut`, `quotientAut`, `layerAut`, and their carrier/projection formulas;
  use P94 naturality for the norm and difference intertwinings.
- `regularShift` via `MulEquiv.arrowCongr`, its application formula, and
  `regular_cyclic_exact` for a finite group with a specified generator.
- `layer_of_surjective`, `ker_eq_range_of_filtration` for an arbitrary pair
  `(f,g)`, its cyclic corollary, and `herbrandH_subsingleton_of_exact`.

The lifting proof makes successive corrections, uses the stated completeness
property for the partial products, and uses separation to eliminate the error.
Apply the general lemma in both orders for cyclic exactness. Its layer input is
exactness, not merely finite-layer quotient value one. The complete statement
catalogue can be re-probed from NOTES using the recipe there; keep placeholders
in ignored scratch files only. No local-field arithmetic, Hilbert 90, reciprocity,
or R1–R3 work is in P96. Standard axioms only; ledger remains 0/0.

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

## Queue after P96

P97: abstract unit filtration and finite quotients. P98: local action, period,
adic transport, and field norm. P99: the small normal lattice. P100: its unit
subgroups and complete filtration. P101: regular layers and acyclicity. P102:
unit quotient one, both finiteness discharges, and the P94 field quotient formula.
The detailed dependencies and scope are in NOTES Pass 95; boundaries may split.

The remaining L3.1 bridges (`Rep`, Hilbert 90), L3.2 unramified
cohomology, and L3.3 reciprocity precede L3.4's ramification correspondence.
Hasse–Arf remains a separate deferred rung. See ROADMAP for the dependency ladder.
