# HANDOFF.md — session bootstrap (written after Pass 94, 2026-09-25)

**State:** L2 is complete (Pass 83), consolidated with separation in Pass 84. L3 is
in progress: `K^ab` (Pass 86), the Herbrand-quotient calculus (Passes 87–90), the cyclic
pair and `q(ℤ) = n` (Passes 91–92), and the equivariant DVR valuation sequence with
**`q(Kˣ) = q(Rˣ) · n` under explicit hypotheses** (Passes 93–94).
Ledger: **`0 FOUNDATIONAL / 0 DEBT`**; 93 project files; no open owed witnesses.
**The next task is Pass 95: design the local-field unit quotient proof `q(Rˣ) = 1`.**

Read `CLAUDE.md`, the active table and Pass-94 entry in `AXIOM_LEDGER.md`, the Pass-94
status header and L3 ladder in `ROADMAP.md`, and the Pass-94 entry in `NOTES.md`.
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

## Next task — Pass 95 design

Inventory the route to `q(Rˣ) = 1` for the valuation ring of a cyclic local-field
extension. Identify concrete lemmas for the unit filtration, its action and finite
quotients, and the passage needed for the full unit group. Reuse the P24–27
ramification/unit calculations where they actually apply. Account explicitly for
the two carried `Ĥ¹` finiteness hypotheses and the identification of the cyclic norm
with the field norm; do not silently replace the abstract DVR by a local field.

The output of that design pass should be concrete lemma statements and a dependency
map. This pass proves no unit quotient formula beyond the conditional reduction,
no Hilbert-90 bridge, and no reciprocity theorem. R1–R3 remain untouched.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
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

## Queue after the unit-group design

The remaining L3.1 bridges (concrete Galois norm, `Rep`, Hilbert 90), L3.2 unramified
cohomology, and L3.3 reciprocity precede L3.4's ramification correspondence.
Hasse–Arf remains a separate deferred rung. See ROADMAP for the dependency ladder.
