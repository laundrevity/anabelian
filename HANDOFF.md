# HANDOFF.md — session bootstrap (written after Pass 70, 2026-07-03)

**State: SERRE IV §1 PROP. 3 IS PROVED, AXIOM-FREE.** The fourteen-pass quotient arc
(P50–63) is complete on top of the Herbrand `φ`/`ψ` analytic theory (P44–49):

> `lowerIndex_decompositionQuotient_mul_eq_sum`
> (`Anabelian/Quotient/SumFormula.lean`):
> **`i_{K'/K}(σ̄) · e' = Σ_{h ∈ H} i_{L/K}(s₀ · dr h)`**
> for every `σ̄ = decompositionQuotient s₀` and every irreducible `π` of `B = 𝒪_L ∩ K'`
> (`e' = addVal_{𝒪_L}(ι π)`); tower `K ⊆ K' ⊆ L` over a nonarchimedean local field,
> `K'/K` normal, `L/K'` Galois. Generator-free (P51's intrinsic `lowerIndex`), uniform in
> `σ̄` (`ℕ∞`: both sides `⊤` at `σ̄ = 1`). `#print axioms`: standard-only.

**Pass 64 was the long-deferred flat→folders refactor**: `Anabelian/` is now nine content
folders (`Galois`, `FiniteField`, `Reduction`, `Ramification`, `Herbrand`, `Extension`,
`LocalField`, `Quotient`, `ForMathlib`) — `scripts/refactor.sh` (table extended to all 64
files) executed as git-tracked renames; module paths changed, **declaration names unchanged**;
`scripts/preflight.sh` and `scripts/chain_check.py` now recurse into folders. **Pass 65 opened the Lemma-5 arc**: `Anabelian/Quotient/IndexProfile.lean` — the **fiber
index profile** `i_{L/K}(s₁·h) = min(i_H(h), j)` for a coset/fiber maximizer `s₁`
(`lowerIndex_mul_decompositionRestrict_eq_min`, `Normal`-free; `exists_coset/_fiber_...`;
`sum_lowerIndex_fiber_eq_sum_min` — the `Σ min` form that feeds P63). Ledger is
**`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations project-wide, through all 65 passes
— keep it that way. **YOUR FIRST TASK is Pass 66 — the `Σ min`-vs-`φ` counting** (below).
**Build caution:** `Quotient/LiftDvd.lean` (P58) elaborates slowly (~15 min); all other
files ~3 s — put new bricks in fresh files.

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-70 entry), `ROADMAP.md`
(status header says Pass 70), and the **tail of `NOTES.md`** (Passes 50–63: the quotient
arc, ending in the Prop. 3 milestone entry with the arc retrospective). **Session start:**
`git status` — the tree must be clean (`.claude/` and `claude.last` are `.gitignore`d);
`scripts/preflight.sh` clause 0 *enforces* this.

## Where the mathematics stands

**Complete, axiom-free strata:** L1 finite/local Galois theory (P1–21); the L2 lower
filtration + tame/wild theory (P22–28); the descent (`𝒪_L`, `ker θ₀ = G₁`) (P29–37); the
assembly (`IsNonarchimedeanLocalField L`) (P38–41); canonicity (P43); the Herbrand `φ`/`ψ`
analytic theory (P44–49: monotone, continuous, both slopes, `φ`'s closed form, upper
numbering `G^v = G_{⌈ψ(v)⌉}`, `H_u = H ∩ G_u`); **the quotient arithmetic through Prop. 3**
(P50–63).

**The Prop.-3 toolkit (P50–63), by file** — everything Lemma 5 will draw on:
- `Quotient/Basic` (P50): `decompositionQuotient`, exactness, `comapRingHom` +
  `𝔪`-reflection. `Ramification/LowerIndex` (P51): `lowerIndex : ℕ∞`, Lemma-1 forms
  (`mem_ramificationGroup_iff_lt_lowerIndex`, `_add_one_le_`), calculus, `i_H = i_G` (`rfl`),
  `ℕ∞` cofinality helpers. `Quotient/Surjective` (P52): `D(𝒪_L) = ⊤`,
  `decompositionQuotientEquiv`. `Ramification/LowerIndexGenerator` (P53): the `addVal` bridge
  `mem_maximalIdeal_pow_iff_le_addVal`, `lowerIndex_eq_addVal`.
  `Extension/MonogenicDischarge` (P54): `exists_generator_extensionIntegers` (monogenicity),
  `maximalIdeal_eq_span_of_mem_of_notMem_sq`, the binomial tail. `Quotient/CharPoly`
  (P55): `fullProdXSubSMul` (whole-`G` product) + monic descent `F`, `D_{K'}(𝒪_L) = ⊤`.
  `Quotient/LiftSet` (P56): `decompositionFiberEquiv` (fiber = coset `s₀·H`, explicit),
  `map_fullProdXSubSMul(_eval)`. `Quotient/ComapIntegers` (P57):
  `extensionIntegers_comap_eq` (`𝒪_L ∩ K' = 𝒪_{K'}`), DVR-on-`B`, `baseToComapRingHom`,
  `exists_generator_comap_spec` (generator + telescoping + `i_{K'/K} = addVal_B(σ̄y−y)`).
  `Quotient/LiftDvd` (P58): direction (i) + `map_comapRingHom_smul` +
  `dvd_eval_of_dvd_coeff`. `Quotient/AddVal` (P59): `addVal_neg/_prod`, the
  `e'`-dilation `addVal_comapRingHom`, the fiber sum `addVal_liftProd`.
  `Quotient/GeneratorRep` (P60): polynomial representation, `adjoin_generator_eq_top`
  (`L = K'(x)`). `Quotient/MinpolyBound` (P61): the remainder-vanishing degree count.
  `Quotient/Division` (P62): direction (ii). `Quotient/SumFormula` (P63): **Prop. 3**.

## YOUR FIRST TASK — Pass 71: the application — `e' = |H₀|`

All hypotheses are in place (P68 `comapAlgebra` + `ramificationIdx = e'`; P69
`IsGaloisGroup`; P70 everything else + the definitional inertia matching). Assemble:

> `Nat.card (ramificationGroup K' (𝒪_L) 0) = addVal_{𝒪_L}(ι π_B)`-as-ℕ

via: `ramificationGroup_zero_eq_inertia` (P70) → `card_inertia_eq_ramificationIdxIn`
(Mathlib; `G := ↥(D_{K'}(𝒪_L))`, `p := 𝔪_B ≠ ⊥` from the DVR's `not_a_field'`) →
`ramificationIdxIn_eq_ramificationIdx` (check its exact form in the Galois file — it may
need `[p.IsMaximal]` or the primesOver machinery; the single prime here is `𝔪_L`) → P68's
`ramificationIdx_comapRingHom`. Mind: `Finite G` from the `[Fintype]` hypothesis;
`Ideal.Quotient.field` may need `letI` for the separable-residue hypothesis to fire (P70's
instance is stated on the quotient CommRings — check it synthesizes as-is). Statement shape:
for `π : ↥B` irreducible and `(n : ℕ∞) = addVal(ι π)`:
`Nat.card (ramificationGroup K' (extensionIntegers K L) 0) = n` — or cleaner, directly
`(Nat.card (ramificationGroup K' (𝒪_L) 0) : ℕ∞) = addVal(ι π)`. After it: the numerical
Lemma 5 `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)` assembles (P63+P65+P66+P67+P71), then the
set-level Lemma 5 via P51's membership forms; then Prop. 14/15.

**Method (the P43–63 rhythm):** inventory first; `lake env lean` probes **from the project
root**; every Mathlib name source-grepped; fresh file; scope tightly; one rung; clean
partial > half-discharge.

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

## The queue after Pass 71

Lemma 5's bricks → **Lemma 5** → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit `G^v ≤ Gal(K̄/K)` (Serre IV §3).
Optional deepening: `ψ` closed form / `φ` concavity. The **R1-floor** stays
ROADMAP-permitted but **deferred**. R1–R3 remain distant targets that must be earned, never
axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
