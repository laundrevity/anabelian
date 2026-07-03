# HANDOFF.md — session bootstrap (written after Pass 63, 2026-07-03)

**State: SERRE IV §1 PROP. 3 IS PROVED, AXIOM-FREE.** The fourteen-pass quotient arc
(P50–63) is complete on top of the Herbrand `φ`/`ψ` analytic theory (P44–49):

> `lowerIndex_decompositionQuotient_mul_eq_sum`
> (`Anabelian/RamificationSumFormula.lean`):
> **`i_{K'/K}(σ̄) · e' = Σ_{h ∈ H} i_{L/K}(s₀ · dr h)`**
> for every `σ̄ = decompositionQuotient s₀` and every irreducible `π` of `B = 𝒪_L ∩ K'`
> (`e' = addVal_{𝒪_L}(ι π)`); tower `K ⊆ K' ⊆ L` over a nonarchimedean local field,
> `K'/K` normal, `L/K'` Galois. Generator-free (P51's intrinsic `lowerIndex`), uniform in
> `σ̄` (`ℕ∞`: both sides `⊤` at `σ̄ = 1`). `#print axioms`: standard-only.

Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations project-wide, through
all 63 passes — keep it that way. **YOUR FIRST TASK is Pass 64 — begin Serre IV §3 Lemma 5**
(below). **Build caution:** `RamificationLiftDvd.lean` (P58) elaborates slowly (~15 min);
all other files ~3 s — put new bricks in fresh files.

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-63 entry), `ROADMAP.md`
(status header says Pass 63), and the **tail of `NOTES.md`** (Passes 50–63: the quotient
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
- `RamificationQuotient` (P50): `decompositionQuotient`, exactness, `comapRingHom` +
  `𝔪`-reflection. `RamificationIndex` (P51): `lowerIndex : ℕ∞`, Lemma-1 forms
  (`mem_ramificationGroup_iff_lt_lowerIndex`, `_add_one_le_`), calculus, `i_H = i_G` (`rfl`),
  `ℕ∞` cofinality helpers. `RamificationQuotientSurjective` (P52): `D(𝒪_L) = ⊤`,
  `decompositionQuotientEquiv`. `RamificationIndexGenerator` (P53): the `addVal` bridge
  `mem_maximalIdeal_pow_iff_le_addVal`, `lowerIndex_eq_addVal`.
  `ExtensionMonogenicDischarge` (P54): `exists_generator_extensionIntegers` (monogenicity),
  `maximalIdeal_eq_span_of_mem_of_notMem_sq`, the binomial tail. `SubextensionCharPoly`
  (P55): `fullProdXSubSMul` (whole-`G` product) + monic descent `F`, `D_{K'}(𝒪_L) = ⊤`.
  `RamificationLiftSet` (P56): `decompositionFiberEquiv` (fiber = coset `s₀·H`, explicit),
  `map_fullProdXSubSMul(_eval)`. `ExtensionComapIntegers` (P57):
  `extensionIntegers_comap_eq` (`𝒪_L ∩ K' = 𝒪_{K'}`), DVR-on-`B`, `baseToComapRingHom`,
  `exists_generator_comap_spec` (generator + telescoping + `i_{K'/K} = addVal_B(σ̄y−y)`).
  `RamificationLiftDvd` (P58): direction (i) + `map_comapRingHom_smul` +
  `dvd_eval_of_dvd_coeff`. `RamificationAddVal` (P59): `addVal_neg/_prod`, the
  `e'`-dilation `addVal_comapRingHom`, the fiber sum `addVal_liftProd`.
  `ExtensionGeneratorRep` (P60): polynomial representation, `adjoin_generator_eq_top`
  (`L = K'(x)`). `RamificationMinpolyBound` (P61): the remainder-vanishing degree count.
  `RamificationDivision` (P62): direction (ii). `RamificationSumFormula` (P63): **Prop. 3**.

## YOUR FIRST TASK — Pass 64: begin Serre IV §3 Lemma 5

**Target (multi-pass):** `(G/H)_{φ_{L/K'}(u)} = G_u H/H` — in project terms: the image of
`ramificationGroup K (𝒪_L)` under `decompositionQuotient` equals the `B`-filtration at
`φ_{L/K'}(u)` (`B = 𝒪_L ∩ K'`; real-indexing via the `⌈·⌉` conventions of P45's upper
numbering). Serre's proof (IV §3, before Prop. 14): for `σ̄ ≠ 1` set
`j(σ̄) := max_{s ↦ σ̄} i_{L/K}(s)` and prove

> **`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j(σ̄) − 1)`**

by combining Prop. 3 (P63) with the counting `Σ_{s ↦ σ̄} i(s) = Σ_{h ∈ H} min(i_H(h), j)`:
if `s₁` attains the max `j`, then `i(s₁·dr h) = min(i_H(h), j)` (uses P51's calculus
`min_lowerIndex_le_lowerIndex_mul` + the max-attainment), and `Σ_h min(i_H(h), m)` is
`e'`-times-`φ`-affine by P48's piecewise formula. Sub-bricks, one per pass:
- **(A) `i(s₁·dr h) = min(i_H-image(h), j)` when `s₁` attains the max** — purely
  `lowerIndex`-level (P51 calculus + `lowerIndex_decompositionRestrict`); a clean first
  brick.
- **(B) the `Σ min`-vs-`φ` counting** — bridge to P48's `herbrandPhi_eq_affine_formula`
  (also needs identifying P59's `addVal`-form `e'` with the index form `|H_0|`-of-`H` —
  possibly its own brick).
- Then Lemma 5's set-level statement via P51's Lemma-1 membership forms; then Prop. 14/15.

**Method (the P43–63 rhythm):** inventory first; `lake env lean` probes **from the project
root**; every Mathlib name source-grepped; fresh file; scope tightly; one rung; clean
partial > half-discharge.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only — with
  65 files the flat directory is due; consider making a near-term pass the refactor pass.

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

## The queue after Pass 64

Lemma 5's bricks → **Lemma 5** → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit `G^v ≤ Gal(K̄/K)` (Serre IV §3).
Optional deepening: `ψ` closed form / `φ` concavity. The **R1-floor** stays
ROADMAP-permitted but **deferred**. R1–R3 remain distant targets that must be earned, never
axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
