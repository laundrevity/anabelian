# HANDOFF.md — session bootstrap (written after Pass 78, 2026-07-04)

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
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-78 entry), `ROADMAP.md`
(status header says Pass 78), and the **tail of `NOTES.md`** (Passes 50–63: the quotient
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

## YOUR FIRST TASK — Pass 79: the L3 gateway design pass (upper numbering on `Gal(K̄/K)`)

**A DESIGN pass — inventory first, decide, write the plan into ROADMAP; code only what the
design settles.** Herbrand-compatibility (P77/P78) is exactly the well-definedness of
`G^v` on an inverse limit of finite quotients. Questions to settle:
1. **Mathlib's absolute-Galois presentation**: grep `Field.absoluteGaloisGroup`,
   `InfiniteGalois`, `ProfiniteGrp`, the fundamental theorem of infinite Galois theory
   files — what is `Gal(K̄/K)` and how are finite quotients indexed
   (`IntermediateField.FiniteGaloisIntermediateField`? the `.fixingSubgroup` lattice?)?
2. **The carrier decision**: attach `G^v(K̄/K)` to WHAT? Options: (i) the inverse limit of
   the finite-level `G^v`s along the P77 maps (needs the FUNCTORIAL form of P77 — two
   arbitrary comparable finite Galois subextensions, not just the two-level tower); (ii) a
   closed-subgroup definition via preimages (`G^v := ⋂_L preimage of G^v(L/K)`); (iii) a
   `Subgroup (K̄ ≃ₐ[K] K̄)` defined directly. Serre does (i)-equivalent; (ii) is likely
   the cheapest formal move.
3. **What P77 must be upgraded to**: the current statement is for the tower
   `K ⊆ K' ⊆ L` with `𝒪_L`-side and comap carrier; the functorial form needs naturality
   in BOTH variables (`L ⊆ L'` extensions of `K'`) — inventory which project pieces are
   generic in `(K', A)` already (most are!) and which fix `A = 𝒪_L`.
4. **The local-field instance for K'**: intermediate fields of `K̄/K` are finite over `K`
   hence local — is `IsNonarchimedeanLocalField` inherited by finite extensions in the
   project (check the Extension/ strata — P36-ish)? Needed to iterate the tower.
Deliverable: an honest dependency map in ROADMAP (which bricks exist, which are one-pass,
which are walls) + the carrier decision recorded + at most ONE new brick coded. Clean
partial > half-discharge. (Alternative if the inventory shows the gateway blocked:
**Hasse–Arf** — Serre IV §3 + V, multi-pass, needs the jump structure + abelian input.)

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

## The queue after Pass 79

Lemma 5's bricks → **Lemma 5** → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit `G^v ≤ Gal(K̄/K)` (Serre IV §3).
Optional deepening: `ψ` closed form / `φ` concavity. The **R1-floor** stays
ROADMAP-permitted but **deferred**. R1–R3 remain distant targets that must be earned, never
axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
