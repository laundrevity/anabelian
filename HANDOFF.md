# HANDOFF.md — session bootstrap (written after Pass 57, 2026-07-03)

**State:** the **quotient arc is 8 bricks in** (P50–57), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: skeleton. P51: `i_G` (`lowerIndex`, Lemma 1, calculus). P52:
surjectivity. P53: concrete `i_G = v_L(σx − x)`. P54: monogenicity discharged. P55: Serre's
polynomial + descent to `𝒪_L ∩ K'`. P56: the lift-set identity. **P57: the transport +
telescoping** (`Anabelian/ExtensionComapIntegers.lean`): **`𝒪_L ∩ K' = 𝒪_{K'}`**
(`extensionIntegers_comap_eq`, 4 lines via `isIntegral_algebraMap_iff`), the iso
`comapIntegersEquiv` (value-preserving, hand-rolled), **DVR instance on `B = 𝒪_L ∩ K'`**,
`baseToComapRingHom : 𝒪_K →+* B`, P54's generator **transported to `B`**
(`exists_generator_comap`), and the headline **`exists_generator_comap_spec`**: one `y ∈ B`
with (1) `B = 𝒪_K[y]`, (2) **`(σ̄y − y) ∣ (σ̄c − c)`** for every `σ̄ ∈ D(B)`, `c ∈ B` —
direction (i)'s arithmetic half — and (3) **`lowerIndex K B σ̄ = addVal_B (σ̄y − y)`** — the
sum formula's left side, concrete. Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom`
declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 58 — finish direction
(i): `a ∣ b`** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-57 entry), `ROADMAP.md`
(status header says Pass 57), and the **tail of `NOTES.md`** (Passes 50–57: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## The Prop. 3 assembly map (Serre IV §1) — updated

**Target:** for `σ̄ ≠ 1` in `D(B)`: `ι(σ̄y − y)` and `∏_{s ↦ σ̄} (s·x − x)` are **associated**
in `𝒪_L` (`ι = comapRingHom K' 𝒪_L : B →+* 𝒪_L`); then `addVal` both sides + (3) above +
the `e'`-dilation give the sum formula. Remaining bricks:

- **(i) `a ∣ b` — evaluation half (PASS 58)**: all coefficients of `σ̄F − F` are divisible by
  `a = σ̄y − y` in `B` (P57 (2), applied to each coefficient of P55's `F`). Push through
  `ι = comapRingHom` and evaluate at `x`:
  `ι a ∣ ((σ̄F − F).map ι).eval x = (σ̄f)(x) − f(x) = (σ̄f)(x) = ± b` (P55 `_eval` = 0 kills
  `f(x)`; P56's `map_fullProdXSubSMul_eval` computes `(σ̄f)(x)`).
  **The one missing small lemma**: the equivariance `ι (σ̄ • c) = s₀ • (ι c)` for a lift
  `s₀ ↦ σ̄` — i.e. `(F.map ι).map (toRingAut s₀) = (F.map-σ̄-action).map ι` at the polynomial
  level. Note P50's `algebraMap_decompositionQuotient_smul` is exactly this identity at the
  `K'`-value level (`algebraMap K' L (σ̄ • b) = s (algebraMap K' L b)` when
  `decompositionQuotient s = σ̄` — check its exact form; it's stated for
  `σ̄ := decompositionQuotient s`). Also needed: "`d ∣ every coeff of P` ⟹ `d ∣ P.eval z`"
  — trivial induction via `Polynomial.eval_eq_sum_range` + `Finset.dvd_sum`, or check
  Mathlib for a ready lemma.
- **(ii) `b ∣ a`**: `y = g(x)` over `𝒪_K` (P54 at `(K, L)` — note: need the generator `x` of
  `𝒪_L/𝒪_K`, which also generates over `B` ⊇ `𝒪_K`-image, so P55's `F` at that same `x` is
  the right `f`); monic division `g(X) − ι y = F_L·q` over... (design: work with `f` and the
  division in `B[X]` via P55's monic `F`, remainder vanishes by the degree-vs-independence
  argument); transport along `σ̄`, evaluate at `x`.
- **(iii) `addVal` bookkeeping**: `Associated → addVal` equal; `addVal_L b = Σ_h i_G(s₀·dr h)`
  (P53–54 + P56 fiber parametrization + `addVal` of a product = sum); the **`e'`-dilation**
  `addVal_L (ι a) = e' · addVal_B a` (`e' := addVal_L (ι π_B)`) — self-contained DVR brick;
  combine with P57 (3).

**Key names:** P50 `RamificationQuotient.lean` (`decompositionQuotient`, `comapRingHom`,
`algebraMap_decompositionQuotient_smul`, `mem_maximalIdeal_of_comapRingHom`); P51
`RamificationIndex.lean`; P52 `RamificationQuotientSurjective.lean`; P53
`RamificationIndexGenerator.lean` (`mem_maximalIdeal_pow_iff_le_addVal`,
`lowerIndex_eq_addVal`); P54 `ExtensionMonogenicDischarge.lean`
(`exists_generator_extensionIntegers`, `maximalIdeal_eq_span_of_mem_of_notMem_sq`); P55
`SubextensionCharPoly.lean` (`fullProdXSubSMul*`, `exists_fullProdXSubSMul_lift*`,
`decompositionSubgroup_extensionIntegers_restrict_eq_top`); P56 `RamificationLiftSet.lean`
(`map_fullProdXSubSMul(_eval)`, `decompositionFiberEquiv(_apply_coe)`); P57
`ExtensionComapIntegers.lean` (`extensionIntegers_comap_eq`, `comapIntegersEquiv`,
`isDiscreteValuationRing_comap`, `baseToComapRingHom`, `exists_generator_comap(_spec)`,
`smul_baseToComapRingHom_range_eq`); P25 `TameInjectivity.lean`
(`smul_sub_dvd_of_mem_closure` — `A` implicit).

## YOUR FIRST TASK — Pass 58: finish direction (i)

Scope: the equivariance lemma (`ι (σ̄ • c) = s₀ • (ι c)` — from/alongside P50's
`algebraMap_decompositionQuotient_smul`), the "divides every coefficient ⟹ divides the
evaluation" lemma, and the assembly:

> **`a ∣ b`**: for `σ̄ ∈ D(B)`, a lift `s₀`, P55's `F` (over `B`) and P57's `y`:
> `ι (σ̄ • y − y) ∣ ∏_{h} (x − (s₀ · dr h) • x)` in `𝒪_L`.

Watch the two-action bookkeeping: `σ̄ • F` should be the coefficient-wise `D(B)`-action
(`Polynomial.smul` under the `MulSemiringAction D(B) ↥B` — the action exists since `B`'s
decomposition group acts on `↥B`; P55/P56 used the analogous action upstairs). If the
`σ̄ • F` form fights, work coefficient-wise directly: `a ∣ σ̄ • (F.coeff n) − F.coeff n`
(P57 (2)) and sum via `eval_eq_sum_range`. Clean partial > half-discharge — if the assembly
is long, the equivariance + divides-evaluation lemmas alone are a complete pass.

**Method (the P43–57 rhythm):** inventory first; `lake env lean` probes; every Mathlib name
source-grepped; `lake build Anabelian.<File>`; scope tightly.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- `rw` needs syntactically matching coercion forms — state `have`s in `⇑e.toRingHom` form,
  not `⇑↑e` (bit P57); hand-rolled subtype equivs (`Subtype.ext rfl` fields) beat
  `RingEquiv.subringCongr` for `ValuationSubring` friction (P57); structure-field proofs by
  plain defeq application (`map_mul (algebraMap K K') x.1 y.1`), not `push_cast` (P57).
- The style linter rejects goal-changing `show` — use `change` (P56).
- Mathlib's `prodXSubSMul` is orbit-indexed; project `fullProdXSubSMul` is whole-`G` (P55).
- `𝒪[K]` is a `Subring`; `ValuationSubring` statements via `(valuation K).valuationSubring`
  (P55). `ℕ∞` numerals vs casts: explicit `((k:ℕ):ℕ∞)` (P54); `residue` vs `mk` defeq-not-
  syntactic (P54); prefer `Nat.card` API (P54); P25 closure lemmas take `A` implicitly (P53);
  narrow `variable` blocks (P52); `push Not` (P51); `_root_.mem_nonunits_iff` (P50).
- DVR/`ℕ∞` toolkit: P51 cofinality, P53 `mem_maximalIdeal_pow_iff_le_addVal`, P54
  `maximalIdeal_eq_span_of_mem_of_notMem_sq` + `exists_pow_one_add_eq`, P57 DVR-on-`B`.
- D2 lives entirely inside proofs; P52–57 consumed only `IsIntegral`-level API.

## The queue after Pass 58

Direction (ii) (`b ∣ a`, monic division), the `addVal` bookkeeping ((iii): fiber sum +
`e'`-dilation), the **Prop. 3 assembly**, → IV §3 **Lemma 5** `(G/H)_{φ_{L/K'}(u)} = G_u H/H`
→ **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem** (Prop. 14) → Hasse–Arf. Optional:
`ψ` closed form / `φ` concavity. The **R1-floor** stays deferred. R1–R3 remain distant targets
that must be earned, never axiomatized — the line between inputs and targets is drawn in
`ROADMAP.md` and is the project's reason for existing.
