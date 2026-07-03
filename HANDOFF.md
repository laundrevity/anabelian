# HANDOFF.md — session bootstrap (written after Pass 55, 2026-07-03)

**State:** the **quotient arc is 6 bricks in** (P50–55), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: skeleton (`decompositionQuotient`, exactness, inertia
preservation, `comapRingHom` reflecting `𝔪`). P51: `i_G` (`lowerIndex : ℕ∞`, Lemma 1,
calculus, `i_H = i_G` by `rfl`). P52: surjectivity (`D(𝒪_L) = ⊤`, `D(A) ⧸ H ≃* D(A ∩ K')`).
P53: concrete `i_G = v_L(σx − x)` (`lowerIndex_eq_addVal`). P54: monogenicity **discharged**
(`𝒪_L = 𝒪_K[x]`, so the concrete `i_G` is unconditional). **P55: the subextension
characteristic polynomial** (`Anabelian/SubextensionCharPoly.lean`, Prop. 3's substrate):
`fullProdXSubSMul G R x = ∏ g : G, (X − C (g·x))` — the **all-of-`G`** product (Mathlib's
`prodXSubSMul` ranges over the orbit — wrong primitive), monic, degree `|G|`, kills `x`,
`G`-invariant coefficients; the **fixed-points descent** (`Gal(L/K')`-fixed integers come from
`A ∩ K'` via `comapRingHom`); the headline **monic lift `F` over `𝒪_L ∩ K'` with
`F.map (comapRingHom) = ∏_{h ∈ Gal(L/K')}(X − h·x)`**, hypothesis-free at `𝒪_L`
(`decompositionSubgroup_extensionIntegers_restrict_eq_top` : `D_{K'}(𝒪_L) = ⊤` for ANY
intermediate `K'`); and `𝒪_L ∩ K = 𝒪_K` (`extensionIntegers_comap_algebraMap`). Ledger is
**`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations project-wide — keep it that way.
**YOUR FIRST TASK is Pass 56 — a divisibility direction of Prop. 3** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-55 entry), `ROADMAP.md`
(status header says Pass 55), and the **tail of `NOTES.md`** (Passes 50–55: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## Where the mathematics stands (the Prop. 3 assembly map)

**Target:** Serre IV §1 Prop. 3, in the project's natural form: for `σ̄ ≠ 1` in `D(𝒪_L ∩ K')`,

> `σ̄y − y` and `∏_{s ↦ σ̄} (s·x − x)` are **associated** in `𝒪_L`

(`y` generates `𝒪_{K'}/𝒪_K`, `x` generates `𝒪_L/𝒪_K` — both exist by P54; the `e'`/sum form
follows by `addVal` bookkeeping). Serre's proof, in project pieces:

- **(i) `a ∣ b`**: coefficients of `σ̄F − F` are `σ̄c − c` with `c ∈ 𝒪_{K'} = 𝒪_K[y]`, each
  divisible by `a = σ̄y − y` — P25's `smul_sub_dvd_of_mem_closure` applied in the `D(B)`-action
  on `B := 𝒪_L ∩ K'` (`B ≅ 𝒪_{K'}`; note P54's generator statement is at `(K, K')` — some
  transport between `𝒪_{K'}` and `B = comap` may be needed; `extensionIntegers_comap_algebraMap`
  is the same-base prototype). Evaluate at `x`: `f(x) = 0` (P55 `fullProdXSubSMul_eval`), so
  `(σ̄f)(x) = ±b` — this needs **the lift-set identity**: `map σ̄ f = ∏_{s ↦ σ̄} (X − s·x)`,
  i.e. the fiber of `decompositionQuotient` over `σ̄` is the coset `s₀ · range
  (decompositionRestrict)` (P50 exactness + P52 surjectivity) and `{s·x | s ↦ σ̄}` (with
  multiplicity) = `{σ̄-transported h·x}`. This identity is the real content of (i).
- **(ii) `b ∣ a`**: `y = g(x)` for `g` over `𝒪_K` (P54 at `(K, L)`); the monic division
  `g(X) − ι y = F·q` over `𝒪_L ∩ K'` (`F` monic, `Polynomial.modByMonic`/degree argument —
  the remainder vanishes because `x` has degree `[L:K']` over `K'` and kills it); transport
  along `σ̄`, evaluate at `x`: `g(x) − σ̄y = (σ̄f)(x)·(σ̄q)(x) = ±b·…`, LHS `= y − σ̄y = −a`.
- **(iii) `addVal` bookkeeping**: `Associated → addVal a = addVal b`;
  `addVal b = Σ_s addVal (s·x − x) = Σ_s i_G(s)` (P53–54); `addVal_L a = e'·addVal_{K'}(σ̄y −
  y) = e'·i_{G'}(σ̄)` — the `e'`-dilation `v_L|_{K'} = e'·v_{K'}` is a NEW brick (relate
  `addVal` of `𝒪_L` on `comapRingHom`-images to `addVal` of `𝒪_L ∩ K'`; `𝔪_B^k` maps into
  `𝔪_A^{e'k}`-style — `exists_pow_maximalIdeal_le_map` at `(K', L)` is the crude form).

**Key names by file:** P50 `RamificationQuotient.lean` (`decompositionQuotient`, `_ker`,
`comapRingHom`, `mem_maximalIdeal_of_comapRingHom`); P51 `RamificationIndex.lean`
(`lowerIndex`, Lemma 1 forms, calculus, `ℕ∞` cofinality helpers); P52
`RamificationQuotientSurjective.lean` (`decompositionQuotient_surjective`,
`decompositionQuotientEquiv`); P53 `RamificationIndexGenerator.lean`
(`mem_maximalIdeal_pow_iff_le_addVal`, `lowerIndex_eq_addVal`); P54
`ExtensionMonogenicDischarge.lean` (`exists_generator_extensionIntegers`,
`exists_generator_lowerIndex_eq_addVal`, `maximalIdeal_eq_span_of_mem_of_notMem_sq`,
`exists_pow_one_add_eq`); P55 `SubextensionCharPoly.lean` (all `fullProdXSubSMul*`,
`exists_comapRingHom_eq_of_forall_smul_eq`, `exists_fullProdXSubSMul_lift*`,
`decompositionSubgroup_extensionIntegers_restrict_eq_top`,
`extensionIntegers_comap_algebraMap`); P25 `TameInjectivity.lean`
(`smul_sub_dvd_of_mem_closure` — takes `A` implicitly).

## YOUR FIRST TASK — Pass 56: one Prop. 3 brick

Scope ONE of (in rough order of value):
- **(A) The lift-set identity** (the substrate of (i), purely group/product-theoretic):
  `map (σ̄-action) (fullProdXSubSMul (D_{K'}) 𝒪_L x) = ∏_{s ∈ fiber σ̄} (X − C (s·x))` — via
  the fiber-as-coset description (`decompositionQuotient_ker` + surjectivity) and a product
  reindexing (`Equiv.prod_comp` with the coset bijection `h ↦ s₀·h`). May need: the action of
  `σ̄ ∈ D(B)` on `(𝒪_L ∩ K')[X]`-lifted polynomials vs a lift `s₀`'s action upstairs —
  design this API carefully; it is the hinge of direction (i).
- **(B) Direction (ii)'s division brick**: the monic division `P = F·q + r`, `r = 0` when
  `eval₂ x P = 0` and `natDegree P < …` fails — i.e. the "minimal polynomial" property of `F`
  (needs `natDegree F = [L:K']` = `|Gal(L/K')|` — P55's degree + `IsGalois.card_aut_eq_finrank`,
  and `K'`-linear independence of `1, x, …, x^{d−1}` from `L = K'(x)` — check what P54's
  generator gives at the field level: `𝒪_K[x] = 𝒪_L ⟹ K(x) = L`).
- **(C) The `e'`-dilation brick** for (iii): `addVal_A (comapRingHom b) = e' · addVal_B b`
  with `e' := addVal_A (comapRingHom π_B)` — self-contained DVR arithmetic.
Do NOT attempt all of Prop. 3; clean partial > half-discharge.

**Method (the P43–55 rhythm):** inventory first; `lake env lean` probes; every Mathlib name
source-grepped; `lake build Anabelian.<File>`; scope tightly.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- Mathlib's `prodXSubSMul` ranges over the ORBIT; the project's `fullProdXSubSMul` over all
  of `G` — don't confuse them (bit the P55 design once).
- `𝒪[K]` (the `ValuativeRel` notation) is a `Subring`, not a `ValuationSubring` — statements
  at the `ValuationSubring` level go through `(valuation K).valuationSubring` +
  `Valuation.mem_valuationSubring_iff`/`mem_integer_iff` (both `Iff.rfl`) (bit P55).
- `ℕ∞` numerals vs casts: explicit `((k:ℕ):ℕ∞)` `have`s + `.mp`/`.mpr` term-style (P54).
- `residue` vs `Ideal.Quotient.mk`: defeq, not syntactic — route through `have` (P54).
- Prefer `Nat.card` API (`pow_card_eq_one'`, `Nat.card_units` — `α` explicit) over
  `Fintype.card` (P54). P25's closure lemmas take `A` implicitly (P53).
- Narrow `variable` blocks (P52); `push Not` (P51); `_root_.mem_nonunits_iff` (P50); `calc` +
  `AlgEquiv.restrictNormal_commutes` across the `restrictNormalHom` defeq (P50).
- DVR/`ℕ∞` toolkit: P51 cofinality lemmas, P53 `mem_maximalIdeal_pow_iff_le_addVal`, P54
  `maximalIdeal_eq_span_of_mem_of_notMem_sq` + `exists_pow_one_add_eq`.
- D2 (spectral bridge) lives entirely inside proofs; P52–55 consumed only `IsIntegral`-level
  API — keep it that way.

## The queue after Pass 56

The remaining Prop. 3 bricks ((A)/(B)/(C), then the assembly `Associated a b` + the sum
formula) → IV §3 **Lemma 5** `(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity** (Prop. 15)
+ **Herbrand's theorem** `(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit
`G^v ≤ Gal(K̄/K)`. Optional deepening: `ψ` closed form / `φ` concavity. The **R1-floor** stays
ROADMAP-permitted but **deferred**. R1–R3 remain distant targets that must be earned, never
axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
