# HANDOFF.md — session bootstrap (written after Pass 54, 2026-07-03)

**State:** the **quotient arc is 5 bricks in** (P50–54), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: skeleton (`decompositionQuotient`, exactness, inertia
preservation, `𝔪`-reflection `comapRingHom`). P51: `i_G` as `lowerIndex : ℕ∞` + Lemma 1 +
calculus + `i_H = i_G` (`rfl`). P52: surjectivity (`D(𝒪_L) = ⊤` ⟹ `D(A) ⧸ H ≃* D(A ∩ K')`).
P53: the concrete `i_G = v_L(σx − x)` (`lowerIndex_eq_addVal`) under the monogenicity package.
**P54: the monogenicity DISCHARGE** (`Anabelian/ExtensionMonogenicDischarge.lean`, Serre III §6
Prop. 12, finite-residue case): **`𝒪_L` is monogenic over `𝒪_K`**
(`exists_generator_extensionIntegers`), so the concrete `i_G` is **UNCONDITIONAL**:
`∃ x, ∀ σ, i_G(σ) = v_L(σx − x)` (`exists_generator_lowerIndex_eq_addVal`) — zero named
hypotheses left in the `i_G` theory. Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom`
declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 55 — begin Serre IV §1
Prop. 3** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-54 entry), `ROADMAP.md`
(status header says Pass 54), and the **tail of `NOTES.md`** (Passes 50–54: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## Where the mathematics stands

**Closed strata:** descent (P29–37); assembly (P38–41, `IsNonarchimedeanLocalField L` for
finite separable `L/K`); canonicity (P43 — intermediate fields are legitimate base fields, so
`𝒪_{K'}`-based statements are available); Herbrand analytic theory (P44–49).

**The quotient arc (P50–54), files and key names:**
- `RamificationQuotient.lean` (P50): `decompositionQuotient`, `decompositionQuotient_ker`,
  `comapRingHom` + `mem_maximalIdeal_of_comapRingHom`, `ramificationGroup_zero_map_le`.
- `RamificationIndex.lean` (P51): `lowerIndex`, `mem_ramificationGroup_iff_lt_lowerIndex`,
  calculus (`_inv`, `_conj`, `min_…_le_…_mul`, `_eq_top_iff`),
  `lowerIndex_decompositionRestrict` (`rfl`); `ℕ∞` cofinality helpers.
- `RamificationQuotientSurjective.lean` (P52): `smul_extensionIntegers`,
  `decompositionSubgroup_extensionIntegers_eq_top`, `decompositionQuotient_surjective`,
  `decompositionQuotientEquiv` (+ `_extensionIntegers`).
- `RamificationIndexGenerator.lean` (P53): `mem_maximalIdeal_pow_iff_le_addVal` (DVR bridge),
  `forall_smul_sub_mem_iff_generator`, `mem_ramificationGroup_iff_smul_generator_sub_mem`,
  `lowerIndex_eq_addVal` (+ `_extensionIntegers_`).
- `ExtensionMonogenicDischarge.lean` (P54): `exists_pow_one_add_eq` (binomial tail),
  `maximalIdeal_eq_span_of_mem_of_notMem_sq` (DVR brick: `𝔪 ∖ 𝔪²` spans),
  `closure_union_singleton_eq_top`, **`exists_generator_extensionIntegers`** (monogenicity),
  **`exists_generator_lowerIndex_eq_addVal`** (unconditional concrete `i_G`).
- Feeding bricks: P25 `TameInjectivity.lean` (`smul_sub_dvd_of_mem_closure` — telescoping
  divisibility, works for ANY ring generator), P32 engine
  (`closure_subring_union_uniformizer_eq_top`), P33 `exists_pow_maximalIdeal_le_map`, P35
  uniformizer/DVR package, P36 residue finiteness.

## YOUR FIRST TASK — Pass 55: begin Serre IV §1 Prop. 3 (the sum formula)

**Goal (multi-pass):** `i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` — equivalently (Serre's
actual proof object, better for formalizing):

> `addVal (σ̄y − y)`-side: compare `a := σ̄y − y` and `b := ∏_{s ↦ σ̄} (s x − x)` where `y`
> generates `𝒪_{K'}/𝒪_K` and `x` generates `𝒪_L/𝒪_{K'}` — prove `a ∣ b` and `b ∣ a` in
> `𝒪_L`, then take `addVal`. (`e' · i_{K'/K}(σ̄) = Σ_s i_{L/K}(s)` is the `addVal` of the
> two-way divisibility; the `1/e'` form is bookkeeping.)

**Available inputs:** both generators are now theorems — `y` from P54 at `(K, K')`; `x` from
P54 at `(K', L)` (legitimate: `K'` is a local field by the P38–41 assembly + P43 canonicity —
check what instance form `IsNonarchimedeanLocalField K'` takes in
`ExtensionLocalFieldInstance.lean` before writing). The lifts of `σ̄` exist (P52); `i_H = i_G`
(P51); the coset structure `ker = range (decompositionRestrict)` (P50) describes the lift set
as `s₀·H`.

**Scope the FIRST brick.** Candidates, roughly in order:
- **(a) `b ∣ a`** (Serre's easier direction): `a = σ̄y − y` with `y ∈ 𝒪_{K'}`; write `y` as a
  polynomial in `x` over `𝒪_K`… — actually Serre does `a ∣ b` via norm/product arguments and
  `b ∣ a` via `b = ±N(σx' − x')`-type identities; **read Serre IV §1 Prop. 3's proof carefully
  first** and pick the direction with the shorter Mathlib path. P25's telescoping
  (`smul_sub_dvd_of_mem_closure`) is the divisibility workhorse for anything of the form
  "`τz − z` divisible by `τw − w` when `z ∈ 𝒪[w]`".
- **(b) The lift-set description**: `{s ∈ D(A) | decompositionQuotient s = σ̄} = s₀ • range
  (decompositionRestrict)` as a coset (from P50 exactness + P52 surjectivity) + finiteness +
  the product `∏_{s ∈ coset}` well-defined — the combinatorial substrate for `b`. A clean,
  purely group-theoretic pass if (a) looks too big.
- Do NOT attempt the full Prop. 3 in one pass; clean partial > half-discharge.

**Method (the P43–54 rhythm):** inventory first (P53 found its engine already built; P54's
route avoided minpoly entirely because the inventory showed finite-residue tools were
stronger); `lake env lean` probes; every Mathlib name source-grepped; `lake build
Anabelian.<File>`; scope tightly.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- `ℕ∞` numerals vs casts: state `have`s with explicit `((k:ℕ):ℕ∞)` and use `.mp`/`.mpr`
  term-style; `rw` on numeral forms fails (bit P54).
- `residue` vs `Ideal.Quotient.mk` is defeq but NOT syntactic — route through a
  `have : residue … = …` and apply `Ideal.Quotient.eq_zero_iff_mem.mp` term-style (bit P54).
- Prefer the `Nat.card` API (`pow_card_eq_one'`, `Nat.card_units` — `α` **explicit**,
  `Nat.card_pos`) over `Fintype.card` (instance clashes with `Fintype.ofFinite`) (bit P54).
- P25's closure lemmas take `A` implicitly (`smul_sub_dvd_of_mem_closure K hfix hx`).
- Unused section variables trip the warning gate — narrow `variable` blocks (P52).
- `push Not` (not `push_neg`, P51); `_root_.mem_nonunits_iff` under `ValuationSubring` opens
  (P50); `calc` + `AlgEquiv.restrictNormal_commutes` across the `restrictNormalHom` defeq
  (P50).
- `ℕ∞`/DVR toolkit: `lt_biSup_iff`/`le_biSup`, `ENat.eq_top_iff_forall_gt`/`add_one_le_iff`,
  P51 cofinality lemmas, P53 `mem_maximalIdeal_pow_iff_le_addVal`, P54
  `maximalIdeal_eq_span_of_mem_of_notMem_sq`.
- D2 (spectral bridge) lives entirely inside proofs via `letI` — P52–54 consumed only
  `IsIntegral`-level API; keep it that way.

## The queue after Pass 55

Finish **Prop. 3** (both divisibilities + the `addVal` bookkeeping) → IV §3 **Lemma 5**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit `G^v ≤ Gal(K̄/K)`. Optional deepening:
`ψ` closed form / `φ` concavity. The **R1-floor** stays ROADMAP-permitted but **deferred**.
R1–R3 remain distant targets that must be earned, never axiomatized — the line between inputs
and targets is drawn in `ROADMAP.md` and is the project's reason for existing.
