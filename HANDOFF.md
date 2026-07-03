# HANDOFF.md — session bootstrap (written after Pass 58, 2026-07-03)

**State:** the **quotient arc is 9 bricks in** (P50–58), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: skeleton. P51: `i_G`. P52: surjectivity. P53–54: concrete
`i_G = v_L(σx − x)`, unconditional. P55: Serre's polynomial + descent. P56: the lift-set
identity. P57: `𝒪_L ∩ K' = 𝒪_{K'}` + telescoping + `i_{K'/K}(σ̄) = addVal_B(σ̄y − y)`.
**P58: Prop. 3 direction (i), PROVED** (`Anabelian/RamificationLiftDvd.lean`):
**`ι(σ̄y − y) ∣ ∏_{s ↦ σ̄} (x − s·x)` in `𝒪_L`** — the equivariance
`ι(σ̄ • c) = s₀ • ι(c)` (P50 packaged; polynomial level `(σ̄ • F).map ι = (F.map ι).map s₀`),
the generic `dvd_eval_of_dvd_coeff`, the abstract assembly
(`comapRingHom_smul_sub_dvd_liftProd`), and the hypothesis-free `𝒪_L` form
(`exists_generator_dvd_liftProd`: one `y` carrying BOTH the concrete `i_{K'/K}` and the
divisibility for every `x`, `s₀`). Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom`
declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 59 — direction (ii)
or the `addVal` bookkeeping** (below). **Build caution:** `RamificationLiftDvd.lean`
elaborates slowly (~15 min; instance-heavy instantiation) — clean, but budget for it; prefer
putting new Prop.-3 bricks in fresh files.

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-58 entry), `ROADMAP.md`
(status header says Pass 58), and the **tail of `NOTES.md`** (Passes 50–58: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## The Prop. 3 assembly map (Serre IV §1) — updated

**Target:** for `σ̄ ≠ 1` in `D(B)`: `ι(σ̄y − y)` and `b = ∏_{s ↦ σ̄} (s·x − x)` **associated**
in `𝒪_L`; then `addVal` + P57(3) + the `e'`-dilation give
`e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)`. Status: **(i) `a ∣ b` DONE (P58)** (note: P58's
product is `∏ (x − s·x)`; `b`'s sign convention `∏ (s·x − x)` differs by `(−1)^{|H|}` —
handle at assembly time via `Associated`/units or `dvd` symmetry `p ∣ q ↔ p ∣ −q`). Remaining:

- **(ii) `b ∣ a`**: `y`'s image in `𝒪_L` is a polynomial in `x` over `𝒪_K`'s image
  (from P54's `𝒪_L = 𝒪_K[x]` — extract a polynomial representation from
  `Subring.closure`-membership: an element of `closure (range ι₀ ∪ {x})` is `P.eval x` for
  some `P` over the base — this **representation brick** may itself be a pass: closure of
  `range ∪ {x}` = image of `Polynomial.eval x ∘ map` … check Mathlib `Algebra.adjoin`
  machinery: `Algebra.adjoin_singleton_eq_range_aeval` is the model, but over the subring
  base — consider recasting P54's statement via `Algebra.adjoin ↥𝒪[K] {x}`). Then Serre:
  `G := g − C y` over `B` kills `x` after `ι`… division by P55's monic `F` in `B[X]`,
  remainder vanishes (degree `< |H| = [L:K']` + `K'`-independence of powers of `x` — from
  `L = K'(x)`), transport the identity along `σ̄` (coefficients in `B`), map along `ι`,
  evaluate at `x`: `−ι(a) = (σ̄f)(x)·(…)`, so `b ∣ ι(a)`.
- **(iii) `addVal` bookkeeping**: `addVal_L` of the fiber product `= Σ_h i_{L/K}(s₀·dr h)`
  (P53–54's concrete `i_G` per factor + `addVal` multiplicativity `(addVal).map_mul` /
  `map_prod`); the **`e'`-dilation** `addVal_L (ι c) = e' · addVal_B c` with
  `e' := addVal_L (ι π_B)` — self-contained DVR brick (use P53's
  `mem_maximalIdeal_pow_iff_le_addVal` on both sides + P50's
  `mem_maximalIdeal_of_comapRingHom`); combine with P57(3).

**Key names:** P50 `RamificationQuotient.lean` (`comapRingHom`,
`algebraMap_decompositionQuotient_smul`, `mem_maximalIdeal_of_comapRingHom`); P51
`RamificationIndex.lean` (`lowerIndex`, Lemma-1 forms, `ℕ∞` cofinality); P53
`RamificationIndexGenerator.lean` (`mem_maximalIdeal_pow_iff_le_addVal`,
`lowerIndex_eq_addVal`); P54 `ExtensionMonogenicDischarge.lean`
(`exists_generator_extensionIntegers`, `maximalIdeal_eq_span_of_mem_of_notMem_sq`); P55
`SubextensionCharPoly.lean` (`fullProdXSubSMul*`, `exists_fullProdXSubSMul_lift*` — `F`
monic + degree!); P56 `RamificationLiftSet.lean` (`map_fullProdXSubSMul(_eval)`,
`decompositionFiberEquiv`); P57 `ExtensionComapIntegers.lean` (`extensionIntegers_comap_eq`,
`comapIntegersEquiv`, DVR-on-`B`, `baseToComapRingHom`, `exists_generator_comap_spec`); P58
`RamificationLiftDvd.lean` (`dvd_eval_of_dvd_coeff`, `comapRingHom_decompositionQuotient_smul`,
`map_comapRingHom_smul`, `comapRingHom_smul_sub_dvd_liftProd`,
`exists_generator_dvd_liftProd`); P25 `TameInjectivity.lean` (`smul_sub_dvd_of_mem_closure`).

## YOUR FIRST TASK — Pass 59: one brick

- **(A) The `e'`-dilation + fiber-sum bookkeeping** ((iii)) — RECOMMENDED first: it is
  self-contained DVR/`ℕ∞` arithmetic with no new representation machinery, and after it the
  only gap in Prop. 3 is (ii). Deliverables: `addVal_comapRingHom` (`addVal_L (ι c) = e' ·
  addVal_B c`, `e' := addVal_L (ι π_B)` — nonzero, finite) and `addVal_liftProd`
  (`addVal_L (∏_h (x − (s₀·dr h)·x)) = Σ_h lowerIndex K 𝒪_L (s₀·dr h)` via P53–54 per
  factor + `AddValuation`-of-product; mind `⊤` cases — cleanest for `σ̄ ≠ 1` where each
  factor is nonzero... actually factors can still vanish only if `s·x = x`; for a generator
  `x`, `s·x = x ⟹ s = 1` ⟹ fiber of `σ̄ ≠ 1` has no such `s` — that no-vanishing lemma
  needs `x` generating over `𝒪_K`, `s ≠ 1`: `s·x = x` + `s` fixes `𝒪_K`-image + generation
  ⟹ `s` fixes all of `𝒪_L` ⟹ `s = 1` — cf. P23's `iInf_ramificationGroup_eq_bot` ending).
- **(B) The polynomial-representation brick** (unblocks (ii)): every element of
  `Subring.closure (range ι₀ ∪ {x})` is `(P.map ι₀).eval x` for some `P : Polynomial ↥𝒪[K]`
  — by `Subring.closure_induction` (mirror P25's engine structure), or via an
  `Algebra.adjoin` recast. Self-contained.
- Do NOT attempt (ii) whole; clean partial > half-discharge.

**Method (the P43–58 rhythm):** inventory first; `lake env lean` probes; every Mathlib name
source-grepped; `lake build Anabelian.<File>`; scope tightly; fresh file per brick (see the
build caution).

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- `ext` on polynomials over a subring descends to ambient-field coercions — wrap element
  lemmas in `congrArg Subtype.val` (bit P58).
- `rw` needs syntactically matching coercion forms (`⇑e.toRingHom`, not `⇑↑e`); hand-rolled
  subtype equivs beat `subringCongr`; structure fields by plain defeq application (P57).
- Goal-changing `show` → `change` (P56). Orbit-vs-whole-`G` products (P55). `𝒪[K]` is a
  `Subring` (P55). `ℕ∞` casts explicit; `residue` vs `mk` defeq-not-syntactic; `Nat.card`
  API; P25 lemmas take `A` implicitly; narrow `variable` blocks; `push Not`;
  `_root_.mem_nonunits_iff` (P50–54).
- DVR/`ℕ∞` toolkit: P51 cofinality, P53 `mem_maximalIdeal_pow_iff_le_addVal`, P54
  `maximalIdeal_eq_span_of_mem_of_notMem_sq` + `exists_pow_one_add_eq`, P57 DVR-on-`B`.
- D2 lives entirely inside proofs; P52–58 consumed only `IsIntegral`-level API.

## The queue after Pass 59

The remaining Prop. 3 bricks ((ii)'s representation + division, (iii) if not taken), the
**Prop. 3 assembly** (`Associated` + the sum formula `e'·i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_G(s)`),
→ IV §3 **Lemma 5** `(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity** (Prop. 15) +
**Herbrand's theorem** (Prop. 14) → Hasse–Arf. Optional: `ψ` closed form / `φ` concavity.
The **R1-floor** stays deferred. R1–R3 remain distant targets that must be earned, never
axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
