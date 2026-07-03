# HANDOFF.md — session bootstrap (written after Pass 59, 2026-07-03)

**State:** the **quotient arc is 10 bricks in** (P50–59), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: skeleton. P51: `i_G`. P52: surjectivity. P53–54: concrete
`i_G`, unconditional. P55: Serre's polynomial + descent. P56: the lift-set identity. P57:
`𝒪_L ∩ K' = 𝒪_{K'}` + telescoping + `i_{K'/K}(σ̄) = addVal_B(σ̄y − y)`. P58: **direction
(i) `a ∣ b` PROVED**. **P59: the `addVal` bookkeeping**
(`Anabelian/RamificationAddVal.lean`): the **`e'`-dilation**
`addVal_A (ι c) = addVal_B c · addVal_A (ι π_B)` (behind it `isUnit_comapRingHom_iff` — units
transfer both ways along `ι`), the **fiber sum**
`addVal (∏_h (x − (s₀·dr h)·x)) = Σ_h lowerIndex K 𝒪_L (s₀·dr h)`, and generic
`addVal_neg`/`addVal_prod`. **Both sides of Prop. 3's sum formula are `addVal`-readable; the
only gaps left are direction (ii) (`b ∣ a`) and the assembly.** Ledger is **`0 FOUNDATIONAL /
0 DEBT`**, zero `axiom` declarations project-wide — keep it that way. **YOUR FIRST TASK is
Pass 60 — the polynomial-representation brick** (below). **Build caution:**
`RamificationLiftDvd.lean` (P58) elaborates slowly (~15 min) — put new bricks in fresh files
(P59 did: 2.8 s).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-59 entry), `ROADMAP.md`
(status header says Pass 59), and the **tail of `NOTES.md`** (Passes 50–59: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## The Prop. 3 endgame (Serre IV §1)

**Target:** for `σ̄ ≠ 1` in `D(B)`: `Associated (ι(σ̄y − y)) (∏_{s ↦ σ̄} (s·x − x))` in
`𝒪_L`, then `addVal` both sides:
`addVal_L (ι a) = addVal_B a · e'` (P59 dilation) `= i_{K'/K}(σ̄) · e'` (P57(3));
`addVal_L b = Σ_h i_{L/K}(s₀·dr h)` (P59 fiber sum) — giving
**`e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)`** (Prop. 3; the `∏(x − s·x)` vs `∏(s·x − x)`
sign is `(−1)^{|H|}`, a unit — `Associated` absorbs it, or use `addVal_neg`/`addVal_prod`
directly). Status: **(i) `a ∣ b` DONE (P58); bookkeeping DONE (P59).** Remaining:

- **(1) The polynomial-representation brick (PASS 60)**: every element of
  `Subring.closure ((f.range : Set S) ∪ {x})` (for `f : R →+* S`) is `(P.map f).eval x` for
  some `P : Polynomial R` — by `Subring.closure_induction` (constants: `C`; `x`: `X`; closed
  under `+`, `−`, `*`). Purely generic — state it for any ring hom; then at `𝒪_L`:
  `y`'s image `ι y ∈ 𝒪_L = 𝒪_K[x]` (P54) is `(g.map (extensionAlgebraMap K L)).eval x`.
- **(2) Direction (ii) `b ∣ a`**: `G := (image of g in B[X]) − C y` kills… — Serre: divide
  `G` by P55's monic `F` in `B[X]` (`Polynomial.modByMonic`/`divByMonic`,
  `modByMonic_add_div`), remainder `r` has degree `< natDegree F = |H|` (P55) and its
  `ι`-image kills `x` (since `(G.map ι).eval x = g(x) − ι y = 0` and `(F·q).map ι` kills `x`
  via `f(x) = 0`) — so `r`'s image vanishes at `x`; `K'`-independence of `1, x, …, x^{d−1}`
  (`d = [L:K']`, from `L = K'(x)` ⟸ `𝒪_L = 𝒪_K[x]` — extract via
  `IntermediateField.adjoin`/`Algebra.adjoin` or a power-basis argument; **this
  independence sub-brick may be its own pass**) forces `r`'s image `= 0`… careful: `r` has
  `B`-coefficients; its image killing `x` with degree `< d` forces all coefficients zero.
  Then transport `G = F·q + r` along `σ̄` (all coefficients in `B`), map along `ι`, evaluate
  at `x`: `g(x) − ι(σ̄y) = (σ̄f)(x)·((σ̄q).map ι).eval x`, LHS `= ι y − ι (σ̄y) = −ι(a)`,
  `(σ̄f)(x) = ±b` (P56) ⟹ `b ∣ ι(a)`.
- **(3) The assembly**: `associated_of_dvd_dvd` + the `addVal` readings ⟹ Prop. 3. (May
  fold into (2)'s pass if short, else its own.)

**Key names:** P50 `RamificationQuotient.lean` (`comapRingHom`,
`algebraMap_decompositionQuotient_smul`); P53 `RamificationIndexGenerator.lean`
(`mem_maximalIdeal_pow_iff_le_addVal`, `lowerIndex_eq_addVal`); P54
`ExtensionMonogenicDischarge.lean` (`exists_generator_extensionIntegers`); P55
`SubextensionCharPoly.lean` (`fullProdXSubSMul*` incl. `_natDegree`,
`exists_fullProdXSubSMul_lift*` — `F` monic + degree); P56 `RamificationLiftSet.lean`
(`map_fullProdXSubSMul(_eval)`, `decompositionFiberEquiv`); P57
`ExtensionComapIntegers.lean` (`extensionIntegers_comap_eq`, `comapIntegersEquiv`,
DVR-on-`B`, `baseToComapRingHom`, `exists_generator_comap_spec`); P58
`RamificationLiftDvd.lean` (`dvd_eval_of_dvd_coeff`, `map_comapRingHom_smul`,
`comapRingHom_smul_sub_dvd_liftProd`, `exists_generator_dvd_liftProd`); P59
`RamificationAddVal.lean` (`addVal_neg`, `addVal_prod`, `isUnit_comapRingHom_iff`,
`addVal_comapRingHom`, `addVal_liftProd`); P25 `TameInjectivity.lean`
(`smul_sub_dvd_of_mem_closure`).

## YOUR FIRST TASK — Pass 60: the polynomial-representation brick

> `theorem exists_polynomial_eval_of_mem_closure {R S} [CommRing R] [CommRing S]
> (f : R →+* S) {x z : S} (hz : z ∈ Subring.closure ((f.range : Set S) ∪ {x})) :
> ∃ P : Polynomial R, (P.map f).eval x = z`

by `Subring.closure_induction` (mirror P25's engine structure: mem-cases `C r`/`X`; `0`/`1`;
`add`/`neg`/`mul` via `map_add` etc. of eval∘map). Instantiate at `𝒪_L`: from P54's
generator, `∀ z : ↥𝒪_L, ∃ g : Polynomial ↥𝒪[K], (g.map (extensionAlgebraMap K L)).eval x
= z` — in particular for `z := comapRingHom … y`. If short, begin (2)'s division setup in
the same pass — but do NOT half-build the independence sub-brick; clean partial >
half-discharge.

**Method (the P43–59 rhythm):** inventory first; `lake env lean` probes; every Mathlib name
source-grepped; `lake build Anabelian.<File>`; fresh file.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- `rw [h]` substitutes everywhere and stales `have`s phrased pre-substitution — rewrite with
  the primitive lemma (`addVal_def' u hπ n`) instead of a stored `have` (bit P59).
- `Irreducible.not_isUnit` (not `.not_unit`) (P59). `ext` on polynomials over a subring
  descends to ambient coercions — wrap element lemmas in `congrArg Subtype.val` (P58).
- Coercion forms must match syntactically for `rw` (`⇑e.toRingHom` not `⇑↑e`); hand-rolled
  subtype equivs; structure fields by plain defeq application (P57).
- `show`→`change` (P56); orbit-vs-whole-`G` (P55); `𝒪[K]` is a `Subring` (P55); `ℕ∞` casts
  explicit; `residue` vs `mk`; `Nat.card` API; P25 lemmas take `A` implicitly; narrow
  `variable` blocks; `push Not`; `_root_.mem_nonunits_iff` (P50–54).
- DVR/`ℕ∞` toolkit: P51 cofinality, P53 bridge, P54 span-brick + binomial tail, P57 DVR-on-`B`,
  P59 `addVal_neg`/`addVal_prod`/dilation.
- D2 lives entirely inside proofs; P52–59 consumed only `IsIntegral`-level API.

## The queue after Pass 60

(2) direction (ii) (division + independence sub-brick) → (3) the **Prop. 3 assembly**
(`e'·i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)`) → IV §3 **Lemma 5** → **`φ`-transitivity**
(Prop. 15) + **Herbrand's theorem** (Prop. 14) → Hasse–Arf. Optional: `ψ` closed form / `φ`
concavity. The **R1-floor** stays deferred. R1–R3 remain distant targets that must be earned,
never axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
