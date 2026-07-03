# HANDOFF.md — session bootstrap (written after Pass 60, 2026-07-03)

**State:** the **quotient arc is 11 bricks in** (P50–60), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: skeleton. P51: `i_G`. P52: surjectivity. P53–54: concrete
`i_G`, unconditional. P55: Serre's polynomial + descent. P56: lift-set identity. P57:
`𝒪_L ∩ K' = 𝒪_{K'}` + telescoping + `i_{K'/K}(σ̄) = addVal_B(σ̄y − y)`. P58: **direction
(i) `a ∣ b` PROVED**. P59: **the `addVal` bookkeeping** (`e'`-dilation + fiber sum). **P60:
the representation + `L = K'(x)` layer** (`Anabelian/ExtensionGeneratorRep.lean`):
`exists_polynomial_map_eval_eq` (generic: closure membership IS polynomial representation;
at `𝒪_L`: `exists_polynomial_generator_rep` — every integer is
`(g.map (extensionAlgebraMap K L)).eval x`), the commuting square
`comapRingHom_comp_baseToComapRingHom` (`ι ∘ (𝒪_K → B) = extensionAlgebraMap K L`), and
**`adjoin_generator_eq_top`** (`IntermediateField.adjoin K' {(x:L)} = ⊤` for any
intermediate `K'`). Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations
project-wide — keep it that way. **YOUR FIRST TASK is Pass 61 — the remainder-vanishing
brick** (below). **Build caution:** `RamificationLiftDvd.lean` (P58) elaborates slowly
(~15 min) — put new bricks in fresh files (P59/P60 did: ~3 s each).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-60 entry), `ROADMAP.md`
(status header says Pass 60), and the **tail of `NOTES.md`** (Passes 50–60: the quotient
arc). **Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last`
are `.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## The Prop. 3 endgame (Serre IV §1)

**Target:** `Associated (ι(σ̄y − y)) (∏_{s ↦ σ̄} (s·x − x))` in `𝒪_L`, then `addVal`:
LHS `= i_{K'/K}(σ̄)·e'` (P59 dilation + P57(3)); RHS `= Σ_h i_{L/K}(s₀·dr h)` (P59 fiber
sum) ⟹ **`e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)`** (Prop. 3). Status: (i) `a ∣ b` DONE
(P58); bookkeeping DONE (P59); representation + `L = K'(x)` DONE (P60). Remaining:

- **(1) The remainder-vanishing brick (PASS 61)**: for `r : Polynomial ↥B` with
  `(r.map ι).eval x = 0` and `r.natDegree < Fintype.card (D_{K'}(𝒪_L))`: **`r = 0`**.
  Route: (a) `r_{K'} := r.map B.subtype` (or the subring inclusion hom into `K'`) — nonzero
  if `r ≠ 0` (`Polynomial.map_injective`, subtype injective); (b) `aeval (x:L) r_{K'} = 0` —
  value-level: the coercion `𝒪_L →+* L` (i.e. `(extensionIntegers K L).subtype`) applied to
  `(r.map ι).eval x`; chain `Polynomial.eval_map`/`Polynomial.hom_eval₂`/
  `Polynomial.eval₂_map` to reassociate the three homs `↥B → 𝒪_L → L` vs `↥B → K' → L`
  (they agree: `ι` then coe = `algebraMap K' L` then coe — `rfl`-level on values); (c)
  degree count: `minpoly K' (x:L)` has `natDegree = finrank K' K'⟮x⟯`
  (`IntermediateField.adjoin.finrank`, integrality from `FiniteDimensional K' L`)
  `= finrank K' L` (P60 `adjoin_generator_eq_top` — note `K'⟮x⟯ = ⊤` and
  `finrank of ⊤`: `IntermediateField.finrank_top`? check exact form; possibly easier via
  `(adjoin_generator_eq_top …) ▸`) `= Fintype.card (L ≃ₐ[K'] L)`
  (`IsGalois.card_aut_eq_finrank`, needs `[IsGalois K' L]`) `= Fintype.card (D_{K'}(𝒪_L))`
  (P55's `decompositionSubgroup_extensionIntegers_restrict_eq_top`; card of `⊤`-subgroup vs
  group — `Nat.card`/`Fintype.card` juggling, prefer `Nat.card`); (d)
  `minpoly.degree_le_of_ne_zero` (check exact signature/namespace) contradicts (b)+(c).
- **(2) The division + `b ∣ a` (Pass 62)**: `g` := P60's representation of `ι y`… careful:
  represent `comapRingHom … y` (in `𝒪_L`) as `(g.map (extensionAlgebraMap K L)).eval x`;
  move `g` to `B[X]` via `baseToComapRingHom` (the commuting square makes the two routes
  agree); `G := g_B − C y`; `(G.map ι).eval x = 0`; divide by P55's monic `F`
  (`Polynomial.modByMonic_add_div`), remainder kills `x` after `ι` (since `f(x) = 0`),
  degree `< natDegree F = |H|` (P55 `_natDegree` + `degree_modByMonic_lt`) ⟹ `r = 0` by
  (1); so `G = F·(G /ₘ F)`; apply the `σ̄`-action (coefficients in `B`), map along `ι`,
  evaluate at `x`: `g(x) − ι(σ̄y) = (σ̄f)(x)·(…)` (the LHS uses that `σ̄` fixes `g_B`'s
  base coefficients — P57's `smul_baseToComapRingHom_range_eq`-flavored fact at the
  polynomial level, cf. P58's `map_comapRingHom_smul`), LHS `= ι y − ι(σ̄y) = −ι(a)`,
  `(σ̄f)(x) = ∏ (x − (s₀·dr h)·x)` (P56) ⟹ `∏ ∣ ι(a)`.
- **(3) The assembly (Pass 63)**: `associated_of_dvd_dvd` (mind the `(−1)^{|H|}` sign
  between `∏(x − s·x)` and `∏(s·x − x)` — absorbable by `Associated`/`addVal_neg`-per-factor)
  + the `addVal` readings ⟹ Prop. 3.

**Key names:** P50 `RamificationQuotient.lean` (`comapRingHom`); P53
`RamificationIndexGenerator.lean` (bridge, `lowerIndex_eq_addVal`); P54
`ExtensionMonogenicDischarge.lean` (`exists_generator_extensionIntegers`); P55
`SubextensionCharPoly.lean` (`fullProdXSubSMul*` incl. `_natDegree` + `_eval`,
`exists_fullProdXSubSMul_lift*`, `decompositionSubgroup_extensionIntegers_restrict_eq_top`);
P56 `RamificationLiftSet.lean` (`map_fullProdXSubSMul(_eval)`); P57
`ExtensionComapIntegers.lean` (`extensionIntegers_comap_eq`, DVR-on-`B`,
`baseToComapRingHom`, `exists_generator_comap_spec`, `smul_baseToComapRingHom_range_eq`);
P58 `RamificationLiftDvd.lean` (`dvd_eval_of_dvd_coeff`, `map_comapRingHom_smul`,
`exists_generator_dvd_liftProd`); P59 `RamificationAddVal.lean` (`addVal_neg/_prod`,
`isUnit_comapRingHom_iff`, `addVal_comapRingHom`, `addVal_liftProd`); P60
`ExtensionGeneratorRep.lean` (`exists_polynomial_map_eval_eq`,
`comapRingHom_comp_baseToComapRingHom`, `exists_polynomial_generator_rep`,
`adjoin_generator_eq_top`).

## YOUR FIRST TASK — Pass 61: the remainder-vanishing brick

As specified in (1) above. Scope: the single theorem (with whatever small value-level
`eval₂`-reassociation lemmas it needs) + nothing else; it is the last genuinely new
mathematics before Prop. 3 (Pass 62 is gluing, Pass 63 is bookkeeping). Inventory the exact
Mathlib forms first: `minpoly.degree_le_of_ne_zero` vs `minpoly.natDegree_le`-family,
`IntermediateField.adjoin.finrank`, `IsGalois.card_aut_eq_finrank`, `finrank` of `⊤`
(`IntermediateField.finrank_top'`?), `Subgroup` card-of-top. Watch the `Fintype` vs
`Nat.card` idiom (P54).

**Method (the P43–60 rhythm):** inventory first; `lake env lean` probes **from the project
root** (never `cd` into the scratchpad — `lake env` loses the search path and elan may pull
a stray toolchain; bit P60); every Mathlib name source-grepped; fresh file.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- Probes run from the project root only (P60). `ExtensionComapIntegers` does NOT pull in
  `comapRingHom` — import `RamificationQuotient` explicitly when using it (P60).
- `rw [h]` stales pre-substitution `have`s — rewrite with primitive lemmas (P59).
  `Irreducible.not_isUnit` (P59). `congrArg Subtype.val` under polynomial `ext` (P58).
  Coercion forms must match syntactically; hand-rolled subtype equivs; plain defeq structure
  fields (P57). `show`→`change` (P56). `𝒪[K]` is a `Subring` (P55). `ℕ∞` casts explicit;
  `Nat.card` API; narrow `variable` blocks; `push Not` (P50–54).
- DVR/`ℕ∞` toolkit: P51 cofinality, P53 bridge, P54 span-brick + binomial tail, P57
  DVR-on-`B`, P59 `addVal_neg`/`addVal_prod`/dilation.
- D2 lives entirely inside proofs; P52–60 consumed only `IsIntegral`-level API.

## The queue after Pass 61

Pass 62: the division + `b ∣ a`. Pass 63: the **Prop. 3 assembly**
(`e'·i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)`). Then IV §3 **Lemma 5**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
(Prop. 14) → Hasse–Arf. Optional: `ψ` closed form / `φ` concavity. The **R1-floor** stays
deferred. R1–R3 remain distant targets that must be earned, never axiomatized — the line
between inputs and targets is drawn in `ROADMAP.md` and is the project's reason for
existing.
