# HANDOFF.md — session bootstrap (written after Pass 53, 2026-07-03)

**State:** the **quotient arc is 4 bricks in** (P50–53), on the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: the skeleton (`decompositionQuotient`, exactness
`ker = range`, inertia preservation). P51: the currency (Serre's `i_G` as
`lowerIndex K A σ : ℕ∞`, Lemma 1 `σ ∈ G_i ↔ i < i_G(σ)`, calculus, `i_H = i_G` by `rfl`).
P52: surjectivity (`𝒪_L` Galois-stable ⟹ `D(𝒪_L) = ⊤` ⟹ `decompositionQuotient` surjective ⟹
`D(A) ⧸ H ≃* D(A ∩ K')`). **P53: the concrete `i_G`**
(`Anabelian/RamificationIndexGenerator.lean`): the one-generator collapse
`(∀ a, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n` (P25's telescoping engine upgraded to an iff), Lemma 1
in generator form, and **`lowerIndex K A σ = addVal (σ • x − x)` = `v_L(σx − x)`**
(`lowerIndex_eq_addVal`, via the new DVR bridge `mem_maximalIdeal_pow_iff_le_addVal`) — under
the monogenicity package as **named binders** (`hfix` free at `𝒪_L` by P32's
`smul_extensionAlgebraMap_range_eq`; `hgen` = classical monogenicity, an honest named
hypothesis, NOT discharged, NOT axiomatized). Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero
`axiom` declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 54 — discharge
`hgen` (recommended) or start Prop. 3** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution), `AXIOM_LEDGER.md` (state + tail Pass-53 entry), `ROADMAP.md`
(status header says Pass 53), and the **tail of `NOTES.md`** (Passes 50–53: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this.

## Where the mathematics stands

**Closed strata:** descent (P29–37); assembly (P38–41, `IsNonarchimedeanLocalField L`);
canonicity (P43); Herbrand analytic theory (P44–49: `φ`/`ψ` complete, upper numbering,
`H_u = H ∩ G_u`).

**The quotient arc (P50–53), files and key names:**
- `RamificationQuotient.lean` (P50): `decompositionQuotient`, `decompositionQuotient_ker`,
  `comapRingHom` + `mem_maximalIdeal_of_comapRingHom`, `ramificationGroup_zero_map_le`.
- `RamificationIndex.lean` (P51): `lowerIndex`, `mem_ramificationGroup_iff_lt_lowerIndex`
  (+ `_add_one_le_`), `lowerIndex_one/_eq_top_iff/_inv/_conj`,
  `min_lowerIndex_le_lowerIndex_mul`, `lowerIndex_decompositionRestrict` (`rfl`); `ℕ∞`
  cofinality helpers `enat_le_of_forall_natCast_lt` / `enat_eq_of_forall_natCast_lt_iff`.
- `RamificationQuotientSurjective.lean` (P52): `smul_extensionIntegers`,
  `decompositionSubgroup_extensionIntegers_eq_top`, `decompositionQuotient_surjective`,
  `decompositionRestrict_range_normal`, `decompositionQuotientEquiv` (+ `_extensionIntegers`).
- `RamificationIndexGenerator.lean` (P53): `mem_maximalIdeal_pow_iff_le_addVal` (DVR bridge),
  `forall_smul_sub_mem_iff_generator`, `mem_ramificationGroup_iff_smul_generator_sub_mem`,
  `lowerIndex_eq_addVal`, `lowerIndex_extensionIntegers_eq_addVal` (only `hgen` left as a
  binder).
- Older bricks that fed P53: P25 `TameInjectivity.lean` (`smul_sub_dvd_of_mem_closure` — the
  telescoping engine; its `π` is ANY ring generator, no `hspan` needed), P32
  `ExtensionMonogenic.lean` (`smul_extensionAlgebraMap_range_eq` = `hfix` free), P35
  `ExtensionUniformizer.lean` (DVR instance + uniformizer package), P36 residue finiteness.

## YOUR FIRST TASK — Pass 54: discharge `hgen` (recommended), or start Prop. 3

**(a) RECOMMENDED — discharge `hgen`** (Serre III §6 Prop. 12, specialized to our setting):
`𝒪_L = 𝒪_K[x]` for finite separable `L/K` over a nonarchimedean local field — i.e.
`∃ x, Subring.closure (↑(extensionAlgebraMap K L).range ∪ {x}) = ⊤`. This would convert P53's
conditional statements into **unconditional** ones at `𝒪_L` and remove the last named
hypothesis from the `i_G` theory. Ingredients in-project: residue fields are **finite** (P36
arc — check `ExtensionResidueFinite.lean` for the exact statements), so `𝓀_L = 𝓀_K(x̄)` for
some `x̄` (`𝓀_L^×` cyclic — Mathlib finite-field API); the P32–34 engine
(`closure_subring_union_uniformizer_eq_top` in `ExtensionMonogenicGeneral.lean`) reduces
generation to "residues covered + a uniformizer in the subring"; Serre's trick: if the lift `x`
of a residue generator has `v(f(x)) = 1` (`f` = a monic lift of `x̄`'s minimal polynomial) take
`π := f(x) ∈ 𝒪_K[x]`, else replace `x` by `x + π` — the case analysis is the real work. Check
first what `ExtensionMonogenicGeneral`/`ExtensionMonogenicTop` already give (the engine is
stated for a general subring `A₀ ⊇ base image`; `A₀ := Subring.closure (base ∪ {x})` is the
intended instantiation). If the full Prop. 12 turns out multi-pass, a clean partial —
e.g. the unramified case (`e = 1`: residue generator lift alone generates) — is a complete
pass; do NOT half-build the general case.

**(b) Prop. 3** (`i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)`, Serre IV §1): the proof
compares `σ̄y − y` (`y` generating `𝒪_{K'}` over `𝒪_K`) with `∏_{s ↦ σ̄} (sx − x)` (`x`
generating `𝒪_L` over `𝒪_{K'}`) by divisibility both ways, then takes `addVal`. Multi-pass;
if taken, scope ONE divisibility direction. Note it needs `x` generating over `𝒪_{K'}` — the
tower-level monogenicity — so (a) helps here too (P43 canonicity makes `𝒪_{K'}` a legitimate
base).

**Method (the P43–53 rhythm):** inventory first (P53's inventory found the engine already
built — repeat that); `lake env lean <scratch>.lean` probes before touching the tree; every
Mathlib name source-grepped first; `lake build Anabelian.<File>` (≈3 s incremental); scope
tightly; one rung.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). Sandboxed fallback: NOTES P36 recipe.
- **Workflow**: source-grep Mathlib names BEFORE writing; probe; `lake build`; expect the new
  file + the root `Anabelian.lean` edit only.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free build.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders; its own pass only.

## House idioms (recent vintage; older in NOTES P25–41)

- P25's closure lemmas take `A` implicitly — `smul_sub_dvd_of_mem_closure K hfix hx`,
  `mem_ramificationGroup_of_smul_uniformizer_sub_mem K hgen hfix h` (bit P53's probe once).
- Unused section variables trip the warning gate — narrow `variable` blocks (bit P52).
- `push_neg` deprecated — `push Not` (P51). `_root_.mem_nonunits_iff` under
  `ValuationSubring` opens (P50). `rw` fails across `restrictNormalHom`/`restrictNormal` —
  use `calc` + `AlgEquiv.restrictNormal_commutes` (P50).
- `ℕ∞`: `lt_biSup_iff`/`le_biSup`, `ENat.eq_top_iff_forall_gt`/`ENat.add_one_le_iff`, the P51
  cofinality lemmas, and now P53's `mem_maximalIdeal_pow_iff_le_addVal` for DVR order counts.
- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake-level linter).
- D2 (spectral bridge) lives entirely inside proofs via `letI`; P52/P53 consumed only
  `IsIntegral`-level API — keep it that way.

## The queue after Pass 54

Whichever of (a)/(b) wasn't taken → **Prop. 3** complete → IV §3 **Lemma 5**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit `G^v ≤ Gal(K̄/K)`. Optional deepening:
`ψ` closed form / `φ` concavity. The **R1-floor** stays ROADMAP-permitted but **deferred**.
R1–R3 remain distant targets that must be earned, never axiomatized — the line between inputs
and targets is drawn in `ROADMAP.md` and is the project's reason for existing.
