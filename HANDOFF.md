# HANDOFF.md — session bootstrap (written after Pass 52, 2026-07-03)

**State:** the **quotient arc is 3 bricks in** (P50–52), on top of the complete Herbrand `φ`/`ψ`
analytic theory (P44–49). P50: the skeleton (`decompositionQuotient : D(A) →* D(A ∩ K')`,
exactness `ker = range (decompositionRestrict)`, inertia preservation). P51: the currency
(Serre's `i_G` as `lowerIndex K A σ : ℕ∞`, Lemma 1 `σ ∈ G_i ↔ i < i_G(σ)`, calculus,
`i_H = i_G` by `rfl`). **P52: surjectivity** (`Anabelian/RamificationQuotientSurjective.lean`):
`𝒪_L = extensionIntegers K L` is **Galois-stable** (it is the integral closure of `𝒪_K`;
`smul_extensionIntegers`), so **`D(𝒪_L) = ⊤`** and `decompositionQuotient` is **surjective**
(via `restrictNormalHom_surjective`), giving the first-isomorphism packaging
**`D(A) ⧸ range (decompositionRestrict) ≃* D(A ∩ K')`** (`decompositionQuotientEquiv`, range
normal because it is a kernel) — the `(G/H)` of Herbrand's theorem, realized. Ledger is
**`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations project-wide — keep it that way.
**YOUR FIRST TASK is Pass 53 — the concrete `i_G` via monogenicity** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree, **governance
consistency**), `AXIOM_LEDGER.md` (state + tail Pass-52 entry), `ROADMAP.md` (status header says
Pass 52), and the **tail of `NOTES.md`** (Passes 50–52: the quotient arc).
**Session start:** `git status` — the tree must be clean (`.claude/` and `claude.last` are
`.gitignore`d); `scripts/preflight.sh` clause 0 *enforces* this. If anything is untracked,
resolve it before new work.

## Where the mathematics stands

**Closed strata:** descent (P29–37, `ker θ₀ = G₁` unconditional, quotient theory concrete at
`𝒪_L`); assembly (P38–41, `IsNonarchimedeanLocalField L` for finite separable `L/K`); canonicity
(P43, intermediate fields as base fields); Herbrand analytic theory (P44–49: `φ`/`ψ` monotone,
continuous, both slopes, `φ` closed form; upper numbering `G^v = G_{⌈ψ(v)⌉}`; `H_u = H ∩ G_u`).

**The quotient arc (P50–52), files and key names:**
- `RamificationQuotient.lean` (P50): `decompositionQuotient` (via `AlgEquiv.restrictNormalHom`;
  action compatibility = `restrictNormal_commutes`, NOT `rfl`), `decompositionQuotient_ker`,
  `comapRingHom` + `mem_maximalIdeal_of_comapRingHom` (the inclusion `A ∩ K' →+* A` reflects
  `𝔪`), `ramificationGroup_zero_map_le` / `inertiaSubgroup_map_le`.
- `RamificationIndex.lean` (P51): `lowerIndex`, `mem_ramificationGroup_iff_lt_lowerIndex` (+
  `_add_one_le_` form), `lowerIndex_one/_eq_top_iff/_inv/_conj`,
  `min_lowerIndex_le_lowerIndex_mul`, `lowerIndex_decompositionRestrict` (`rfl`); `ℕ∞` helpers
  `enat_le_of_forall_natCast_lt` / `enat_eq_of_forall_natCast_lt_iff` (public, reusable).
- `RamificationQuotientSurjective.lean` (P52): `smul_extensionIntegers`,
  `decompositionSubgroup_extensionIntegers_eq_top`, `decompositionQuotient_surjective`
  (abstract, stability hypothesis), `decompositionRestrict_range_normal`,
  `decompositionQuotientEquiv` (+ `_extensionIntegers` instantiations).

## YOUR FIRST TASK — Pass 53: the concrete `i_G` (Serre's one-generator reduction)

**Goal (multi-pass, this is the next brick):** Serre IV §1 Prop. 3
`i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` — the arithmetic engine of Lemma 5 →
`φ`-transitivity → Herbrand. Its one remaining prerequisite is the **concrete `i_G`**:

> `i_G(σ) = v_L(σx − x)` for a generator `x` of `𝒪_L` over `𝒪_K` — equivalently, Serre's
> **one-generator reduction**: `(∀ a ∈ 𝒪_L, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n`.

The `←` direction is the content: any `a ∈ 𝒪_L` is a polynomial in `x` over `𝒪_K`, and
`σ(P(x)) − P(x)` is divisible by `σx − x` (a ring identity: `σ` fixes the coefficients, and
`σx^k − x^k = (σx − x)·(…)`). With P51's `lowerIndex` this becomes
`lowerIndex K A σ = (𝔪-adic order of σx − x)` — pick whatever order/valuation form the project
already has at `A = 𝒪_L`.

**First step: inventory.** Check what the `ExtensionMonogenic*` files (P29–37 descent arc)
actually provide — the generator statement's exact form (`Algebra.adjoin 𝒪_K {x} = ⊤`? a power
basis? for which `L/K`?) — and what `ExtensionRamificationData`/`ExtensionUniformizer` give as
the `𝔪`-adic order. Scope to the reduction lemma + the `lowerIndex` identification, complete
and axiom-free; do NOT start Prop. 3's sum. If the monogenic form is awkward, the reduction
`(∀ a, …) ↔ (σx − x ∈ 𝔪^n)` alone (no valuation form) is a complete pass.

**Method (the P43–52 rhythm):** `lake env lean <scratch>.lean` probes before touching the tree
(P51 and P52 probes compiled first try because every Mathlib name was source-grepped first);
`lake build Anabelian.<File>` (≈3 s incremental); probe files in the scratchpad.

## Environment (verify, then trust)

- **Toolchain in-loop:** host `lean`/`lake` (v4.30.0). If sandboxed, the detached-probe-env
  recipe (NOTES P36) is the fallback.
- **Workflow**: source-grep Mathlib for every name BEFORE writing; probe; `lake build`; expect
  the new file + the root `Anabelian.lean` edit only.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, ≤100-char lines, named
  statement-level `letI`/`haveI` binders, import-chain completeness, warning-free `lake build`.
- **`scripts/refactor.sh`** (P42, **not yet run**): flat→folders restructure; its own pass only.

## House idioms (recent vintage; older ones in NOTES P25–41)

- Unused section variables trip the warning gate — declare narrow `variable` blocks or use
  per-theorem binders (bit P52's probe).
- `push_neg` is deprecated — use `push Not` (bit P51).
- `ValuationSubring` opens shadow `mem_nonunits_iff` — `_root_.mem_nonunits_iff` (bit P50).
- `rw` fails across the `restrictNormalHom`/`restrictNormal` defeq — `calc`/`exact` with
  `AlgEquiv.restrictNormal_commutes` (bit P50).
- A `variable` not mentioned in a declaration is not auto-bound (`comapRingHom` takes `K' A`).
- `ℕ∞` sups: `lt_biSup_iff`/`le_biSup`, `ENat.eq_top_iff_forall_gt`/`ENat.add_one_le_iff`, and
  the P51 cofinality lemmas.
- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake-level linter).
- D2 (spectral/normed bridge) lives **entirely inside proofs** via `letI` — P52 confirmed the
  discipline holds (only the `IsIntegral` membership of `extensionIntegers` is consumed).

## The queue after Pass 53

**Prop. 3** (the sum formula — needs the concrete `i_G` from P53 + the lift analysis over
`decompositionQuotient`, lifts existing by P52) → IV §3 **Lemma 5**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity** (Prop. 15) + **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14) → Hasse–Arf, the limit `G^v ≤ Gal(K̄/K)`. Optional deepening: the
`ψ` closed form / `φ` concavity. The **R1-floor** stays ROADMAP-permitted but **deferred**
(deliberate, ledgered, rule-5-argued if ever taken). R1–R3 remain distant targets that must be
earned, never axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is
the project's reason for existing.
