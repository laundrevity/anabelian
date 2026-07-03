# HANDOFF.md — session bootstrap (written after Pass 50, 2026-07-02)

**State:** Passes 44–49 built the full Herbrand `φ`/`ψ` **analytic theory** (Serre IV §§1, 3, all
absent from Mathlib, all axiom-free); **Pass 50 opened the quotient-ramification theory** with its
group-theoretic skeleton (`Anabelian/RamificationQuotient.lean`): the **quotient restriction**
`decompositionQuotient : D(A) →* D(A ∩ K')` along `Gal(L/K) ↠ Gal(K'/K)` (`K'/K` normal),
**exactness at the decomposition level** `ker (decompositionQuotient) =
range (decompositionRestrict)` (the P46 map), and **inertia preservation** `G_0(L/K) → G_0(K'/K)`
(the `i = 0`, renumbering-free base case of Serre Lemma 5). Ledger is **`0 FOUNDATIONAL /
0 DEBT`**, zero `axiom` declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass
51 — begin the ramification arithmetic of the quotient** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree, **governance
consistency**), `AXIOM_LEDGER.md` (state + tail Pass-50 entry), `ROADMAP.md` (status header says
Pass 50), and the **tail of `NOTES.md`** (Passes 43–50: canonicity, the Herbrand analytic theory,
the quotient skeleton).
**Session start:** `git status` — the tree must be clean. `.claude/` and `claude.last` are
`.gitignore`d, so a clean tree shows **nothing** untracked; `scripts/preflight.sh` clause 0
*enforces* this (it fails on any untracked file outside `.gitignore`). If anything is untracked,
resolve it before new work (`CLAUDE.md` clean-tree rule).

## Where the mathematics stands

**Descent closed and harvested** (P29–37): `ker θ₀ = G₁` unconditionally for every finite separable
`L/K`; the quotient theory concrete at `𝒪_L`. **Assembly COMPLETE** (P38–41):
`IsNonarchimedeanLocalField L` for every finite separable `L/K`. **Canonicity DISCHARGED** (P43):
`extensionValuativeRel` is base-independent across towers — intermediate fields usable as base
fields.

**The ascent, rungs 1–7 built** (P44–50): the Herbrand function `φ`
(`Anabelian/HerbrandFunction.lean`, strictly monotone, continuous), its inverse `ψ` + the **upper
numbering** `G^v = G_{⌈ψ(v)⌉}` (`Anabelian/UpperNumbering.lean`), subgroup compatibility
`H_u = H ∩ G_u` (`Anabelian/RamificationSubgroup.lean`, P46, with `decompositionRestrict :
Gal(L/K') →* Gal(L/K)` — action agreement `rfl`), slope `φ'(u) = 1/(G_0:G_u)`
(`Anabelian/HerbrandSlope.lean`), `φ`'s piecewise-linear closed form
(`Anabelian/HerbrandFormula.lean`), `ψ` slope `ψ'(v) = (G_0:G_{ψ(v)})`
(`Anabelian/HerbrandPsiSlope.lean`), and now the **quotient skeleton**
(`Anabelian/RamificationQuotient.lean`, P50): for `K ⊆ K' ⊆ L` with `[Normal K K']` and
`A ∩ K' := A.comap (algebraMap K' L)` (= `𝒪_{K'}` at `A = 𝒪_L`, unambiguous by P43) —
`decompositionQuotient` (via Mathlib's `AlgEquiv.restrictNormalHom`; action compatibility is
`restrictNormal_commutes`, NOT `rfl` — the quotient direction changes the field),
`decompositionQuotient_ker` (exactness), `comapRingHom : A ∩ K' →+* A` +
`mem_maximalIdeal_of_comapRingHom` (the inclusion reflects `𝔪`), and
`decompositionQuotient_mem_ramificationGroup_zero` / `ramificationGroup_zero_map_le` /
`inertiaSubgroup_map_le` (inertia → inertia). All axiom-free.

## YOUR FIRST TASK — Pass 51: the ramification arithmetic of the quotient

**Goal (multi-pass):** Serre IV §3 **Lemma 5** `(G/H)_{φ_{L/K'}(u)} = G_u H/H`, feeding
**`φ`-transitivity** `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` (Prop. 15) and **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14). The skeleton (P50) is done; what remains is the **arithmetic
core**: how `i_{K'/K}(σ̄)` relates to the `i_{L/K}` of the lifts of `σ̄` (Serre IV §1 Prop. 3 /
§3 Lemma 5's proof engine).

**Scope the FIRST brick, complete and axiom-free** — the natural candidate: the function
`i_G(σ) = min over generators / inf_a v(σa − a)` as a project object. Serre defines
`i_G(σ) = v_L(σx − x)` for a generator `x` of `𝒪_L` over `𝒪_K` (monogenicity — the project has
`ExtensionMonogenic*` files from the descent arc; check what P29–37 already provide) and proves
`σ ∈ G_u ⇔ i_G(σ) ≥ u + 1`. A clean Pass-51 deliverable: define `i` (e.g. as the sup/min of the
`𝔪`-adic valuations of `σa − a`, or via the existing monogenic generator), prove the membership
equivalence with `ramificationGroup`, and its behavior under the P46 restriction (`i_H = i_G` on
`H` — Serre IV §1 Prop. 2's second half, which P46 didn't need). Do NOT half-build Lemma 5's sum
formula (`i_{K'/K}(σ̄) = (1/e') Σ_{lifts} i_{L/K}(s)` — Serre IV §1 Prop. 3 is where the real
arithmetic lives; it can be its own pass). **Alternatively:** surjectivity of
`decompositionQuotient` at the finite/local level, or the last clean `φ`/`ψ` deepening (the `ψ`
closed form; concavity needs a from-scratch piecewise argument).

**Method (the P43–50 rhythm):** local toolchain **in the loop** — `lake build Anabelian.<File>`
(≈3 s incremental) for the real build, `lake env lean <scratch>.lean` for throwaway probes of
defeqs/instances/lemma names before committing. Scope tightly; one rung. P50's probe compiled with
only three mechanical fixes because every Mathlib name was source-grepped first — keep that
discipline.

## Environment (verify, then trust)

- **Toolchain in-loop (preferred):** host `lean`/`lake` (v4.30.0) directly usable.
  `lake build Anabelian.<File>` is the real build; `lake env lean <scratch>.lean` runs a throwaway
  probe with full `LEAN_PATH` (import the project modules you need, `#print axioms`/`example`/
  `#synth` to settle defeqs, instances, lemma names before editing the project file). Keep probe
  files in the scratchpad (outside the repo, so clause 0 stays clean). If sandboxed, the
  detached-probe-env recipe (NOTES P36) is the fallback.
- **Workflow**: source-grep Mathlib for every name BEFORE writing; probe substantive proofs with
  `lake env lean`; then `lake build` the project file; expect the new file + the root
  `Anabelian.lean` edit only.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, long lines (≤100 chars),
  named statement-level `letI`/`haveI` binders, import-chain completeness
  (`scripts/chain_check.py`), and a warning-free `lake build`. Committable only if it exits 0.
- **`scripts/refactor.sh`** (tracked, P42, **not yet run**): a one-shot flat→folders restructure.
  Belongs in its own dedicated pass; do not fold it into a math commit.

## House idioms (recent vintage; older ones in NOTES P25–41)

- `ValuationSubring` opens shadow `mem_nonunits_iff` — use `_root_.mem_nonunits_iff` for the
  local-ring one (bit P50).
- `rw` fails across the `restrictNormalHom`/`restrictNormal` defeq (a `MonoidHom.mk'` wrapper) —
  use `calc`/`exact` with the underlying `AlgEquiv.restrictNormal_commutes` (bit P50).
- A `variable` not mentioned in a declaration is not auto-bound — `comapRingHom` takes `K' A`,
  not `K K' A` (bit P50).
- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake linter; probes can't catch
  lake-level linters — only elaboration).
- D2 (the spectral/normed bridge) lives **entirely inside proofs** via `letI` — none in any
  statement, so `#print axioms` stays standard-only. Keep it that way.

## The queue after Pass 51

Continue the quotient arithmetic → Serre IV §1 Prop. 3 (the `i_{K'/K}` sum formula) → Lemma 5 →
`φ`-transitivity + **Herbrand's theorem** `(G/H)^v = G^v H/H`, then Hasse–Arf and the limit
`G^v ≤ Gal(K̄/K)` (Serre IV §3); surjectivity of `decompositionQuotient` and the `ψ` closed
form/concavity remain as parallel options. Separately, the **R1-floor** (axiomatizing L3 local
class field theory for a *conditional* R1 result) is ROADMAP-permitted but **deferred** — if
taken, it must be a deliberate, ledgered decision (A1/A2 preserved in the NOTES Pass-42 entry)
with an explicit rule-5 argument. R1–R3 remain distant targets that must be earned, never
axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the project's
reason for existing.
