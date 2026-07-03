# HANDOFF.md — session bootstrap (written after Pass 51, 2026-07-03)

**State:** Passes 44–49 built the full Herbrand `φ`/`ψ` **analytic theory**; **Pass 50 opened the
quotient-ramification theory** with its group-theoretic skeleton
(`Anabelian/RamificationQuotient.lean`: `decompositionQuotient : D(A) →* D(A ∩ K')`,
decomposition-level exactness `ker = range (decompositionRestrict)`, inertia preservation
`G_0 → G_0`); **Pass 51 minted its currency** (`Anabelian/RamificationIndex.lean`): **Serre's
`i_G`** as the generator-free `lowerIndex K A σ : ℕ∞ = sup {n | ∀ a ∈ A, σa − a ∈ 𝔪^n}`, with
**IV §1 Lemma 1** `σ ∈ G_i ↔ (i : ℕ∞) < i_G(σ)` (+ Serre's `i + 1 ≤` form), the calculus
(`i(σ⁻¹) = i(σ)`, `i(στ) ≥ min`, class function via normality, `i(1) = ⊤`, `= ⊤ ↔ σ = 1` under
Krull separation), and **`i_H = i_G` on `H`** (IV §1 Prop. 2's second half) — **by `rfl`**.
Ledger is **`0 FOUNDATIONAL / 0 DEBT`**, zero `axiom` declarations project-wide — keep it that
way. **YOUR FIRST TASK is Pass 52 — the concrete `i_G` or the lift analysis** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree, **governance
consistency**), `AXIOM_LEDGER.md` (state + tail Pass-51 entry), `ROADMAP.md` (status header says
Pass 51), and the **tail of `NOTES.md`** (Passes 44–51: the Herbrand analytic theory, the
quotient skeleton, `i_G`).
**Session start:** `git status` — the tree must be clean. `.claude/` and `claude.last` are
`.gitignore`d, so a clean tree shows **nothing** untracked; `scripts/preflight.sh` clause 0
*enforces* this. If anything is untracked, resolve it before new work (`CLAUDE.md` clean-tree
rule).

## Where the mathematics stands

**Descent closed** (P29–37): `ker θ₀ = G₁` unconditionally, quotient theory concrete at `𝒪_L`.
**Assembly COMPLETE** (P38–41): `IsNonarchimedeanLocalField L` for finite separable `L/K`.
**Canonicity DISCHARGED** (P43): intermediate fields usable as base fields. **Herbrand analytic
theory COMPLETE** (P44–49): `φ`/`ψ` monotone + continuous + both slopes + `φ`'s closed form;
upper numbering `G^v = G_{⌈ψ(v)⌉}`; subgroup compatibility `H_u = H ∩ G_u` (P46,
`decompositionRestrict`, action agreement `rfl`).

**The quotient arc, 2 bricks in** (P50–51):
- **P50 skeleton** (`RamificationQuotient.lean`): for `K ⊆ K' ⊆ L`, `[Normal K K']`,
  `A ∩ K' := A.comap (algebraMap K' L)` — `decompositionQuotient` (via
  `AlgEquiv.restrictNormalHom`; action compatibility is `restrictNormal_commutes`, NOT `rfl`),
  `decompositionQuotient_ker` (exactness), `comapRingHom` + `mem_maximalIdeal_of_comapRingHom`
  (the inclusion reflects `𝔪`), inertia preservation (`ramificationGroup_zero_map_le`,
  `inertiaSubgroup_map_le`).
- **P51 currency** (`RamificationIndex.lean`): `lowerIndex` + Lemma 1
  (`mem_ramificationGroup_iff_lt_lowerIndex` / `_add_one_le_`) + calculus + `i_H = i_G`
  (`lowerIndex_decompositionRestrict`, `rfl`). `ℕ∞` interface:
  `enat_le_of_forall_natCast_lt` / `enat_eq_of_forall_natCast_lt_iff` (public, reusable).

## YOUR FIRST TASK — Pass 52: toward Serre IV §1 Prop. 3 (the sum formula)

**Goal (multi-pass):** Prop. 3 `i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` — the arithmetic
engine of IV §3 Lemma 5 → `φ`-transitivity → Herbrand's theorem. Its prerequisites, either of
which is a clean Pass 52:

- **(a) The concrete `i_G`:** `i_G(σ) = v(σx − x)` for a monogenic generator `x` of
  `𝒪_L/𝒪_K` — the bridge between P51's sup and generator arithmetic. Check what the
  `ExtensionMonogenic*` files (descent arc, P29–37) already give: there is a
  power-basis/generator statement for `𝒪_L` over `𝒪_K` at the finite level; the lemma is
  `∀ a, σa − a ∈ 𝔪^n ↔ σx − x ∈ 𝔪^n` (Serre's one-generator reduction — uses that `σ` is a ring
  hom and `a` is a polynomial in `x`), then `lowerIndex = v(σx − x)` in whatever valuation
  normal form the project uses at `A = 𝒪_L` (the `ℕ∞`-valued `𝔪`-adic order; check
  `ExtensionRamificationData`/`ExtensionUniformizer` for what exists).
- **(b) Surjectivity of `decompositionQuotient`** at the finite/local level (the lifts of `σ̄`
  must exist for the sum to be over a nonempty set): Mathlib's `restrictNormalHom_surjective`
  gives a lift in `Gal(L/K)`; landing it in `D(A)` needs transitivity on the valuation subrings
  above a given one — at the local-field level `D` may be everything (check what the assembly
  P38–41 gives about uniqueness of the valuation on `L`; if the extension valuative structure is
  unique, every `σ` stabilizes `𝒪_L` and `D(A) = Gal(L/K)`, making surjectivity nearly free —
  probe `extensionValuativeRel`-uniqueness / P43 canonicity first, this may be a short pass).

Scope ONE of these, complete and axiom-free. Do NOT half-build the sum formula itself.

**Method (the P43–51 rhythm):** local toolchain **in the loop** — `lake build Anabelian.<File>`
(≈3 s incremental); `lake env lean <scratch>.lean` for probes (P50 compiled with three mechanical
fixes, P51 first-try, because every Mathlib name was source-grepped first). Scope tightly; one
rung. Probe files in the scratchpad, outside the repo.

## Environment (verify, then trust)

- **Toolchain in-loop (preferred):** host `lean`/`lake` (v4.30.0). `lake build Anabelian.<File>`
  is the real build; `lake env lean <scratch>.lean` probes defeqs/instances/lemma names before
  editing the project file. If sandboxed, the detached-probe-env recipe (NOTES P36) is the
  fallback.
- **Workflow**: source-grep Mathlib for every name BEFORE writing; probe; then `lake build`;
  expect the new file + the root `Anabelian.lean` edit only.
- **Pre-commit gate**: `scripts/preflight.sh` — clause 0 clean tree, long lines (≤100 chars),
  named statement-level `letI`/`haveI` binders, import-chain completeness, warning-free
  `lake build`. Committable only if it exits 0.
- **`scripts/refactor.sh`** (tracked, P42, **not yet run**): one-shot flat→folders restructure;
  its own dedicated pass only.

## House idioms (recent vintage; older ones in NOTES P25–41)

- `push_neg` is deprecated in current Mathlib — use `push Not` (bit P51).
- `ValuationSubring` opens shadow `mem_nonunits_iff` — `_root_.mem_nonunits_iff` (bit P50).
- `rw` fails across the `restrictNormalHom`/`restrictNormal` defeq — use `calc`/`exact` with
  `AlgEquiv.restrictNormal_commutes` (bit P50).
- A `variable` not mentioned in a declaration is not auto-bound (`comapRingHom` takes `K' A`).
- `ℕ∞` sups: `lt_biSup_iff`/`le_biSup` + `ENat.eq_top_iff_forall_gt`/`ENat.add_one_le_iff`; for
  `≤`/`=` from natural-cofinality use the P51 project lemmas `enat_le_of_forall_natCast_lt`/
  `enat_eq_of_forall_natCast_lt_iff`.
- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake-level linter; probes only
  catch elaboration).
- D2 (spectral/normed bridge) lives **entirely inside proofs** via `letI`. Keep it that way.

## The queue after Pass 52

The remaining Prop.-3 prerequisite (whichever of (a)/(b) wasn't taken), then **Prop. 3 itself**
(the sum formula), → IV §3 **Lemma 5** `(G/H)_{φ_{L/K'}(u)} = G_u H/H` → **`φ`-transitivity**
(Prop. 15) + **Herbrand's theorem** `(G/H)^v = G^v H/H` (Prop. 14), then Hasse–Arf and the limit
`G^v ≤ Gal(K̄/K)`. The `ψ` closed form / concavity remain optional analytic deepening. The
**R1-floor** (axiomatizing L3 for a conditional R1) stays ROADMAP-permitted but **deferred** —
a deliberate, ledgered decision with a rule-5 argument if ever taken. R1–R3 remain distant
targets that must be earned, never axiomatized.
