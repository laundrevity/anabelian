# HANDOFF.md — session bootstrap (written after Pass 46, 2026-06-25)

**State:** Pass 43 **discharged the canonicity obligation** (the last L-rung prerequisite). **Passes
44–46 built the Herbrand machinery** (Serre IV §§1, 3, all absent from Mathlib, all axiom-free): the
**Herbrand function** `φ` (`Anabelian/HerbrandFunction.lean`, P44 — strictly monotone, continuous),
its inverse **`ψ = φ⁻¹` + the upper numbering** `G^v(L/K) = G_{⌈ψ(v)⌉}` (`Anabelian/UpperNumbering.lean`,
P45), and the **subgroup compatibility** `H_u = H ∩ G_u` (Serre IV §1 Prop. 2,
`Anabelian/RamificationSubgroup.lean`, P46 — `ramificationGroup_eq_comap`). Ledger is **`0 FOUNDATIONAL
/ 0 DEBT`**, zero `axiom` declarations project-wide — keep it that way. **YOUR FIRST TASK is Pass 47 —
`φ`-transitivity** (below).

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass, clean-tree),
`AXIOM_LEDGER.md` (state + tail Pass-46 entry), `ROADMAP.md` (status header says Pass 46), and the
**tail of `NOTES.md`** (Passes 41–46: assembly, canonicity, Herbrand `φ`/`ψ` + upper numbering, Prop. 2).
**Session start:** `git status` — the tree must be clean. `.claude/` is now `.gitignore`d, so a clean
tree shows **nothing** untracked; `scripts/preflight.sh` clause 0 now *enforces* this (it fails on
any untracked file outside `.gitignore`). If anything is untracked, resolve it before new work
(`CLAUDE.md` clean-tree rule) — this is exactly how the Pass-42 orphan was caught.

## Where the mathematics stands

**The descent is closed and harvested** (P29–37): `ker θ₀ = G₁` unconditionally for every finite
separable `L/K`; the full P27/P28 quotient theory concrete at `𝒪_L` (`G₁` = the normal Sylow
`p`-subgroup of `G₀`). Serre IV §§1–2, finite level, zero conditional hypotheses, zero axioms.

**The assembly is COMPLETE** (P38–41): `IsNonarchimedeanLocalField L` for every finite separable
`L/K`, on the rung-1 valuative structure `extensionValuativeRel` (induced by `𝒪_L`). Parents 1
(`IsValuativeTopology`) + 3 (`IsNontrivial`) from P38; parent 2 (`LocallyCompactSpace`) from P41 via
`FiniteDimensional.proper` + the rung-1 = spectral topology identification (`isValuativeTopology_unique`).

**Canonicity is DISCHARGED** (P43): `extensionValuativeRel K L = extensionValuativeRel K' L` for a
tower `K ⊆ K' ⊆ L` (`Anabelian/ExtensionCanonical.lean`, `extensionValuativeRel_base_independent`) —
the relation depends only on `𝒪_L`, base-independent by integral-closure transitivity. Intermediate
fields are now usable as base fields.

**The ascent is OPEN, rungs 1–3 built** (P44–46): the Herbrand function `φ`
(`Anabelian/HerbrandFunction.lean`, `herbrandPhi K A`, Serre's `∫_0^u dt/(G_0 : G_t)`; integrand
antitone ⟹ clean `intervalIntegral` analysis ⟹ `herbrandPhi_strictMono`/`_continuous`/`_zero`/`_eq_id`
/`_le_self`), its inverse `ψ` (`Anabelian/UpperNumbering.lean`, `herbrandPsi K A` via
`Function.invFun`; `herbrandPsi_strictMono`/`_continuous`/`_zero`/`_eq_id`, inverse identities
`herbrandPhi_psi`/`herbrandPsi_phi`), the **upper numbering** `upperRamificationGroup K A v =
G_{⌈ψ(v)⌉}` (`_zero` = `G_0`, `_antitone`, `_eventually_bot`), and the **subgroup compatibility**
`H_u = H ∩ G_u` (`Anabelian/RamificationSubgroup.lean`, `ramificationGroup_eq_comap`/`_map_eq`, the
restriction `decompositionRestrict : Gal(L/K') →* Gal(L/K)`). Both `φ`/`ψ` are abstract engines
`herbrandPhiSeq`/`herbrandPsiSeq (g : ℕ → ℝ)` + the ramification instantiation. All axiom-free.

## YOUR FIRST TASK — Pass 47: `φ`-transitivity `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}`

**Goal:** Serre IV §3 Prop. 15 — the Herbrand functions of a tower **compose**. This is the second
prerequisite for Herbrand's theorem (after P46's Prop. 2), and where Pass 43's canonicity + the tower
theory earn their keep. It is **harder than P46** — it touches the integral/order formula, not just
subgroup bookkeeping — so scope it as its own rung.

**The math.** For `K ⊆ M ⊆ L` (here probably `K ⊆ K' ⊆ L` in the project's variable naming), with
`H = Gal(L/M) ≤ G = Gal(L/K)`: `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}`. The lever is P46's `H_u = H ∩ G_u`
(`ramificationGroup_eq_comap`), which ties the order sequences `|G_i|`, `|H_i| = |H ∩ G_i|`, and the
quotient `|(G/H)_j|` across the tower. Serre's proof differentiates: both sides have the same value at
0 and the same derivative (`φ'` is `1/(G_0:G_u)`), so they agree. **Inventory first** whether to go via
the derivative (would want the deferred slope lemma `φ'(u) = 1/(G_0:G_u)` — a clean sub-rung to do
first) or via the explicit piecewise sum. Consider doing the **slope `φ'` lemma** (FTC on the
`intervalIntegral`, deferred since P44) as a self-contained Pass 47 if full transitivity is too big.

**Method (the P43–46 rhythm):** local toolchain **in the loop** — `lake build Anabelian.<File>`
(≈3 s incremental) for the real build, `lake env lean <scratch>.lean` for throwaway probes of
defeqs/instances/lemma names before committing. Scope tightly; one rung.

**Method (the P43–44 lesson):** use the local toolchain **in the loop** — `lake build
Anabelian.<File>` for the real build (≈3 s incremental), and `lake env lean <scratch>.lean` for fast
throwaway probes of defeqs/instances/lemma names before committing to a proof. Scope ONE concrete
rung (e.g. just `ψ` + its basic properties); do not attempt all of §3 at once.

## Environment (verify, then trust)

- **Toolchain in-loop (P43–44 rhythm — preferred):** the host `lean`/`lake` (v4.30.0) is directly
  usable. `lake build Anabelian.<File>` is the real build (≈3 s incremental once deps are cached);
  `lake env lean <scratch>.lean` runs a throwaway probe with the full `LEAN_PATH` (import `Mathlib` +
  the project module, `#print axioms`/`example`/`#synth` to settle defeqs, instances, lemma names
  before editing the project file). Use it constantly — the P43 draft failed precisely because it was
  written without a compiler. Keep probe files in the scratchpad (outside the repo, so clause 0 stays
  clean). If running in a *sandboxed* session instead, the older detached-probe-env recipe (NOTES P36)
  is the fallback, and `lake build`/`git commit` may need to run host-side (the mount can deny
  `unlink`, leaving a stale `.git/index.lock` to `rm -f`).
- **Workflow**: source-grep Mathlib for every name BEFORE writing; probe substantive proofs with
  `lake env lean`; then `lake build` the project file; expect the new file + the root `Anabelian.lean`
  edit only.
- **Pre-commit gate**: `scripts/preflight.sh` (run host-side) — **clause 0 clean tree** (new, P42),
  long lines (chars not bytes), named statement-level binders, import-chain completeness
  (`scripts/chain_check.py`), and a `lake build` warning gate. A pass is committable only if it exits 0.
  **Never `grep -v` warnings out of probe output** — probe warnings are signal.
- **`scripts/refactor.sh`** (tracked, P42, **not yet run**): a one-shot flat→folders restructure of the
  (now 48-file) `Anabelian/` tree. Belongs in its own dedicated pass with a host `lake build` to verify; do
  not fold it into a math commit.

## House idioms (P36–41 vintage; older ones in NOTES P25–35)

- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake linter; the probe env cannot
  catch lake-level linters — only elaboration).
- The `letI`-tower statement pattern (relation → `ValuativeRel.topologicalSpace` →
  `IsTopologicalAddGroup.rightUniformSpace` → `isUniformAddGroup_of_addCommGroup`) is the house form
  for topological statements about `L`; instances fire automatically under it (probe-verified).
- D2 (the spectral/normed bridge) lives **entirely inside proofs** via `letI` — none in any
  statement, so `#print axioms` stays standard-only. Keep it that way.
- Renames/nesting that bit recent sessions: `sub_pow_expChar_pow_of_commute`;
  `Nat.exists_eq_pow_mul_and_not_dvd`; `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`
  (nested!); `RingEquiv.subringCongr`; `Valuation.integer` (not `Valued.integer`) via `Valued.v`.

## The queue after Pass 47

Continue the **ascent**: after `φ`-transitivity comes **Herbrand's theorem** `(G/H)^v = G^v H/H`,
then Hasse–Arf and the limit `G^v ≤ Gal(K̄/K)` (Serre IV §3); also still deferred — concavity of `φ`,
the explicit piecewise-linear formula, the slope `φ'(u) = 1/(G_0 : G_u)` (a likely Pass-47
sub-rung). Separately, the **R1-floor** (axiomatizing L3 local class field theory to
reach a *conditional* R1 reconstruction result) is a ROADMAP-permitted but **deferred** option — if
taken, it must be a deliberate, ledgered decision (A1/A2 preserved in the NOTES Pass-42 entry) with
an explicit rule-5 argument that the conditional theorem does not trivially imply R1. R1–R3 remain
distant targets that must be earned, never axiomatized — the line between inputs and targets is drawn
in `ROADMAP.md` and is the project's reason for existing.
