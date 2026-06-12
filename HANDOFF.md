# HANDOFF.md — session bootstrap (written after Pass 39, updated after Pass 40, 2026-06-11)

**Pass 40 is DONE** (this document's original "first task", executed in the same session that
wrote it): `ValuativeRelCongr.lean` (the keystone pair + the group-uniformity uniqueness brick)
and `ExtensionSpectralSeam.lean` (P29's `hmem` exported; the rung-1 relation EQUALS the
spectral relation; `CompleteSpace L` spectrally). **YOUR FIRST TASK is Pass 41** — the
assembly closes; the worked-out plan is in NOTES' Pass-40 "Scope: pointer to Pass 41" (five
numbered steps from the `IsValuativeTopology`-uniqueness lemma to the assembly theorem
`IsNonarchimedeanLocalField L`). Everything below remains accurate as background.

You are picking up the `anabelian` project mid-stride. Read in this order before any work:
`CLAUDE.md` (the constitution — axiom budget, rule-2, commit-per-pass), `AXIOM_LEDGER.md`
(state: **0 FOUNDATIONAL / 0 DEBT**, zero `axiom` declarations project-wide — keep it that
way), `ROADMAP.md` (status header says Pass 39), and the **tail of `NOTES.md`** (Passes 36–39:
the descent finale, the consolidation, and the assembly's first two rungs — including the
environment recipes this document references). Session start: `git status` clean (only
`.claude/` untracked is OK); `df -h /sessions` (see Environment below).

## Where the mathematics stands

**The descent is closed and harvested** (P29–37): `ker θ₀ = G₁` unconditionally for every
finite separable `L/K` of nonarchimedean local fields (P36, `hresid` proved via the
orbit-polynomial bricks + freshman's dream through `Polynomial.expand` + iterated-Frobenius
surjectivity); the full P27/P28 quotient theory concrete at `𝒪_L` (P37): additive characters,
`G₁` = the normal Sylow `p`-subgroup of `G₀`. Serre IV §§1–2, finite level, zero conditional
hypotheses, zero axioms.

**The assembly is two rungs in** (P38–39), target `IsNonarchimedeanLocalField L` (Mathlib's
class; three parents). Rung 1 (`Anabelian/ExtensionLocalField.lean`): `extensionValuativeRel`
(the relation on `L` from `𝒪_L`'s valuation; a `@[reducible] def`, NOT an instance —
base-independence across towers is a named canonicity obligation), parents `IsValuativeTopology`
(free upstream) and `IsNontrivial` (P30 uniformizer) discharged. Rung 2
(`Anabelian/ExtensionValued.lean`): Mathlib's porting helper makes `L` `Valued` **on the
rung-1 structures** (adopts the given uniformity; `Valued.v = valuation L` is `rfl`), and the
integer ring is `𝒪_L` (as subrings; `valued_integer_extensionValuativeRel`), a DVR with finite
residue field (P30/P31 transported along `RingEquiv.subringCongr`). The `Valued`-native
compactness criterion (`compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`,
`Mathlib/Topology/Algebra/Valued/LocallyCompact.lean`) is therefore **two-thirds discharged**.

## YOUR FIRST TASK — Pass 40: the completeness conjunct

**Goal:** `CompleteSpace ↥((Valued.v (R := L)).integer)` under the rung-1 `letI`-tower — then
`CompactSpace` (criterion `.mpr`), `LocallyCompactSpace L` (integers are a `𝓝 0`-neighborhood
via `is_topological_valuation` at `γ = 1`, then
`IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup`), then **the assembly theorem
`IsNonarchimedeanLocalField L`**. Two passes likely: completeness (P40), compactness + assembly
(P41).

**The route to completeness** (the spectral seam, returning in its honest form):

1. **Commit the kernel-checked-but-uncommitted keystone pair** (probed this session; re-probe,
   then commit):
   `ofValuation_congr : v.IsEquiv w → ofValuation v = ofValuation w` (one `ext x y`; the class
   is `@[ext]` at `ValuativeRel/Basic.lean:73`) and
   `ofValuation_eq_of_same_subring : (∀ x, w x ≤ 1 ↔ x ∈ A) → ofValuation A.valuation = ofValuation w`
   (via `Valuation.isEquiv_iff_val_le_one`, `Basic.lean:930`, + `valuation_le_one_iff`).
   Equal relations ⟹ equal `ValuativeRel.topologicalSpace` TERMS — the topology identification
   is an honest `rw`, not a homeomorphism argument.
2. **Export P29's internal `hmem` standalone**: `x ∈ extensionIntegers K L ↔ spectralNorm K L x ≤ 1`
   (equivalently `∈ Valued.integer` for the spectral `Valued L ℝ≥0`). The proof is VERBATIM
   inside `extensionIntegers`' definition (`Anabelian/ExtensionIntegers.lean:114–145`): copy the
   `letI` block (rightUniformSpace, RankOne, `Valued.toNontriviallyNormedField`,
   `spectralNorm.normedField K L`, ultrametric, `NormedField.toValued`) and the
   `isIntegral_iff_minpoly_coeff_mem_findim` / `spectralValue_le_one_iff` /
   `Valued.toNormedField.norm_le_one_iff` chain. The `synthInstance.maxHeartbeats 400000`
   set_option may be needed (same reason as P29).
3. **Conclude rung-1 relation = ofValuation(spectral valuation)** (1)+(2) ⟹ rung-1 topology
   **equals** the spectral-norm topology.
4. **`CompleteSpace L` spectrally**: inventory first — `Mathlib/Analysis/Normed/Unbundled/`
   (`SpectralNorm.lean` has a `section CompleteSpace` at ~:817; check `FiniteExtension.lean`
   for an f.d. completeness instance; fallback: `FiniteDimensional.complete` over the
   `NontriviallyNormedField K` bridge). Then `CompleteSpace 𝒪`: the integer ring is closed
   (`{‖·‖ ≤ 1}` closed in a metric space) + `IsClosed.completeSpace_coe`.
5. Transfer along (3) to the rung-1 tower; state everything in the `letI`-tower form of
   `ExtensionValued.lean` (copy its statement pattern verbatim).

**Alternative if (4) fights**: the 𝔪-adic route — `IsAdicComplete` from `Module.Finite ↥𝒪[K]`
(instance exists, `ExtensionMonogenic.lean:55`) over the adically-complete `𝒪[K]`
(`LocalField/Basic.lean` instance), with `exists_pow_maximalIdeal_le_map` (P34) giving
adic-topology agreement; then bridge adic-complete → uniform-complete for the discrete
valuation. More plumbing; inventory before choosing.

## Environment (verify, then trust)

- **Probe environment** may still be ALIVE at `/sessions/confident-inspiring-darwin/tmp/p38`
  (toolchain `lean/` 822 MB + `pkgs/` ~2.1 GB including the full analysis closure). Test:
  `$S/lean/bin/lean` with the 8-package `LEAN_PATH` (each entry
  `$S/pkgs/.lake/packages/<pkg>/.lake/build/lib/lean`). If the VM was reset, rebuild from the
  NOTES-P36 recipe + P38/P39 closure extensions (~5 calls, ~20 min): probes are
  `module`-headed files run with bare `lean`, publics+`.ir` only, 0.5–1 s per iteration.
- **Workflow** (the verified P36–39 rhythm): source-grep Mathlib for every name BEFORE writing;
  kernel-verify every substantive proof abstractly in the probe env (generic over
  `ValuationSubring`/`Valued`/whatever — the committed file should be name-substitution from
  checked code); `lake build` runs HOST-SIDE (ask the user; expect only the new file + root);
  commits run HOST-SIDE (the mount denies `unlink` — `git commit` in-sandbox is impossible;
  also in-sandbox `git status` leaves a stale `.git/index.lock` the user must `rm -f`).
- **Pre-handoff mechanical gate (COMMITTED as `scripts/preflight.sh` after Pass 40)**: run the
  static checks in-sandbox before every hand-off (long lines; named statement-level
  `letI`/`haveI` binders — anonymous `letI : T := ...` is the rule; `scripts/chain_check.py`
  for import-chain completeness, the P37/P39 failure class); the user runs the full
  `scripts/preflight.sh` host-side (adds the `lake build` warning gate) before every commit.
  **Never `grep -v` warnings out of probe output** — probe warnings are signal (the Pass-40
  unusedVariables batch was visible in the probe and filtered away; it cost a host round-trip).
- **Disk**: `/sessions` was reset this session (~9.3 G free at last check) but dead-session
  corpses accumulate (~1.5–3 G per session); the host-side fix (verified): quit Claude fully,
  delete `~/Library/Application Support/Claude/vm_bundles/claudevm.bundle`, relaunch — costs
  the probe env (NOTES P36 post-pass addendum has details).

## House idioms — the newer ones (P36–39 vintage; older ones in NOTES P25–35)

- Defs of class type need `@[reducible]`/`@[implicit_reducible]` (lake linter; the probe env
  cannot catch lake-level linters — only elaboration).
- Import-regex for closure BFS must handle `public import`, `meta import`, `import all`.
- Renames/nesting hit this session: `sub_pow_expChar_pow_of_commute` (ExpChar era);
  `Nat.exists_eq_pow_mul_and_not_dvd` (replaces ord_proj/ord_compl);
  `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing` (nested!);
  `RingEquiv.subringCongr`; `Valuation.integer` (not `Valued.integer`) reached via `Valued.v`.
- `Valuation.Compatible.vle_iff_le`/`vlt_iff_lt` take explicit `x y`; the canonical
  `(valuation R).Compatible` is an instance; `IsValuativeTopology.v_eq_valuation` is `rfl`.
- The `letI`-tower statement pattern (relation → `ValuativeRel.topologicalSpace` →
  `IsTopologicalAddGroup.rightUniformSpace` → `isUniformAddGroup_of_addCommGroup`) is the
  house form for topological statements about `L`; instances (helper-`Valued`,
  `IsValuativeTopology`, `NonarchimedeanRing`) fire automatically under it (probe-verified).
- Host-build failures this session were 100% infrastructure (imports ×2, linter ×2), 0%
  mathematics — the probe methodology covers all elaboration risk.

## After Pass 40/41 (the assembly closes)

The queue: the **canonicity obligation** (base-independence of `extensionValuativeRel` across
towers — needed before `M/L/K` iteration); then the **ascent** (Herbrand `φ`/`ψ`, upper
numbering — Serre IV §3), for which the assembly was built: intermediate fields as base fields
make Herbrand's quotient theorem statable. R1–R3 remain distant targets that must be earned,
never axiomatized — the line between inputs and targets is drawn in `ROADMAP.md` and is the
project's reason for existing.
