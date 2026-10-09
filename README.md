# anabelian

A long-horizon (multi-year) Lean 4 + Mathlib formalization effort in **anabelian geometry**,
aimed ultimately at the **mono-anabelian reconstruction** of a field from Galois- and
monoid-theoretic data.

This is **not** a continuation of the `iutt` project and does not import it. `iutt`'s job was to
*locate* the reconstruction gap; this repository's job is to *fill* it, rung by rung, axiom-free.

## How this repository is governed

The discipline matters more than any single file, and **all governance files must agree on the
current state** (see `CLAUDE.md` → "Governance consistency"). Read these in order:

- **`CLAUDE.md`** — the constitution: the axiom-budget discipline, rule-2, the honest scope, and the
  governance-consistency rule.
- **`ROADMAP.md`** — the dependency ladder from the current Mathlib floor up to mono-anabelian
  reconstruction, each rung `NOT-STARTED` / `IN-PROGRESS` / `DONE`. **Its status header is the
  authoritative "current pass / current state" marker.**
- **`AXIOM_LEDGER.md`** — every non-standard axiom, classified `FOUNDATIONAL` (honest boundary) vs
  `DEBT` (a hole we intend to fill); the source of truth for what is assumed. Its "Active axioms"
  table is the authoritative ledger count.
- **`NOTES.md`** — the per-pass record: the Mathlib inventory, what was proved, the ledger delta.
- **`HANDOFF.md`** — the session bootstrap: the current state and the next task.
- **`Anabelian/Statements/`** — the **statement ledger** (since Pass 99): `Prop`-valued `def`s
  stating target theorems, audited as *statements* (sources, every convention choice) before any
  proof is attempted, and checked by the preflight gate. Guards against the failure the axiom
  ledger cannot see — a compiling, standard-only statement of the wrong theorem.

## Current state — Pass 99 (2026-10-08)

**Ledger: `0 FOUNDATIONAL / 0 DEBT`; zero `axiom` declarations project-wide; statement ledger:
1 entry (`L34`).** Clean cached build on
Mathlib commit `0653561` (Lean `v4.35.0-rc2`; bumped from `v4.30.0` in Pass 97)
(`scripts/preflight.sh` CLEAN: 101 project files, 10545 build jobs, warning-free). Since Pass 98 the
project depends on the external Lean library `n-yamaguchi-0729/ClassFieldTheory @ 7713795`
(local/global class field theory, Hasse–Arf; every imported headline standard-only) — listed in
`AXIOM_LEDGER.md`'s "External dependencies" section as an honest boundary: **imported, not earned**.
Every headline `#print axioms` is standard-only (`propext` / `Classical.choice` / `Quot.sound`); no
open owed witnesses. *(For the always-current authoritative status see `ROADMAP.md`'s header and
`AXIOM_LEDGER.md`'s "Active axioms" table; this section mirrors them.)*

The current strata are:

- **L1 — finite and local Galois theory.** Finite-field absolute Galois groups and the
  residue-reduction surjection are proved (the latter for perfect base fields; the
  imperfect case remains tracked).
- **L2 — higher ramification, DONE (Pass 83), consolidated in Pass 84.** The finite-level
  theory, Herbrand's theorem, and the absolute upper filtration as a closed inverse
  limit are proved. The filtration is antitone, normalized, and separating.
- **L3 — local class field theory, IN-PROGRESS.** The maximal abelian subextension
  interface is complete (Pass 86). The cyclic layer has the Herbrand quotient, finite
  triviality, short-exact-sequence multiplicativity, the cyclic norm/difference pair,
  and `q(ℤ) = n` (Passes 87–92). Pass 93 supplies the valuation exact sequence
  `1 → Rˣ → Kˣ → Multiplicative ℤ → 1` for a DVR and its fraction field. Pass 94
  proves equivariance and the conditional identity `q(Kˣ) = q(Rˣ) · n`. Pass 95
  proves the finite-acyclic-kernel reduction and records the local unit proof design.
  Pass 96 proves the design's field-free layer: stable/quotient/layer actions with the
  naturality of the cyclic pair, the acyclicity of the regular module `C[G]`, and
  filtration lifting (`ker f = im g` from separated, complete, layer-exact filtrations).
  Pass 97 is a governance pass (the Mathlib bump), with no mathematical change.
  **Pass 98 imports local class field theory and Hasse–Arf** from ClassFieldTheory and
  proves the bridge: `hasseArf_extension` / `hasseArf_herbrandPhi` state Hasse–Arf at the
  project's `𝒪_L`, `ramificationGroup`, `herbrandPhi` with no instance on `L` (the
  `HasExtension` compatibility is discharged from Pass 43), and the two Herbrand theories are
  identified (groups definitionally equal, `φ` equal as real functions, `ψ` equal). L3.1–L3.3
  are thereby **imported**. **Pass 99** retires the in-project unit-quotient route to
  reciprocity, builds the **unit filtration** `Uⁿ ≤ Kˣ` with `U⁰/U¹ ≃ 𝓀ˣ` and
  `Uⁿ/Uⁿ⁺¹ ≃ 𝓀⁺` (`n ≥ 1`), transports the upper groups (equal to upstream's for `t > -1`;
  upper jumps of the project's `G^v(𝒪_L)` are integers), and opens the statement ledger with
  **`L34`**: `θ(Uⁿ) = Gⁿ(E/K)` at finite level. **L3.4 is IN-PROGRESS**: stated, not proved.
- **L4 — global reciprocity imported (Pass 98), Chebotarev absent.** R1–R3 — NOT-STARTED:
  local, Neukirch–Uchida, and mono-anabelian reconstruction remain distant targets. No
  reconstruction theorem is claimed; the reciprocity theorems used are external and
  existential (`profiniteLocalReciprocity` is `Nonempty`, not the canonical map).

**Current frontier:** L3.4, the ramification correspondence. Its source side is built —
`unitFiltration K n : Subgroup Kˣ` with `unitsQuotEquivResidueUnits : U⁰/U¹ ≃* 𝓀ˣ` and
`unitLayerQuotEquiv : Uⁿ/Uⁿ⁺¹ ≃* 𝓀⁺` for `n ≥ 1` (the multiplicative side of the Pass-24/27
characters). Its target side is the project's `G^v(𝒪_E)`, now proved equal to upstream's
upper groups for `t > -1` and carrying upper-jump integrality with no instance on `L`
(`upperRamificationGroup_extensionIntegers_jump_int`). The statement itself is ledgered as
`L34 : Prop` in `Anabelian/Statements/L34.lean` — finite level, against the Frobenius-normalized
Artin family, which upstream proves to exist and be unique — with every convention choice
recorded. The in-project unit-quotient program (Pass-95 rows P98–P102) is retired; its proved
generic layer (Passes 87–96) stays in the tree. **Next: Pass 100 — open the `L34` proof program:
inventory upstream's norm-index and conductor results, fix the route, prove the `n = 0` case
`θ(U⁰) = G_0`, and ledger the `K^ab`-level statement.** Hasse–Arf is imported and identified
(Pass 98).

The earlier [strata and frontier detail](NOTES.md#pass-93-readme-detail) is preserved
verbatim in NOTES through Pass 93; the Pass-99 summary above states the current frontier.

## Build

```sh
lake exe cache get   # never build Mathlib from source
lake build
```

`lake build` re-runs the `#print axioms` audit of the headline results on every build;
`scripts/preflight.sh` is the full pre-commit gate (clean tree, line length, import-chain
completeness, named-binder check, the statement-ledger checks, and a warning-free build).
