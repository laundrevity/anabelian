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

## Current state — Pass 98 (2026-10-08)

**Ledger: `0 FOUNDATIONAL / 0 DEBT`; zero `axiom` declarations project-wide.** Clean cached build on
Mathlib commit `0653561` (Lean `v4.35.0-rc2`; bumped from `v4.30.0` in Pass 97)
(`scripts/preflight.sh` CLEAN: 98 project files, 10542 build jobs, warning-free). Since Pass 98 the
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
  are thereby **imported**; L3.4 (the ramification correspondence) is open and unblocked.
- **L4 — global reciprocity imported (Pass 98), Chebotarev absent.** R1–R3 — NOT-STARTED:
  local, Neukirch–Uchida, and mono-anabelian reconstruction remain distant targets. No
  reconstruction theorem is claimed; the reciprocity theorems used are external and
  existential (`profiniteLocalReciprocity` is `Nonempty`, not the canonical map).

**Current frontier:** `cyclicHerbrandQuotient_units` proves `q(Kˣ) = q(Rˣ) · n`
for compatible ring automorphisms, carrying `n ≠ 0`, periodicity on `Kˣ`, and explicit
`Ĥ¹` finiteness on `Rˣ` and `Kˣ`. Value-group finiteness is derived. Pass 95's
`finite_acyclic_kernel_reduction` derives finite middle cohomology and quotient one
from an acyclic subgroup with finite quotient. The [unit proof design](NOTES.md#pass-95)
specifies the normal-basis lattice, regular unit layers, adic-completeness transport,
both finiteness discharges, and the field-norm comparison. Pass 96 proved the
design's generic layer (`cyclic_exact_of_complete_filtration`, `regular_cyclic_exact`,
`herbrandH_subsingleton_of_exact`, the `restrictAut`/`quotientAut`/`layerAut` actions):
given a `σ`-stable, separated, complete filtration of a subgroup `V₀ ≤ 𝒪_Lˣ` with regular
layers, both `Ĥ(V₀)` vanish. The arithmetic inputs — the normal-basis lattice, its unit
subgroups, adic completeness, finite index — remain unproved (rows P97–P101 of the
Pass-95 design) — and, since Pass 98, no longer on the critical path to reciprocity, which
is imported. **Next: Pass 99 — transport the upper-numbering identification and upper-jump
integrality to the project's `G^v`, and decide (HANDOFF) whether the in-project unit-quotient
program continues or L3.4 takes over.** Hasse–Arf is imported and identified (Pass 98).

The earlier [strata and frontier detail](NOTES.md#pass-93-readme-detail) is preserved
verbatim in NOTES through Pass 93; the Pass-98 summary above states the current frontier.

## Build

```sh
lake exe cache get   # never build Mathlib from source
lake build
```

`lake build` re-runs the `#print axioms` audit of the headline results on every build;
`scripts/preflight.sh` is the full pre-commit gate (clean tree, line length, import-chain
completeness, named-binder check, and a warning-free build).
