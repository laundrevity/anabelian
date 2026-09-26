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

## Current state — Pass 97 (2026-09-26)

**Ledger: `0 FOUNDATIONAL / 0 DEBT`; zero `axiom` declarations project-wide.** Clean cached build on
Mathlib `v4.30.0` (`scripts/preflight.sh` CLEAN: 98 project files, 8574 build jobs, warning-free).
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
  Pass 97 proves the abstract DVR unit filtration, finite quotients for finite residue
  fields, the depth-one residue equivalence, and the exact coefficient map with its
  twisted action at positive depth.
- **L4 and R1–R3 — NOT-STARTED.** Global tools and local, Neukirch–Uchida, and
  mono-anabelian reconstruction remain distant targets. No reconstruction or local
  reciprocity theorem is claimed.

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
layers, both `Ĥ(V₀)` vanish. Pass 97 supplies the abstract `U^m` API and proves finite
index for any subgroup containing `U^m` when the residue field is finite. It also
identifies the residue quotient and the positive-depth coefficients, retaining their
twisted action. The local action, adic-completeness transport, normal-basis lattice,
its unit subgroups, and regular layers remain for Passes 98–101.
**Next: P98, local action and period, adic-completeness transport, and field-norm comparison.**
Class formation and reciprocity remain ahead; Hasse–Arf is separately deferred.

The earlier [strata and frontier detail](NOTES.md#pass-93-readme-detail) is preserved
verbatim in NOTES through Pass 93; the Pass-97 summary above states the current frontier.

## Build

```sh
lake exe cache get   # never build Mathlib from source
lake build
```

`lake build` re-runs the `#print axioms` audit of the headline results on every build;
`scripts/preflight.sh` is the full pre-commit gate (clean tree, line length, import-chain
completeness, named-binder check, and a warning-free build).
