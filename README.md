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

## Current state — Pass 47 (2026-06-25)

**Ledger: `0 FOUNDATIONAL / 0 DEBT`; zero `axiom` declarations project-wide.** Clean cached build on
Mathlib `v4.30.0` (`scripts/preflight.sh` CLEAN: 49 project files, ~8500 build jobs, warning-free).
Every headline `#print axioms` is standard-only (`propext` / `Classical.choice` / `Quot.sound`); no
open owed witnesses. *(For the always-current authoritative status see `ROADMAP.md`'s header and
`AXIOM_LEDGER.md`'s "Active axioms" table; this section mirrors them.)*

The project has earned, axiom-free, the following strata (detail in `NOTES.md` / `ROADMAP.md`):

- **L1 — Galois theory of local & finite fields (Passes 1–21).** `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` as a
  topological group (the first L1 "whole of depth", Pass 10); `Gal(ℚ̄/ℚ)` non-abelian (Pass 3); and
  — the project's **first `DEBT`-discharged-into-theorem** — the residue-reduction surjection
  `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)`: taken as a `FOUNDATIONAL` boundary at Pass 5, reclassified to `DEBT` at
  Pass 11, and **discharged into a proved `theorem` at Pass 20** (perfect case; the imperfect
  equal-characteristic case is a tracked owed generality, not an axiom).
- **L2 — Higher ramification (Serre, *Local Fields*, ch. IV), in progress.** The lower-numbering
  filtration `G_i` and its theory (Passes 22–28: inertia, antitone, normality, the tame character
  `G_0/G_1 → 𝓀ˣ`, wild inertia `G_1` a `p`-group). The **descent** — `𝒪_L` as a valuation subring
  of a finite extension, the ramification theory concrete at `𝒪_L` — closed and harvested (Passes
  29–37). The **finite-extension local-field assembly** `IsNonarchimedeanLocalField L` complete
  (Passes 38–41). The **canonicity** of `extensionValuativeRel` across towers (Pass 43). The
  **Herbrand ascent**: the function `φ` (Pass 44), its inverse `ψ` and the **upper numbering** `G^v`
  (Pass 45), the lower-numbering **subgroup compatibility** `H_u = H ∩ G_u` (Pass 46), and the
  **slope** `φ'(u) = 1/(G_0 : G_u)` (Pass 47).
- **L3–L4 and the targets R1–R3 — `NOT-STARTED`, explicitly multi-year and far.** L3 (local class
  field theory), L4 (global tools), then the reconstruction targets: R1 (local reconstruction), R2
  (Neukirch–Uchida), R3 (mono-anabelian recovery). Every file touches the project's subject
  (absolute Galois groups) while recovering nothing from an abstract group; the targets remain
  untouched and must be *earned*, never axiomatized.

**Current frontier:** `φ`-transitivity `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` (Serre IV §3 Prop. 15) and
Herbrand's theorem `(G/H)^v = G^v H/H` — the upper numbering's defining quotient-compatibility. With
the slope (Pass 47) in hand, the remaining wall is the index-multiplicativity / quotient relationship
`(G/H)_{φ(u)} = G_u H/H` (Serre Lemma 5).

## Build

```sh
lake exe cache get   # never build Mathlib from source
lake build
```

`lake build` re-runs the `#print axioms` audit of the headline results on every build;
`scripts/preflight.sh` is the full pre-commit gate (clean tree, line length, import-chain
completeness, named-binder check, and a warning-free build).
