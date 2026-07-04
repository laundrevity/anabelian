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

## Current state — Pass 79 (2026-07-04)

**Ledger: `0 FOUNDATIONAL / 0 DEBT`; zero `axiom` declarations project-wide.** Clean cached build on
Mathlib `v4.30.0` (`scripts/preflight.sh` CLEAN: 79 project files, ~8500 build jobs, warning-free).
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
  (Pass 45), the lower-numbering **subgroup compatibility** `H_u = H ∩ G_u` (Pass 46), the
  **slope** `φ'(u) = 1/(G_0 : G_u)` (Pass 47), the **explicit piecewise-linear formula**
  `φ(u) = (|G_1|+…+|G_n|+(u−n)|G_{n+1}|)/|G_0|` (Pass 48), the **`ψ` slope**
  `ψ'(v) = (G_0 : G_{ψ(v)})` (Pass 49), and the **quotient-restriction skeleton** toward Serre's
  Lemma 5 — `decompositionQuotient : D(A) →* D(A ∩ K')`, exactness of
  `Gal(L/K') → Gal(L/K) → Gal(K'/K)` at the decomposition level, inertia preservation
  `G_0(L/K) → G_0(K'/K)` (Pass 50); **Serre's `i_G` function** `lowerIndex : D(A) → ℕ∞`
  (generator-free), with Lemma 1 `σ ∈ G_i ↔ i < i_G(σ)`, its calculus, and `i_H = i_G` on
  subextensions by `rfl` (Pass 51); **surjectivity of the quotient restriction** — `𝒪_L` is
  Galois-stable (integral closure), so `D(𝒪_L) = ⊤` and `D(A) ⧸ H ≃* D(A ∩ K')`: the `(G/H)`
  of Herbrand's theorem, realized (Pass 52); the **concrete `i_G`** —
  `i_G(σ) = v_L(σx − x)` (`lowerIndex_eq_addVal`) with Lemma 1 in generator form (Pass 53);
  the **monogenicity discharge** — `𝒪_L = 𝒪_K[x]` (Serre III §6 Prop. 12, finite-residue
  case), making the concrete `i_G` **unconditional**: `∃ x, ∀ σ, i_G(σ) = v_L(σx − x)`
  (Pass 54); and the **subextension characteristic polynomial** —
  `∏_{h ∈ Gal(L/K')} (X − h·x)` descends to a monic polynomial over `𝒪_L ∩ K'`
  (`fullProdXSubSMul` + the fixed-points descent, hypothesis-free at `𝒪_L`), the substrate of
  Prop. 3 (Pass 55); and the **lift-set identity** — the fiber of `decompositionQuotient` is
  the coset `s₀·H` as an explicit bijection (`decompositionFiberEquiv`), and Serre's
  polynomial transported along a lift is the fiber product `∏_{h}(X − (s₀·dr h)·x)`
  (Pass 56); and **`𝒪_L ∩ K' = 𝒪_{K'}`** with the Prop.-3 generator package at
  `B = 𝒪_L ∩ K'` — one `y` with `B = 𝒪_K[y]`, the coefficient telescoping
  `(σ̄y − y) ∣ (σ̄c − c)`, and the concrete `i_{K'/K}(σ̄) = addVal_B(σ̄y − y)` (Pass 57); and
  **Prop. 3's direction (i), proved** — `ι(σ̄y − y) ∣ ∏_{s ↦ σ̄} (x − s·x)` in `𝒪_L`,
  hypothesis-free (Pass 58); the **`addVal` bookkeeping** — the `e'`-dilation
  `addVal_A(ι c) = addVal_B(c)·e'` and the fiber sum
  `addVal(∏_{s ↦ σ̄}(x − s·x)) = Σ i_{L/K}(s)` (Pass 59); and the **representation +
  `L = K'(x)` layer** — every integer of `L` is `g(x)` for `g` over `𝒪_K`, and the same
  generator generates `L` as a field over every intermediate `K'` (Pass 60); and the
  **remainder-vanishing brick** — a polynomial over `B` of degree `< [L:K']` whose image
  kills `x` is zero (Pass 61); **Prop. 3's direction (ii), proved** —
  `∏_{s ↦ σ̄} (x − s·x) ∣ ι(σ̄y − y)` for every `y ∈ B` (Pass 62); **SERRE IV §1
  PROP. 3, PROVED** — the sum formula `i_{K'/K}(σ̄) · e' = Σ_{s ↦ σ̄} i_{L/K}(s)`,
  generator-free, axiom-free (Pass 63); the **fiber index profile** toward Lemma 5 —
  `i(s₁·h) = min(i_H(h), j)` for a fiber maximizer `s₁`, with the `Σ min` sum form
  (Pass 65); the **double count** — `Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|` via level sets
  and Pass 51's Lemma 1 (Pass 66); the **`φ`-bridge** —
  `Σ_{k≤n} |G_k| = |G_0|·(φ(n)+1)` with the cast forms (Pass 67); **`e'` in ideal
  form** — `Ideal.ramificationIdx 𝔪_B 𝔪_L = addVal(ι π_B)` on the new `comapAlgebra`
  scaffold (Pass 68); the **`IsGaloisGroup` package** — `D_{K'}(𝒪_L)` is a Galois group
  for `B ⊆ 𝒪_L` (faithful, commuting, invariant — Pass 55's descent in instance form)
  (Pass 69); the **inertia matching + instance package** — the project's `G₀` IS
  Mathlib's `Ideal.inertia 𝔪_L D` (by `pow_one`), with LiesOver/Module.Finite/torsion-free/
  separable-residue all in place (Pass 70); **`e' = |H₀|`, proved** —
  `(|H₀| : ℕ∞) = addVal(ι π_B)`, the classical `e = |inertia|` for `L/K'` (Pass 71); **THE NUMERICAL LEMMA 5, proved** — `i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1` for every
  `σ̄ ≠ 1` (Pass 72); **SERRE IV §3 LEMMA 5, proved** —
  `(G_u).map (decompositionQuotient) = ramificationGroup K B ⌈φ_{L/K'}(u)⌉₊`, Herbrand's
  renumbering lemma `(G/H)_{φ_{L/K'}(u)} = G_u H/H` (Pass 73); the **card
  multiplicativity** — `|G_u| = |(G/H)_{⌈φ_{L/K'}(u)⌉}| · |H_u|`, Prop. 15's arithmetic
  heart, with `e_{L/K} = e_{K'/K}·e_{L/K'}` at `u = 0` (Pass 74); the **alignment
  lemma** — the quotient filtration is constant on integer indices in
  `(φ_{L/K'}(n), ⌈φ_{L/K'}(n+1)⌉]` (Pass 75); **PROP. 15, proved: `φ`-transitivity** —
  `φ_{L/K}(u) = φ_{K'/K}(φ_{L/K'}(u))` for every real `u`, by right-derivative gluing
  (Pass 76); **HERBRAND'S THEOREM, proved** — `(G^v).map (decompositionQuotient) =
  (G/H)^v` for every real `v`: the upper numbering is compatible with quotients (Serre IV
  §3 Prop. 14) (Pass 77); the **consolidated Herbrand package** —
  `Anabelian/Herbrand/Main.lean`, the arc's nine headline theorems audited in one block,
  plus Herbrand on the canonical carrier `𝒪_{K'}` (Pass 78); and the **L2-capstone
  design** — the extension of `G^v` to `Gal(K^sep/K)` (still chapter-IV/L2 material; the
  earlier "L3 gateway" label named the consumer, not the stratum): carrier
  `separableClosure` (not `AlgebraicClosure` — char-`p` honesty), preimage-intersection
  definition, brick ladder B1–B5 mapped in `ROADMAP.md` (Pass 79).
- **L3–L4 and the targets R1–R3 — `NOT-STARTED`, explicitly multi-year and far.** L3 (local class
  field theory), L4 (global tools), then the reconstruction targets: R1 (local reconstruction), R2
  (Neukirch–Uchida), R3 (mono-anabelian recovery). Every file touches the project's subject
  (absolute Galois groups) while recovering nothing from an abstract group; the targets remain
  untouched and must be *earned*, never axiomatized.

*(Pass 64 restructured the source tree: `Anabelian/` is now nine content folders —
`Galois`, `FiniteField`, `Reduction`, `Ramification`, `Herbrand`, `Extension`, `LocalField`,
`Quotient`, `ForMathlib` — with module paths updated and declaration names unchanged.)*

**Current frontier:** with **Serre IV §1 Prop. 3 proved** (Pass 63 — the fourteen-pass
quotient arc P50–63, all axiom-free), the next target is **Serre IV §3 Lemma 5**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` — converting the `i`-sum identity into the `φ`-renumbering
statement — and through it **`φ`-transitivity** (Prop. 15) and **Herbrand's theorem**
`(G/H)^v = G^v H/H` (Prop. 14), the upper numbering's defining quotient-compatibility. The
`φ`/`ψ` analytic theory (Passes 44–49) and the full quotient arithmetic (Passes 50–63) are
in place, and the fiber index profile (Pass 65) + the double count (Pass 66) convert the
sum formula into `e'·i_{K'/K}(σ̄) = Σ_{k<j} |H_k|`, and the `φ`-bridge (Pass 67) reads the
right side as `|H_0|·(φ_{L/K'}(j−1)+1)`; for `e' = |H_0|`, Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn` (`|inertia| = e`) applies once the project's
objects are identified with the ideal-theoretic ones — Pass 68 did the `e'` half
(`ramificationIdx 𝔪_B 𝔪_L = addVal(ι π_B)`), Pass 69 the `IsGaloisGroup` gateway, Pass 70
the inertia matching plus every remaining instance, Pass 71 closed `e' = |H₀|`, Pass 72
assembled the numerical Lemma 5, and **Pass 73 proved Lemma 5 itself**:
`(G_u).map (decompositionQuotient) = ramificationGroup K B ⌈φ_{L/K'}(u)⌉₊`. Passes 74–76 took Prop. 15
(`φ`-transitivity), and **Pass 77 closed the arc with HERBRAND'S THEOREM**:
`(G^v).map (decompositionQuotient) = (G/H)^v` — the upper numbering is
quotient-compatible. Pass 78 consolidated the arc
(`Anabelian/Herbrand/Main.lean`) and Pass 79 designed **L2's capstone**: `G^v` on
`Gal(K^sep/K)` — exactly what Herbrand-compatibility makes well-defined — by
preimage-intersection over the finite Galois subextensions, with the five-brick ladder
(full-group form → instance plumbing → definition → functorial compatibility → projection
surjectivity) recorded in `ROADMAP.md`. L3 (local class field theory) remains NOT-STARTED
and consumes this interface.

## Build

```sh
lake exe cache get   # never build Mathlib from source
lake build
```

`lake build` re-runs the `#print axioms` audit of the headline results on every build;
`scripts/preflight.sh` is the full pre-commit gate (clean tree, line length, import-chain
completeness, named-binder check, and a warning-free build).
