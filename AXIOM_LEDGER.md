# AXIOM_LEDGER.md

The spine of the project. **Every non-standard axiom used anywhere in the build is logged here**,
classified, cited, and (if `DEBT`) given an intended discharge path. This file — not `#print axioms`
output alone — is the source of truth for what the project assumes. It is updated every pass.

## The convention

`#print axioms` is run on every headline result (and, where practical, inside the source files
themselves so the audit re-runs on each `lake build`). Axioms are then bucketed:

- **Standard / free** — `propext`, `Classical.choice`, `Quot.sound`. These are the ambient logic of
  Lean + Mathlib and are *not* logged as entries. Their presence is expected and carries no debt.
- **`FOUNDATIONAL`** — a deep result we *deliberately* take as a known input from outside the
  current sub-target (e.g. a theorem whose own formalization is a separate multi-year effort). An
  honest boundary marker, not a failure. Must still carry a statement, the precise result encoded,
  and a literature citation.
- **`DEBT`** — a result we *intend to discharge inside this project* and are temporarily stubbing.
  A failure-in-progress. Must additionally carry an intended discharge path and must be **strictly
  below** the current sub-target in the dependency order (`ROADMAP.md`).

**Reclassification rule (anti-drift, added Pass 1).** An axiom's class is **not** allowed to change
silently. Any move `DEBT → FOUNDATIONAL` or `FOUNDATIONAL → DEBT` requires a dated, justified entry
in the **Reclassification log** below, naming the axiom, the old and new class, the date, and the
reason. This exists because over a multi-year horizon the insidious failure is quietly relabeling a
hole-we-owe (`DEBT`) as a boundary-we-accept (`FOUNDATIONAL`) — which would let the project "finish"
by redefining its debts away. In particular, a `DEBT → FOUNDATIONAL` move is only legitimate if the
result is genuinely *below* the current sub-target and we are consciously choosing to take it as an
external input; it must also be consistent with the per-target permitted-`FOUNDATIONAL` lists in
`ROADMAP.md` (R1–R3). Reclassifying a *target* (R1/R2/R3) as `FOUNDATIONAL` is never legitimate.

Hard rules (from `CLAUDE.md`):

1. A `DEBT` axiom that *is* the target, or trivially implies it, is **forbidden** (the cardinal
   sin: asserting what the project exists to prove).
2. Never `axiom` past a result Mathlib already has — search first (`#check`, `exact?`, grep
   `.lake/packages/mathlib`), verify every name.
3. Progress is measured as **net reduction in `DEBT`**, or a `DEBT` axiom discharged into a theorem,
   or an honest dependency map — never "it compiles."

Each entry uses this schema:

```
### <axiom_name>   [FOUNDATIONAL | DEBT]
- Statement:        <the Lean type, verbatim>
- Encodes:          <the precise mathematical result>
- Citation:         <literature reference>
- Rung (ROADMAP):   <where it sits in the dependency ladder>
- Discharge path:   <DEBT only: how/when we intend to prove it>
- Introduced:       <pass N>   Discharged: <pass M | —>
```

---

## Active axioms

| name | class | rung | introduced | status |
|------|-------|------|-----------|--------|
| `Anabelian.residueReduction_surjective` | `FOUNDATIONAL` | L1 (below R1) | Pass 5 | active |

**Count: 1 `FOUNDATIONAL`, 0 `DEBT`.**

### `Anabelian.residueReduction_surjective`   [FOUNDATIONAL]
- Statement: `∀ (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]`
  `[IsNonarchimedeanLocalField K], ∃ φ : Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K],`
  `Function.Surjective φ`.
- Encodes: the **residue reduction** `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)` of a nonarchimedean local field is
  surjective (equivalently `Gal(K^ur/K) ≅ Gal(𝓀̄/𝓀)`, the unramified-quotient theorem). We posit the
  *existence* of a surjection — weaker than, and implied by, the full classical theorem (the specific
  *continuous* residue reduction whose kernel is exactly the inertia subgroup).
- Citation: J.-P. Serre, *Local Fields*, ch. I–II; J. Neukirch, *Algebraic Number Theory*, ch. II.
- Rung (ROADMAP): **L1**, strictly **below R1**. It is a structural fact *about* a given local
  field's Galois group, not a recovery of the field from an abstract group — so it does not approach
  R1/R2/R3. Permitted as a `FOUNDATIONAL` input for R1 per the per-target list in `ROADMAP.md`.
- Why `FOUNDATIONAL` not `DEBT`: the maximal-unramified-extension Galois edifice that would *prove*
  it is **absent from Mathlib** (only ingredients — `HenselianLocalRing`, residue functoriality,
  `Algebra.IsUnramified` — are present), and is a substantial classical construction (Serre ch. I–III).
  Consciously taken as an external boundary, not a hole we are mid-proving. (Reclassifying it to
  `DEBT` later — i.e. committing to construct it in-project — is allowed via the Reclassification log.)
- Introduced: Pass 5.   Discharged: —

---

## Reclassification log

Dated record of every `DEBT ⇄ FOUNDATIONAL` class change (see the Reclassification rule above).
Empty so far — no axioms exist yet, so none have been reclassified.

| date | axiom | old class | new class | reason |
|------|-------|-----------|-----------|--------|
| *(none)* | — | — | — | — |

---

## Owed witnesses

**Distinct from axioms.** These are *unproved load-bearing-hypothesis claims*: a pass asserted some
hypothesis is essential to a theorem but did not prove the failure-when-dropped. Per the extended
rule-2 (`CLAUDE.md`), such a claim must be tracked here until discharged — it is **not** an axiom
(nothing is assumed in the kernel; the affected theorems are fully proved *with* the hypothesis),
but it **is** a debt of rigor: we owe a constructible counterexample showing the hypothesis cannot
be dropped. "Optional" is not a permitted status. Discharging a witness = proving the
failure-when-dropped axiom-free; it then moves to the Pass log as discharged.

**Route-first-step rule (anti-route-rot, added Pass 3).** Any recorded *discharge route* ("dischargeable
via X") must have its **first concrete step probe-verified** — the named Mathlib declarations exist
and their signatures fit, checked in a throwaway `lake env lean`. "Viable in principle" with no
probe-checked first step is not an acceptable route annotation: an unverified route is the same
species of plausible-but-unchecked claim as the owed witness itself, and lets unreachable obligations
masquerade as merely-deferred ones.

Schema: `lemma supported` · `hypothesis claimed load-bearing` · `witness owed` · `discharge target`.

### W1 — `[Finite F]` is load-bearing for finite-field Galois structure   ·   **DISCHARGED (Pass 3)**
- Lemmas supported: `Anabelian.absoluteGaloisGroup_mul_comm` (Pass 1, commutativity);
  `Anabelian.frobenius_zpowers_fixedField` and `Anabelian.frobenius_topologicalClosure_eq_top`
  (Pass 2, procyclicity — procyclic ⟹ abelian, so the witness covers both).
- Hypothesis claimed load-bearing: `[Finite F]` on the base field.
- Witness owed: a field whose absolute Galois group is **non-abelian** (hence non-procyclic).
- **Discharged Pass 3** by `Anabelian.rationals_absoluteGaloisGroup_not_commutative`
  (`Anabelian/RationalsNonAbelian.lean`): `Gal(ℚ̄/ℚ)` is non-commutative, via
  `(X³-2).Gal ≅ S₃` (`Gal.galActionHom_bijective_of_prime_degree'`) pushed up through the surjection
  `Gal.restrict_surjective`. Standard axioms only. (Pass-2 had assessed this "owed, route-plausible";
  Pass-3's probe verified every route step and the discharge went through — modulo a ℚ-algebra
  diamond on `Algebra ℚ (AlgebraicClosure ℚ)`, resolved by locally disabling `DivisionRing.toRatAlgebra`;
  see `NOTES.md`.)
- Introduced: Pass 1 (as prose) → tracked here Pass 2.   Discharged: **Pass 3**.

**Count: 0 open, 1 discharged (W1, Pass 3).**

---

## Pass log

### Pass 0 (2026-05-30) — orientation, inventory, seed lemma

Introduced **zero** axioms. This is the correct pass-0 outcome: there is nothing to stub yet, and
the one lemma proved (`Anabelian.fixingSubgroup_injective` and its absolute-Galois specialization in
`Anabelian/Basic.lean`) rests only on the three standard axioms. Verified:

```
'Anabelian.fixingSubgroup_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.absoluteGaloisGroup_fixingSubgroup_injective' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

Ledger delta: **0 / 0**. The floor is clean.

### Pass 1 (2026-05-30) — rung L1, finite-field absolute Galois group is commutative

Introduced **zero** axioms. The headline lemma `Anabelian.absoluteGaloisGroup_mul_comm` (and its
mixin instance `finiteField_absoluteGaloisGroup_isMulCommutative`) in `Anabelian/FiniteField.lean`
rests only on the three standard axioms. Verified:

```
'Anabelian.absoluteGaloisGroup_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.finiteField_absoluteGaloisGroup_isMulCommutative' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

Also (bookkeeping, no axioms): added the **Reclassification rule** + **Reclassification log** above,
and the per-target permitted-`FOUNDATIONAL` lists in `ROADMAP.md` (R1–R3).

Ledger delta: **0 / 0**.

### Pass 2 (2026-05-30) — rung L1, finite-field absolute Galois group is procyclic

Introduced **zero** axioms. `Anabelian.frobenius_zpowers_fixedField` and
`Anabelian.frobenius_topologicalClosure_eq_top` (Frobenius topologically generates `Gal(𝔽_q̄/𝔽_q)`)
in `Anabelian/FiniteField.lean` rest only on the three standard axioms. Verified:

```
'Anabelian.frobenius_zpowers_fixedField' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.frobenius_topologicalClosure_eq_top' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

Also (bookkeeping, no axioms): **Step 0** extended rule-2 in `CLAUDE.md` to load-bearing theorem
hypotheses, created the **Owed witnesses** section above, and entered **W1** (the `[Finite F]`
come-apart for the Pass-1/Pass-2 finite-field lemmas) as a tracked obligation.

Ledger delta: **0 DEBT / 0 FOUNDATIONAL**; Owed witnesses: **+1 (W1, open)**, 0 discharged.
Option (a) — discharging W1 by proving `Gal(ℚ̄/ℚ)` non-abelian — was assessed reachable in principle
(AbelRuffini's non-solvable, hence non-abelian, Galois group over ℚ + `restrictNormalHom_surjective`)
but requires splitting-field-into-`AlgebraicClosure` plumbing that is a separate construction; left
owed with that route recorded (see `NOTES.md`).

### Pass 3 (2026-05-30) — rung L1, discharge W1 (ℚ's absolute Galois group is non-abelian)

Introduced **zero** axioms; **discharged owed witness W1**.
`Anabelian.rationals_absoluteGaloisGroup_not_commutative` (`Anabelian/RationalsNonAbelian.lean`) —
`¬ ∀ σ τ : Field.absoluteGaloisGroup ℚ, σ * τ = τ * σ` — rests only on the three standard axioms.
Verified:

```
'Anabelian.rationals_absoluteGaloisGroup_not_commutative' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

Route (Pass-2 had recorded it as plausible): **Step 0 probe-verified every step** — `(X³-2)` is
irreducible (rational root theorem `isInteger_of_is_root_of_monic`), its Galois group is `≅ S₃`
(`Gal.galActionHom_bijective_of_prime_degree'`, needing 3 complex / ≤1 real roots), `S₃` is
non-abelian (`decide`), and the absolute Galois group surjects onto it (`Gal.restrict_surjective`,
which **is** `restrictNormalHom_surjective`). The anticipated "splitting-field embedding" plumbing
was unnecessary; the one real obstacle was a **ℚ-algebra diamond** (`DivisionRing.toRatAlgebra` vs
`AlgebraicClosure.instAlgebra`), resolved by locally disabling `DivisionRing.toRatAlgebra`.

Also (bookkeeping, no axioms): **Step 0** added the **Route-first-step rule** to the Owed-witnesses
convention above.

Ledger delta: **0 DEBT / 0 FOUNDATIONAL**; Owed witnesses: **−1 (W1 discharged)**; now **0 open**.

### Pass 4 (2026-05-30) — rung L1, residue-reduction faithfulness half

Introduced **zero** axioms; **no new owed witness**. `Anabelian/ResidueReduction.lean` proves
(standard axioms only) the faithfulness half of the abstract residue reduction:
`inertiaSubgroup_eq_reductionKer`, `mem_inertiaSubgroup_iff` (inertia = pointwise residue
stabilizer), `residueReduction_quotient_injective` (decomposition ⧸ inertia ↪ residue
automorphisms). Verified:

```
'Anabelian.inertiaSubgroup_eq_reductionKer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_inertiaSubgroup_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.residueReduction_quotient_injective' depends on axioms:
    [propext, Classical.choice, Quot.sound]
```

These are genuine-but-**light**: Mathlib's ramification API (`RamificationGroup.lean`) is
definition-only, so each is a short derivation. The substantive **surjectivity half** (reduction onto
the residue Galois group) is **absent from Mathlib** and logged as an L1 sub-target, not stubbed.
No load-bearing hypothesis (the results hold for any valuation subring) ⟹ no owed witness.

Step 0 (bookkeeping, no axioms): tracked **D1** (the ℚ-algebra diamond) as a structural-hygiene debt
in `ROADMAP.md`, to be fixed once before sustained number-field work; trigger = its second
recurrence. The diamond **did not reappear** this pass (the residue-reduction work is over an abstract
valued field `K`, with no concrete ℚ-algebra), so D1 stays at "first appearance, not yet triggered".

Ledger delta: **0 DEBT / 0 FOUNDATIONAL**; Owed witnesses: 0 added, **0 open**.

### Pass 5 (2026-05-30) — rung L1 inflection: the unramified quotient (first non-empty ledger)

The streak of zero-entry passes ends here, correctly: the easy/finite L1 fruit was harvested (P1–4),
and the residue surjection — the next L1 sub-target — needs structure theory **absent from Mathlib**.
After inventory (maximal-unramified Galois edifice = zero hits; only ingredients present), this pass
chose **option (B)**: import the residue surjection as a classified **`FOUNDATIONAL`** boundary
(`Anabelian.residueReduction_surjective`, entry above) and prove real downstream structure on it,
rather than option (A) (scaffold the construction) — because the surjection's content *is* the
unramified↔residue correspondence, leaving no clean strictly-lower `DEBT` to stub without the
cardinal sin.

`Anabelian/UnramifiedQuotient.lean` proves on that boundary (standard axioms + the one `FOUNDATIONAL`
entry, verified by in-file `#print axioms`):

```
'Anabelian.unramifiedQuotient_iso' depends on axioms:
    [propext, residueReduction_surjective, Classical.choice, Quot.sound]
'Anabelian.residue_procyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.unramifiedQuotient_procyclic' depends on axioms:
    [propext, residueReduction_surjective, Classical.choice, Quot.sound]
```

- `unramifiedQuotient_iso` (rests on the boundary) — `G_K ⧸ N ≃* Gal(𝓀̄/𝓀)` via the first iso
  theorem; `N` = kernel of the residue reduction (classically the inertia subgroup).
- `residue_procyclic` (standard only) — the residue Galois group is procyclic (Pass 2, `𝓀[K]` finite).
- `unramifiedQuotient_procyclic` (rests on the boundary + Pass 2) — the payoff: the unramified
  quotient of a local field's absolute Galois group is procyclic.

The `FOUNDATIONAL` posits *existence* of the surjection; identifying `N` with Pass 4's `inertiaSubgroup`
needs the (absent) valuation on `K̄` and is logged as remaining L1 work. **Not the cardinal sin**: the
boundary is strictly below R1 (a fact about a given field's Galois group, not reconstruction).

D1 (ℚ-algebra diamond) did **not** recur — the work is over a local field `K` and its *finite* residue
field `𝓀[K]`, with no `Algebra ℚ (AlgebraicClosure ℚ)` in play; D1 stays at "first appearance".

Ledger delta: **`FOUNDATIONAL` +1** (`residueReduction_surjective`), **`DEBT` +0**; Owed witnesses
0 added, 0 open.

### Pass 6 (2026-05-30) — rung L1 discipline-inversion: `Ẑ ↠ Gal(𝔽_q̄/𝔽_q)`, no new boundary

Introduced **zero** axioms; **added no second `FOUNDATIONAL`** — the explicitly disallowed outcome of
this pass (the `FOUNDATIONAL`-stacking trap). After the Pass-5 first boundary, the metric guard binds:
a rising `FOUNDATIONAL` count is not progress. Of the two permitted routes — (A) discharge
`residueReduction_surjective` into a theorem on strictly-lower `DEBT`, (Z) the `≅ Ẑ` residue-side
axiom-free — inventory found **(A) blocked** (the surjection's content *is* the unramified↔residue
correspondence; its lifting step is irreducibly absent from Mathlib, and the infrastructure below it
needs the absent valuation on `K̄`), so any "strictly-lower" `DEBT` would be the cardinal sin. Chose
**(Z)**.

`Anabelian/FiniteFieldZHat.lean` proves (standard axioms only — in-file `#print axioms` confirm):

```
'Anabelian.zhatToGalois_etaFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.zhatToGalois_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `zhatToGalois` — the canonical continuous hom `Ẑ → Gal(K̄/K)` (finite `K`), from the
  profinite-completion universal property (`ProfiniteGrp.ProfiniteCompletion.lift`) applied to
  `n ↦ Frobⁿ`.
- `zhatToGalois_surjective` — **it is surjective** (closed range ⊇ dense Frobenius powers, via Pass 2):
  the **surjective half** of `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`. The injective half (full iso) is genuinely
  multi-pass and logged as remaining L1 work in `ROADMAP.md`.

Active axioms unchanged: **1 `FOUNDATIONAL`** (`residueReduction_surjective`, Pass 5, untouched and
unused here), **0 `DEBT`**. Reclassification log stays empty (the boundary was not discharged —
honestly, because (A) is blocked, not avoided). D1 (ℚ-diamond) did **not** recur (finite fields,
no `Algebra ℚ (AlgebraicClosure ℚ)`).

Ledger delta: **0 / 0** (no `DEBT`, no new `FOUNDATIONAL`); axiom-free structural progress toward `≅ Ẑ`.

### Pass 7 (2026-05-30) — rung L1, finite levels of `≅ Ẑ`: `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n`

Introduced **zero** axioms; **added no second `FOUNDATIONAL`**. The preferred move was to **close the
whole** `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (route (i)), finishing Pass 6's surjective half with injectivity. Inventory
found this **not closable axiom-free this pass**: injectivity of `zhatToGalois` needs `Ẑ`'s presentation
as `lim ℤ/n` (Mathlib's `Ẑ = completion (Multiplicative ℤ)` is indexed by `FiniteIndexNormalSubgroup`,
not `ℤ/n`) and the cofinal inverse-system matching — genuinely multi-pass, absent off the shelf. Per
the route-(i) fallback, made **real axiom-free progress on the injective half** by closing its
per-level ingredient — and did **not** posit the iso as `FOUNDATIONAL` (closing-by-positing is the
stacking trap).

`Anabelian/FiniteGaloisCyclic.lean` (standard axioms only — in-file `#print axioms`):

```
'Anabelian.galoisFiniteField_mulEquivZMod' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `galoisFiniteField_mulEquivZMod` — for a finite extension `L/K` of finite fields,
  `Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L))` (cyclic of order the degree). A **complete**
  theorem (not a half); the per-level datum `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n` of `≅ Ẑ`'s injective half.

Honest: this is **genuine but modest** (short proof assembling `IsGalois.card_aut_eq_finrank` + the
finite-field `IsCyclic` instance + `zmodCyclicMulEquiv`); the **targeted whole `≅ Ẑ` is NOT closed**
this pass — only its per-level ingredient is, with the remaining gap (`Ẑ = lim ℤ/n` + cofinal matching)
logged in `ROADMAP.md`. Active axioms unchanged: **1 `FOUNDATIONAL`** (`residueReduction_surjective`,
unused here), **0 `DEBT`**. Reclassification log stays empty. D1 did **not** recur (finite fields).

Ledger delta: **0 / 0** — axiom-free; no `DEBT`, no new `FOUNDATIONAL`.
