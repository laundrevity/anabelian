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
| *(none)* | — | — | — | — |

**Count: 0 `FOUNDATIONAL`, 0 `DEBT`.** The project's sole non-standard axiom,
`Anabelian.residueReduction_surjective`, was **DISCHARGED into a proved `theorem` in Pass 20** (perfect
case; `#print axioms` standard-only on it and all downstream — `propext`/`Classical.choice`/`Quot.sound`).
This is the project's **first `DEBT`-discharged-into-theorem** — genuine progress, not a relabel. The
imperfect equal-characteristic case is a tracked remainder in `ROADMAP.md` (an *owed generality*, not an
axiom — nothing is assumed in the kernel). See the (now historical) entry + the Pass-20 log below.

### `Anabelian.residueReduction_surjective`   [DISCHARGED Pass 20 → `theorem`]   *(`FOUNDATIONAL` Passes 5–10, `DEBT` Passes 11–19)*
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
- Was `FOUNDATIONAL` (Passes 5–10): taken as an external boundary because the maximal-unramified
  edifice that proves it was assessed absent. **Pass 11 corrected that assessment** and reclassified to
  `DEBT` (committing to discharge in-project) — see below and the Reclassification log.
- **Discharge path (DEBT; bounded sub-plan; keystone PRESENT — revised Pass 12).** The hard step —
  the **lifting/surjectivity** — is **not** a wall and needs **no** maximal-unramified / `K^ur` /
  `IsKrasner` construction (Pass 11's route assumed it; Pass 12 corrected this): Mathlib proves the
  residue-reduction surjectivity directly in the profinite setting via
  **`Ideal.Quotient.stabilizerHom_surjective_of_profinite`** (`RingTheory/Invariant/Profinite.lean`)
  — for a profinite `G` acting continuously on a discrete `B/A` with `Algebra.IsInvariant A B G`,
  `stabilizer G Q ↠ Aut((B/Q)/(A/P))`. Apply with `G = Gal(K̄/K)`, `B = 𝒪[K̄]`, `A = 𝒪[K]`,
  `Q = 𝔪[K̄]`, `P = 𝔪[K]` (`stabilizer = ⊤`).
  **Keystone fit-verdict (Pass 13, route-first-step on the keystone):** two findings. (i) `B` must be
  **`DiscreteTopology`** — the keystone's topology on `B` is the *algebraic/Krull* (discrete) one with
  `ContinuousSMul` = open stabilizers, **not** the valuation topology; reframing, not a wall. (ii) `G =
  Gal(K̄/K)` profinite needs **`IsGalois K (AlgebraicClosure K)`** (verified ABSENT for general fields —
  `CompactSpace Gal(K̄/K)` fails without it; holds for perfect `K`, e.g. char-0 / mixed-char local
  fields, but **not** imperfect equal-char like `𝔽_q((t))`). A genuine **route prerequisite** to track.
  **Route pivot (Pass 13): use `B = integralClosure 𝒪[K] K̄` directly** (native to `ValuativeRel`) —
  this **avoids the `IsNonarchimedeanLocalField → NormedField` bridge and its watched diamond (no D2
  incurred)**; `spectralNorm` (P11–12) is a valid identification of the same ring but off the critical
  path. Steps:
  1. **`𝒪[K̄] = integralClosure 𝒪[K] K̄`. ✅ Pass 13** (`Anabelian/ResidueReductionIntegral.lean`):
     `galoisIntegers K` (the keystone's `B`).
  1b. **Galois `MulSemiringAction` on `𝒪[K̄]`. ✅ Pass 13**: `isIntegral_map_galois` (`σ` preserves
     integrality over `𝒪[K]`) ⟹ `galoisIntegers_isInvariant` (`IsInvariantSubring`) ⟹
     `IsInvariantSubring.toMulSemiringAction` — the `MulSemiringAction G B` the keystone consumes. (The
     P11–12 `spectralIntegers` analogue stands on the parallel valuation-ring track.)
  2a. **Fixed ring `𝒪[K̄]^Gal = 𝒪[K]`. ✅ Pass 14** (`Anabelian/ResidueReductionInvariant.lean`,
     perfect `K`): `galoisIntegers_algebraIsInvariant` — `Algebra.IsInvariant 𝒪[K] (integralClosure
     𝒪[K] K̄) Gal`, via `K̄^Gal = K` (`InfiniteGalois.fixedField_fixingSubgroup`) + integrality descent +
     `𝒪[K]` integrally closed. (Carries `[PerfectField K]`, the generality decision — see Job B below.)
  2b. **`DiscreteTopology B` + `ContinuousSMul G B`. ✅ Pass 15** (`Anabelian/ResidueReductionContinuity.lean`):
     `galoisStabilizer_isOpen` (stabilizers open, `stabilizer_isOpen_of_isIntegral`) ⟹
     `continuousSMul_galoisIntegers` (`continuousSMul_iff_stabilizer_isOpen`, discrete `B`).
  3. **Residue identification** (the blocker; Pass-15 verdict: **bounded multi-pass sub-plan, not a
     wall**): `Q = 𝔪[K̄]` over `P = 𝔪[K]`; **`B/Q ≅ AlgebraicClosure 𝓀[K]`**, `Aut = Gal(𝓀̄/𝓀) =
     Field.absoluteGaloisGroup 𝓀[K]`; `stabilizer = ⊤`. Decomposes:
     - 3a. `𝒪[K̄]` local + `𝔪[K̄]`. **Pass-17 three-route comparison by estimated pass-count** (target:
       `IsLocalRing`, NOT necessarily full `ValuationRing`): **(i) native `ValuationRing`** — needs the
       unique-extension-of-valuation-to-`K̄` theory; `ValuativeExtension` is compatibility-only (no
       construction of the `ValuativeRel` on `K̄`), so ~3 passes, no D2. **(ii) `spectralNorm`** —
       `Valued.integer K̄` is a `ValuationRing` ⟹ `IsLocalRing` **free**; only the bridge
       `integralClosure = Valued.integer K̄` (`spectralNorm x ≤ 1 ↔ IsIntegral 𝒪[K] x`) is real, and it
       is **reachable** (`spectralNorm = spectralValue ∘ minpoly` + `spectralValue_le_one_iff` + this
       pass's algebraic brick) — ~2 passes **+ a tracked D2**. **(iii) Henselian-local-direct** —
       `HenselianLocalRing` exists but the integral-closure-local fact + colimit to `K̄` are absent
       (`Henselian.lean` is the only `Henselian` file; `TFAE` is root-lifting only) — ~2–3 passes, no D2.
       **Decision: route (ii), incur the tracked D2** — by the cost principle (a bounded fix-once D2 is
       cheaper than 2–3 passes of foundational theory), (ii) is materially shortest (local-ness free +
       bridge reachable). **This REVERSES Pass 16's "stay native"** on new evidence (Pass 16 missed
       `spectralValue_le_one_iff` and the free `Valued.integer` local-ness — its (ii) estimate was
       wrong); a magnitude decision, not a D2-reflex. **✅ Pass 18** (`Anabelian/GaloisIntegersLocal.lean`,
       `isLocalRing_galoisIntegers`): brick 3a DONE via route (ii). The **D2 is incurred but localized
       entirely inside the proof** (a `letI` chain — `IsTopologicalAddGroup.rightUniformSpace`,
       `RankOne`, `Valued.toNontriviallyNormedField`, `spectralNorm.normedField K K̄`,
       `NormedField.toValued`); none leaks to the statement, so 2a/2b/3c are untouched (re-verified
       standard-axioms-only). `Valued.integer K̄` is local for free; the bridge `integralClosure 𝒪[K] K̄
       = Valued.integer K̄` (`spectralValue_le_one_iff` + Pass-17 brick + the agreement `‖a‖ ≤ 1 ↔ a ∈
       𝒪[K]`, which is `Iff.rfl` as `Valued.v = ValuativeRel.valuation K` and `mem_integer_iff` is `rfl`)
       transports local-ness along a `RingEquiv`. Standard-axioms-only. **`𝔪[K̄]` is now THE maximal
       ideal**, feeding 3c.
     - 3b. residue `𝓀̄` algebraic over `𝓀[K]` (residue classes lift to integral elements). [remaining]
     - 3c. `𝓀̄` algebraically closed. **✅ Pass 16** (`Anabelian/ResidueAlgClosed.lean`): the **general**
       fact `residueField_isAlgClosed_of_integrallyClosed` (residue field of an integrally-closed subring
       of an alg-closed field is alg-closed — a monic poly lifts to a monic over the subring, gets a root
       in `K̄`, integral ⟹ in the subring; **not** Hensel) + its two hypotheses discharged for `𝒪[K̄]`
       (`Subtype.coe_injective`; `galoisIntegers_integrallyClosed` = `𝒪[K̄]` integrally closed in `K̄`,
       via `isIntegral_trans` + `IsIntegralClosure.isIntegral_iff`) ⟹ `galoisResidueField_isAlgClosed`
       (residue field at **any** maximal ideal of `𝒪[K̄]` is alg-closed). **3c done modulo 3a** (consumes
       3a's maximal ideal). Route-independent, axiom-free, no D2.
     - 3d. `𝓀̄ ≅ AlgebraicClosure 𝓀[K]` (`isAlgClosure_iff` + `IsAlgClosure.equiv`). **supported**.
     - 3e. `Aut(𝓀̄/𝓀[K]) ≅ Field.absoluteGaloisGroup 𝓀[K]` (transport along 3d). supported.
  4. **Apply the keystone** `stabilizerHom_surjective_of_profinite`; reinterpret as
     `Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K]` surjective — **delete the `axiom`,
     replace with a `theorem`** (only then is the `DEBT` discharged). **KEYSTONE PRESENT** — *applied*,
     never posited.
- **Generality decision (Job B, Pass 14): option (a), narrow to the perfect case.** The keystone needs
  `Gal(K̄/K)` profinite = `IsGalois K K̄` (⟺ `K` perfect). The statement **is true** for imperfect `K`
  too (`Aut(K̄/K) ≅ Gal(K^sep/K)` as `K̄/K^sep` is rigid; residue field finite hence perfect), but the
  keystone *as applied* delivers only the perfect case. So the discharging `theorem` will carry
  `[PerfectField K]` (a documented **narrowing**, not a silent discharge), and the **imperfect
  equal-characteristic case is a tracked remainder** (`ROADMAP.md`), never dropped. Not yet enacted (the
  axiom is not yet removed); decided + recorded this pass.
- **`DEBT` status: DISCHARGED (Pass 20).** The full route is built and assembled: steps 1, 1b
  (`MulSemiringAction`), 2a (`Algebra.IsInvariant`), 2b (`DiscreteTopology`/`ContinuousSMul`), 3a
  (`𝒪[K̄]` local), 3b/3c/3d/3e + `IsLocalHom`/`LiesOver` (the residue iso `𝓀̄ ≅ AlgebraicClosure 𝓀[K]`,
  `galoisResidueAut`), then Step 4: `stabilizer G 𝔪[K̄] = ⊤` (the unique maximal ideal is Galois-stable,
  via `Ideal.pointwise_smul_eq_comap` + `comap_isMaximal_of_equiv` + `eq_maximalIdeal`) ⟹ apply
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite` ⟹ reinterpret (`stabilizer = ⊤` for the domain,
  `galoisResidueAut` for the codomain) ⟹ the surjection `Gal K →* Gal 𝓀[K]`. **The `axiom` was deleted
  and replaced by a `theorem`** (carrying `[PerfectField K]`) of the same statement. `#print axioms`:
  standard-only on the theorem and all downstream. **The surjection now *follows* — nothing posited.**
- **Not the cardinal sin (confirmed at the finish line):** L1, strictly **below** R1/R2/R3. The proof
  genuinely *applies* `stabilizerHom_surjective_of_profinite` to the assembled axiom-free bricks — it is
  not a re-posit, not circular, no hidden `sorry`/axiom (verified by the standard-only `#print axioms`).
- **Tracked remainder (owed generality, not an axiom):** the discharge carries `[PerfectField K]` (the
  keystone needs `Gal(K̄/K)` profinite = `IsGalois K K̄` ⟺ `K` perfect). The statement is **true** for
  imperfect equal-char `K` (`𝔽_q((t))`) too, via the separable-closure framing `Aut(K̄/K) ≅ Gal(K^sep/K)`
  — tracked in `ROADMAP.md`, never dropped. Nothing is assumed in the kernel for it.
- Introduced: Pass 5 (`FOUNDATIONAL`).   Reclassified `→ DEBT`: Pass 11.   **Discharged → `theorem`:
  Pass 20** (perfect case; imperfect case a tracked owed generality).

---

## Reclassification log

Dated record of every `DEBT ⇄ FOUNDATIONAL` class change (see the Reclassification rule above).

| date | axiom | old class | new class | reason |
|------|-------|-----------|-----------|--------|
| 2026-05-30 (Pass 11) | `Anabelian.residueReduction_surjective` | `FOUNDATIONAL` | `DEBT` | Pass 11 chose route (a) — discharge the boundary — and **began the construction** axiom-free (`Anabelian/SpectralValuation.lean`: the spectral valuation ring `𝒪[K̄]` + Galois-invariance, the foundational strictly-lower brick of the discharge route). The Pass-6 "valuation on `K̄` irreducibly absent" assessment was **corrected**: `spectralNorm.normedField` + `NormedField.toValued` (`Valued K̄`) and `IsKrasner` (lifting) are PRESENT. This is the legitimate `FOUNDATIONAL → DEBT` direction (committing to prove in-project, not relabeling a debt as a boundary); it is **not** paper — construction is begun and the route's first step is probe-verified. Genuinely below R1, so not the cardinal sin. |

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

### Pass 8 (2026-05-30) — rung L1: the `Ẑ`-side inverse-system presentation of `≅ Ẑ`

Introduced **zero** axioms; **added no second `FOUNDATIONAL`**. The designated job was to **close**
`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (bijectivity of Pass 6's `zhatToGalois`). Inventory found closure **not reachable
this pass** — and **corrected Pass 7's inventory**: the general "profinite = limit of finite
quotients" machinery is in fact **PRESENT** (`ProfiniteGrp.Limits`: `toLimit`, `toLimit_injective`,
`isoLimittoFiniteQuotientFunctor`, `proj`, `continuousMulEquivLimittoFiniteQuotientFunctor`), and
`etaFn_injective_iff_residuallyFinite` is about the **unit** `η`, not `zhatToGalois`. The decisive
blocker is the **Galois side**: no `𝔽_{q^n}` as a `FiniteGaloisIntermediateField` of
`AlgebraicClosure K` (only standalone `GaloisField p n`), so the level projection
`Gal(K̄/K) → Gal(𝔽_{q^n}/𝔽_q)` — needed on every injectivity route — is genuinely absent. Per the
permitted not-closed outcome, made **real axiom-free progress on the actual injective-half machinery**
(the `Ẑ`-side inverse-system presentation) and sharpened the remainder into a numbered sub-plan
(`ROADMAP.md`); the iso was **NOT posited**.

`Anabelian/ZHatProcyclic.lean` proves (standard axioms only — in-file `#print axioms`):

```
'Anabelian.zhat_topologicalClosure_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.zhat_quotient_isCyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `zhat_topologicalClosure_eq_top` — **`Ẑ` is procyclic** (`zhatGen = η(ofAdd 1)` topologically
  generates `Ẑ`): the `Ẑ`-side analogue of Pass 2's `frobenius_topologicalClosure_eq_top` for `Gal`.
- `zhat_quotient_isCyclic` — **every finite quotient of `Ẑ` is cyclic**: with the point-separating
  projections (`toLimit_injective`), this presents `Ẑ` as the inverse limit of finite **cyclic**
  groups, matching `Gal`'s `ℤ/n` system (Pass 7) — the `Ẑ`-side of the injectivity square.

Active axioms unchanged: **1 `FOUNDATIONAL`** (`residueReduction_surjective`, Pass 5, unused here),
**0 `DEBT`**. Reclassification log stays empty. D1 (ℚ-diamond) did **not** recur (the work is over `Ẑ`
and `Multiplicative ℤ`, no `Algebra ℚ (AlgebraicClosure ℚ)`).

Ledger delta: **0 / 0** — axiom-free; no `DEBT`, no new `FOUNDATIONAL`.

### Pass 9 (2026-05-30) — rung L1: the Galois-side level subfields `𝔽_{q^n}` (`≅ Ẑ` sub-plan, infra)

Introduced **zero** axioms; **added no second `FOUNDATIONAL`**. Executed Pass 9 of the `≅ Ẑ` sub-plan:
built the one absent Galois-side ingredient (`𝔽_{q^n} ⊆ K̄` + level projection `r_n` + Frobenius-aligned
generator). **Graded as infrastructure, not a closed whole** — `≅ Ẑ` is **not** closed (injectivity =
the Pass-10 cofinality/diagram chase) and **nothing was posited**. Every piece is finite-field-concrete
and built from scratch.

`Anabelian/FiniteFieldLevel.lean` (standard axioms only — in-file `#print axioms`):

```
'Anabelian.levelField_finrank' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.levelRestrict_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.levelRestrict_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.orderOf_levelRestrict_frobenius' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `levelField K n` (= `fixedField (zpowers (Frob^n))`), `mem_levelField`, `levelField_finite`,
  `levelField_finrank` (degree exactly `n`, via carrier = rootSet of separable `X^(q^n)−X`, card `q^n`),
  `levelFGIF K n` (the `FiniteGaloisIntermediateField` bundle).
- `levelRestrict K n` (= `restrictNormalHom`, the `r_n`), `levelRestrict_surjective`.
- **Frobenius alignment (the trap, handled):** `levelRestrict_frobenius`:
  `r_n (Frob) = frobeniusAlgEquivOfAlgebraic K (levelField K n)`; `orderOf_levelRestrict_frobenius`:
  `orderOf (r_n Frob) = n`. So `r_n` sends the *absolute* Frobenius (`= zhatToGalois (η (ofAdd 1))`,
  Pass 6) to the Frobenius generator of `Gal(𝔽_{q^n}/K)`, **not** an arbitrary `zmodCyclicMulEquiv`
  generator — exactly what Pass 10's commuting square consumes.

Active axioms unchanged: **1 `FOUNDATIONAL`** (`residueReduction_surjective`, Pass 5, unused here),
**0 `DEBT`**. Reclassification log stays empty. D1 (ℚ-diamond) did **not** recur (finite fields and
their algebraic closure; no `Algebra ℚ (AlgebraicClosure ℚ)`). Load-bearing hypothesis `NeZero n` is
genuine (for `n = 0` the level field is all of `K̄`, infinite) but is not a rule-2 come-apart claim
(no `structure`/`class`); no owed witness.

Ledger delta: **0 / 0** — axiom-free; no `DEBT`, no new `FOUNDATIONAL`.

### Pass 10 (2026-05-30) — rung L1: **`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` CLOSED** (first L1 whole of depth)

Introduced **zero** axioms; **added no second `FOUNDATIONAL`**. This pass **closes** the
topological-group isomorphism `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`, axiom-free — the capstone of the Pass 6–9 sub-plan
and the project's **first closed L1 whole of real depth**. Nothing was posited anywhere in the
Pass 6–10 chain; the iso is earned.

`Anabelian/FiniteFieldZHatIso.lean` (standard axioms only — in-file `#print axioms`):

```
'Anabelian.zhatToGalois_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisContinuousMulEquivZHat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `zhatToGalois_injective` — `ker zhatToGalois = ⊥`. Via the **cofinality core** `ker_levelComp_le`:
  for `χ_m := r_m ∘ zhatToGalois` (`levelComp`), the dense `⟨zhatGen⟩` meets the *open* `ker χ_m` in
  exactly `⟨zhatGen^m⟩` (`χ_m (zhatGen^k) = 1 ↔ m ∣ k`, using Pass 9's `orderOf (r_m Frob) = m`), so
  `ker χ_m = closure⟨zhatGen^m⟩` (`IsOpen.inter_closure` + Pass 8 density). Then separation
  (`exist_openNormalSubgroup_sub_open_nhds_of_one`) + Lagrange (`pow_card_eq_one'`) finish.
- `galoisContinuousMulEquivZHat` — **`Gal(𝔽_q̄/𝔽_q) ≃ₜ* Ẑ`**: `zhatToGalois` bijective (injective +
  Pass 6 surjective) ⟹ homeomorphism (`Continuous.homeoOfEquivCompactToT2`) ⟹ `ContinuousMulEquiv`.

The uniqueness/cofinality "crux" the Pass-9 setup flagged needed **no absent machinery**: the
`DiscreteTopology Gal(𝔽_{q^m}/K)` instance (`krullTopology_discreteTopology_of_finiteDimensional`)
makes `ker χ_m` open, and `ker χ_m = closure⟨zhatGen^m⟩` replaces an explicit unique-subgroup lemma.

Active axioms unchanged: **1 `FOUNDATIONAL`** (`residueReduction_surjective`, Pass 5, untouched and
unused here), **0 `DEBT`**. **Sub-target `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`: DONE.** Reclassification log stays empty.
D1 (ℚ-diamond) did **not** recur (finite fields). No new `structure`/`class`; no owed witness.

Ledger delta: **0 / 0** — axiom-free; no `DEBT`, no new `FOUNDATIONAL`.

### Pass 11 (2026-05-30) — rung L1 inflection: route (a), begin discharging the one boundary

**The inflection decision (the deliverable).** Pass 10 banked `≅ Ẑ`; the danger was breadth-without-depth
(opening clean fragments while the one boundary sat undischarged — the IUT-Stage-1 replay). The fork was
**(a) begin discharging `residueReduction_surjective`** vs **(b) open an independent deep sub-target**.
Resolved by the **common-prerequisite finding**: the valuation on `K̄` gates *both* — (a) needs it for
`𝓀[K̄]`/the reduction map; (b)'s ramification filtration is defined *via* the valuation and sits *on* the
residue reduction (and is itself absent). So (b) is no independent escape. Combined with a **tractability
correction** (Pass 6's "valuation on `K̄` absent" was wrong: `spectralNorm.normedField`/`NormedField.toValued`
give `Valued K̄`, and `IsKrasner` is the lifting machinery — all PRESENT), **(a) is the highest-leverage
move.** Chose (a).

**Built (axiom-free, strictly-lower):** `Anabelian/SpectralValuation.lean` —

```
'Anabelian.spectralIntegers' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.spectralIntegers_mem_iff_galois' depends on axioms: [propext, Classical.choice, Quot.sound]
```

the spectral valuation ring `𝒪[K̄]` (closed unit ball, a `Subring (AlgebraicClosure K)`) and the fact
`Gal(K̄/K)` preserves it — the foundational brick of the discharge route (route step 1).

**Ledger move:** **reclassified `residueReduction_surjective` `FOUNDATIONAL → DEBT`** (Reclassification
log, first entry) — a genuine commitment backed by begun construction, not paper. **Count: `1 FOUNDATIONAL
/ 0 DEBT` → `0 FOUNDATIONAL / 1 DEBT`.** This is the first pass to *raise* `DEBT`, which is the intended
*good* direction for route (a) (you cannot discharge what you never commit to). **No second `FOUNDATIONAL`;
nothing cardinal-sin posited** (the lifting/surjectivity — the irreducible heart — is untouched, never
stubbed; only strictly-lower valuation infrastructure was built).

D1 (ℚ-diamond) did **not** recur (the work is over an abstract nonarch normed field and its algebraic
closure; no `Algebra ℚ (AlgebraicClosure ℚ)`). No new `structure`/`class` (no rule-2 obligation). No owed
witness. Recovers nothing from an abstract group.

Ledger delta: **`DEBT` +1 (via `FOUNDATIONAL → DEBT` reclassification), `FOUNDATIONAL` −1; no new axiom.**

### Pass 12 (2026-05-30) — rung L1, route (a): the lifting is NOT a wall (keystone present)

**Primary deliverable — the lifting-tractability verdict.** Pass 11 flagged the **lifting** (the heart
of `residueReduction_surjective`, Pass-6-feared "irreducibly absent") as unverified. Front-loaded it:
**verdict — NOT a wall.** Mathlib proves the residue-reduction surjectivity directly in the profinite
setting via **`Ideal.Quotient.stabilizerHom_surjective_of_profinite`** (`RingTheory/Invariant/Profinite.lean`):
for profinite `G` acting continuously on discrete `B/A` with `Algebra.IsInvariant A B G`,
`stabilizer G Q ↠ Aut((B/Q)/(A/P))`. Assembled from the finite level (`exists_of_isInvariant` /
`stabilizerHom_surjective`, the arithmetic Frobenius) via the same profinite-limit machinery that
closed `≅ Ẑ`. **Corrects Pass 11's route:** the maximal-unramified / `K^ur` edifice is **not** needed,
and `IsKrasner` is field-*generation* (not Galois-lifting). The discharge is a **bounded** sub-plan
with the hardest step PRESENT.

**Built (strictly-lower, axiom-free):** `Anabelian/ResidueReductionRoute.lean` —

```
'Anabelian.spectralIntegers_isInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`spectralIntegers_isInvariant` (`IsInvariantSubring (Gal(K̄/K)) 𝒪[K̄]`, from Pass 11's invariance) ⟹
the `MulSemiringAction (Gal(K̄/K)) 𝒪[K̄]` the keystone consumes (route step 1b).

**`DEBT` status: OPEN — not discharged** (the `axiom residueReduction_surjective` is still present;
discharge happens only when it is deleted and replaced by a `theorem`). **Route-steps remaining:
[Step 2: `Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal` framing (discrete + continuous); Step 3: residue
identification `𝓀̄/𝓀` + `stabilizer = ⊤`; Step 4: apply `stabilizerHom_surjective_of_profinite`].**

**No new axiom; no reclassification; ledger unchanged at `0 FOUNDATIONAL / 1 DEBT`.** Nothing
cardinal-sin posited — the surjection is supplied by a present theorem to be *applied*, never stubbed.
D1 (ℚ-diamond) did **not** recur (abstract nonarch normed field + algebraic closure). No new
`structure`/`class` (no rule-2 obligation). Recovers nothing from an abstract group.

Ledger delta: **0 / 0** (no axiom change; a strictly-lower axiom-free brick + the route revision).

### Pass 13 (2026-05-30) — rung L1, route (a): keystone fit-verdict + route pivot to `integralClosure`

**Keystone fit-verdict (primary; route-first-step on `stabilizerHom_surjective_of_profinite`).** Probed
its exact hypotheses. Two findings: (i) `B` must be **`DiscreteTopology`** (the algebraic/Krull setup,
`ContinuousSMul` = open stabilizers — **not** the valuation topology; reframing, not a wall); (ii) `G =
Gal(K̄/K)` profinite needs **`IsGalois K (AlgebraicClosure K)`**, verified **ABSENT for general fields**
(`CompactSpace Gal(K̄/K)` fails without it) — holds for perfect `K` (char-0/mixed-char local fields), not
imperfect equal-char (`𝔽_q((t))`). A genuine route prerequisite, now tracked.

**Route pivot.** Use `B = integralClosure 𝒪[K] K̄` directly (native to `ValuativeRel`), which **avoids the
`IsNonarchimedeanLocalField → NormedField` bridge and its watched diamond — so NO D2 is incurred**. The
`spectralNorm` ring (P11–12) is the same object on a parallel track, off the critical path.

**Built (strictly-lower, axiom-free, over the exact `IsNonarchimedeanLocalField` setting):**
`Anabelian/ResidueReductionIntegral.lean` —

```
'Anabelian.isIntegral_map_galois' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisIntegers_isInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`galoisIntegers K` (the keystone's `B = 𝒪[K̄] = integralClosure 𝒪[K] K̄`); `isIntegral_map_galois` (`σ ∈
Gal(K̄/K)` preserves integrality over `𝒪[K]`); `galoisIntegers_isInvariant` (`IsInvariantSubring` ⟹ the
`MulSemiringAction G B` the keystone consumes) — route step 1b, on the keystone's actual ring.

**`DEBT` status: OPEN — NOT discharged** (the `axiom residueReduction_surjective` is still present).
**Route-steps remaining: [Step 2 `Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal` + discrete + `ContinuousSMul` +
`IsGalois K K̄` prerequisite; Step 3 residue `𝒪[K̄]/𝔪 ≅ AlgebraicClosure 𝓀[K]` + `Aut` + `stabilizer = ⊤`;
Step 4 apply keystone, delete axiom].** No new axiom; no reclassification; ledger unchanged at
**`0 FOUNDATIONAL / 1 DEBT`**. Nothing cardinal-sin posited (surjection supplied by a present theorem,
to be applied). D1 N/A (local field). **D2 NOT incurred** (integral-closure route avoids the
`NormedField` bridge). No new `structure`/`class` (no rule-2 obligation). Recovers nothing from an
abstract group.

Ledger delta: **0 / 0** (no axiom change; strictly-lower axiom-free bricks + the keystone fit-verdict +
route pivot).

### Pass 14 (2026-05-30) — rung L1, route (a): fixed-ring `𝒪[K̄]^Gal = 𝒪[K]` + the generality decision

**Job B — generality decision (primary, not optional).** Investigated whether
`residueReduction_surjective` holds for imperfect `K`: **yes, true as stated** (`Aut(K̄/K) ≅ Gal(K^sep/K)`
since `K̄/K^sep` is purely inseparable/rigid; residue field finite hence perfect; standard unramified
theory), but the keystone `stabilizerHom_surjective_of_profinite` needs `Gal(K̄/K)` literally profinite
= `IsGalois K K̄` (⟺ `K` perfect). **Decision: option (a) — narrow to the perfect case** when the
discharge lands (carry `[PerfectField K]`, document the narrowing, **track the imperfect equal-char case
as a named remainder** in `ROADMAP.md`); not enacted yet (axiom not removed), only decided + recorded.

**Job A — built (strictly-lower, axiom-free, perfect case):** `Anabelian/ResidueReductionInvariant.lean` —

```
'Anabelian.galoisIntegers_algebraIsInvariant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`galoisIntegers_algebraIsInvariant` — `Algebra.IsInvariant 𝒪[K] (integralClosure 𝒪[K] K̄) Gal`
(`𝒪[K̄]^Gal = 𝒪[K]`), step-2 core of the keystone's hypotheses, via `K̄^Gal = K`
(`InfiniteGalois.fixedField_fixingSubgroup`) + integrality descent (`isIntegral_algebraMap_iff`) +
`𝒪[K]` integrally closed (`IsIntegrallyClosed.isIntegral_iff`, `K = Frac 𝒪[K]`).

**`DEBT` status: OPEN — NOT discharged.** The `axiom residueReduction_surjective` is still present.
**Discharge blocker (re-confirmed): `𝒪[K̄]/𝔪[K̄] ≅ AlgebraicClosure 𝓀[K]`** (residue of `K̄` = alg
closure of `𝓀`) is **ABSENT from Mathlib** and substantial. **Route-steps remaining: [Step 2b
`DiscreteTopology` + `ContinuousSMul`; Step 3 residue iso (ABSENT blocker) + `stabilizer = ⊤`; Step 4
apply keystone, delete axiom with perfect-case narrowing].** Steps 1, 1b, 2a done.

No new axiom; no reclassification; ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. Nothing
cardinal-sin posited (no sub-step stubbed; surjection supplied by a present theorem to be applied). D1
N/A; **D2 not incurred** (integral-closure route). No new `structure`/`class` (no rule-2 obligation).
Recovers nothing from an abstract group.

Ledger delta: **0 / 0** (strictly-lower axiom-free brick + the generality decision; axiom remains the
single open `DEBT`).

### Pass 15 (2026-05-30) — rung L1, route (a): Step 2b (`ContinuousSMul`) + residue-iso verdict

**Primary — residue-iso tractability verdict.** Front-loaded the pinpointed blocker `𝒪[K̄]/𝔪[K̄] ≅
AlgebraicClosure 𝓀[K]`. **Verdict: a BOUNDED multi-pass sub-plan, not a wall.** Decomposes into 3a
(`𝒪[K̄]` local + `𝔪[K̄]`, ABSENT/substantial — via the valuation-integral-closure API, NOT `spectralNorm`
which re-introduces the D2 bridge), 3b (residue algebraic, moderate), 3c (residue **algebraically
closed**, ABSENT/substantial — monic-over-`𝒪[K̄]` root in alg-closed `K̄` is integral; **not** Hensel,
`K̄` is not complete), 3d (`≅ AlgebraicClosure` via `isAlgClosure_iff` + `IsAlgClosure.equiv`,
**supported**), 3e (`Aut` transport, supported). Discharge ~2–3 passes away.

**Built (strictly-lower, axiom-free) — Step 2b:** `Anabelian/ResidueReductionContinuity.lean` —

```
'Anabelian.galoisStabilizer_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.continuousSMul_galoisIntegers' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`galoisStabilizer_isOpen` (every stabilizer of the Galois action on `𝒪[K̄] = integralClosure 𝒪[K] K̄`
is open, via `stabilizer_isOpen_of_isIntegral`) ⟹ `continuousSMul_galoisIntegers` (with the discrete
topology on `𝒪[K̄]`, `ContinuousSMul Gal 𝒪[K̄]`, via `continuousSMul_iff_stabilizer_isOpen`) — the
keystone's `DiscreteTopology B` + `ContinuousSMul G B` hypotheses, now discharged.

**`DEBT` status: OPEN — NOT discharged** (axiom still present). **Route-steps remaining: [Step 3a–3c
(the residue iso — `𝒪[K̄]` local/`𝔪[K̄]`, residue algebraic, residue alg-closed); Step 3d/3e (supported);
Step 4 apply keystone + delete axiom (perfect-case)].** Done: 1, 1b, 2a (P13–14), 2b (P15).

No new axiom; no reclassification; ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. Nothing
cardinal-sin posited (no sub-step stubbed; residue iso to be built, surjection to be applied). D1 N/A;
**D2 not incurred** (the `spectralNorm` re-entry for 3a is flagged as a D2 risk to avoid). No new
`structure`/`class` (no rule-2). Recovers nothing from an abstract group.

Ledger delta: **0 / 0** (Step-2b bricks axiom-free + the residue-iso verdict; axiom remains the single
open `DEBT`).

### Pass 16 (2026-05-30) — rung L1, route (a): brick 3c (residue field alg-closed) + the D2-fork decision

**Primary — the 3a route-first-step probe + the explicit D2-fork decision.** Probed the
valuation-extension-to-`K̄` API underpinning brick **3a** (`𝒪[K̄]` local). Findings: (i) `NormedField K`
is **not** a global instance for `IsNonarchimedeanLocalField K` (only a scoped `Valued.toNormedField`),
so the native valuation theory is what's available; (ii) 3a's local-ness **reduces** to
"`integralClosure 𝒪[K] K̄` is a `ValuationRing`" — found `ValuationRing.isLocalRing` is a **free**
instance — but that `ValuationRing` fact (unique extension of a complete DVR's valuation to `K̄`) is
**ABSENT** from Mathlib in both routes; (iii) the `spectralNorm` route's bridge `spectralNorm x ≤ 1 ↔
IsIntegral 𝒪[K] x` is **also absent**. **Decision (logged): native `ValuativeRel` route, D2 NOT
incurred** — `spectralNorm` offers no shortcut for 3a, so taking on the `NormedField`-bridge diamond
buys nothing. 3a deepened to a genuine from-scratch valuation-extension construction (the single
substantial remaining gate), beyond Pass 15's "substantial".

**Built (strictly-lower, axiom-free, route-independent) — brick 3c:** `Anabelian/ResidueAlgClosed.lean` —

```
'Anabelian.residueField_isAlgClosed_of_integrallyClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisIntegers_integrallyClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisResidueField_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `residueField_isAlgClosed_of_integrallyClosed` — **the general 3c lemma:** if `R` is a subring of an
  algebraically closed field `L` (injective `algebraMap`) and integrally closed in `L`, then `R ⧸ m` is
  algebraically closed for **any** maximal `m`. Proof: monic `p` over `R ⧸ m` lifts to monic `P` over `R`
  of the same degree (`lifts_and_natDegree_eq_and_monic`); `P` over the alg-closed `L` has a root `r`
  (`IsAlgClosed.exists_root`); `r` integral over `R` (root of monic `P`) ⟹ `r ∈ R`; `r mod m` is a root
  of `p` (`IsAlgClosed.of_exists_root`). **Uses `L` alg-closed + integral-closedness, NOT Henselianness.**
- `galoisIntegers_integrallyClosed` — `𝒪[K̄]` is integrally closed in `K̄` (`isIntegral_trans` +
  `IsIntegralClosure.isIntegral_iff`): the general lemma's `hcl` hypothesis for the real ring.
- `galoisResidueField_isAlgClosed` — **brick 3c for `𝒪[K̄]`**: the general lemma applied to `R = 𝒪[K̄]`,
  `L = K̄` (injectivity = `Subtype.coe_injective`). 3c **done modulo 3a** (it supplies the maximal ideal).

**`DEBT` status: OPEN — NOT discharged** (the `axiom residueReduction_surjective` is still present).
**Route-steps remaining: [Step 3a `𝒪[K̄]` local = `integralClosure` is a `ValuationRing` (the one
substantial gate, native route, no D2); Step 3b residue algebraic; Step 3d/3e (supported); Step 4 apply
keystone + delete axiom, perfect-case narrowing].** Done: 1, 1b, 2a (P13–14), 2b (P15), **3c (P16)**.

No new axiom; no reclassification; ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. Nothing
cardinal-sin posited (3c is **proved**, not stubbed; the residue iso is being *built*, the surjection to
be *applied* from a present theorem). D1 N/A; **D2 not incurred** (native route; `spectralNorm` re-entry
rejected — no shortcut). No new `structure`/`class` (no rule-2 obligation). Recovers nothing from an
abstract group.

Ledger delta: **0 / 0** (brick 3c axiom-free + the D2-fork decision; axiom remains the single open
`DEBT`).

### Pass 17 (2026-05-30) — rung L1, route (a): the 3a three-route comparison + the bridge's algebraic half

**Primary — the 3a route comparison by estimated pass-count, across three routes** (target: *local-ness*
= `IsLocalRing` with maximal ideal the valuation's `𝔪[K̄]`, NOT necessarily full `ValuationRing`):
- **(i) native `ValuationRing`** — needs unique-extension-of-valuation-to-`K̄`. Probe: `ValuativeExtension`
  (`ValuativeRel/Basic.lean:1292`) is **compatibility-only** (assumes `[ValuativeRel B]`, does not
  construct it); no canonical `ValuativeRel (AlgebraicClosure K)`. **~3 passes, no D2.**
- **(ii) `spectralNorm` (tracked D2)** — `Valued.integer K̄` is a `ValuationRing` ⟹ `IsLocalRing` **free**
  (`ValuationSubring → ValuationRing → IsLocalRing`); `Padics/Complex.lean` is the template. Only the
  **bridge** `integralClosure 𝒪[K] K̄ = Valued.integer K̄` (`spectralNorm x ≤ 1 ↔ IsIntegral 𝒪[K] x`) is
  real, and **reachable**: `spectralNorm = spectralValue ∘ minpoly` (`SpectralNorm.lean:379`) +
  **`spectralValue_le_one_iff`** (`:202`) + this pass's algebraic brick. **~2 passes + tracked D2.**
- **(iii) Henselian-local-direct** — `HenselianLocalRing` exists (`Henselian.lean:108`) but `grep
  Henselian` hits only that file; `TFAE` is root-lifting only (no integral-closure-local), and even
  `HenselianLocalRing 𝒪[K]` doesn't synth. Needs base-Henselian + integral-closure-local (absent) +
  colimit (absent). **~2–3 passes, no D2.**

**Decision (logged): route (ii), incur the tracked D2.** By the cost principle — a bounded, fix-once D2
diamond (logged like D1) is **cheaper than 2–3 passes of from-scratch valuation/Henselian theory** —
route (ii) is materially shortest (local-ness free + bridge reachable). **This REVERSES Pass 16's "stay
native, D2 not incurred"**, legitimately and on new evidence: Pass 16 grepped only `spectralNorm.*le_one`
(missing `spectralValue_le_one_iff`) and had not found that `Valued.integer` gives local-ness for free,
so its magnitude estimate for (ii) was wrong. A magnitude decision, **not** a D2-reflex (opposite of P16).

**Built (strictly-lower, axiom-free, D2-free):** `Anabelian/GaloisIntegersLocal.lean` —

```
'Anabelian.isIntegral_iff_minpoly_coeff_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`isIntegral_iff_minpoly_coeff_mem` — for `x : K̄`, `IsIntegral 𝒪[K] x ↔ ∀ i, (minpoly K x).coeff i ∈
𝒪[K]` — the **algebraic half** of route (ii)'s bridge. Forward:
`minpoly.isIntegrallyClosed_eq_field_fractions` (`𝒪[K]` integrally closed, `K = Frac 𝒪[K]`); reverse:
lift via `Polynomial.toSubring` (+ `monic_toSubring`, `aeval_map_algebraMap`, `map_toSubring`). Norm-free
⟹ **D2-free**; D2 is deferred to exactly the spectral steps that need the norm. (Note: local-ness cannot
be finished purely algebraically — the non-units-form-an-ideal step needs the multiplicative ultrametric
`spectralNorm`, which is why route (ii)'s D2 is unavoidable.)

**`DEBT` status: OPEN — NOT discharged** (the `axiom residueReduction_surjective` is still present).
**Route-steps remaining: [3a route (ii): (a) D2 setup ⟹ `IsLocalRing (Valued.integer K̄)`; (b) bridge
`integralClosure = Valued.integer K̄` (algebraic half ✅ this pass); (c) transport ⟹ 3a; 3b residue
algebraic; 3d/3e supported; Step 4 apply keystone + delete axiom].** Done: 1, 1b, 2a, 2b, 3c-modulo-3a,
**bridge algebraic half (this pass)**. **Nothing cardinal-sin posited** — 3a is being *built*; no `DEBT`
posits `𝒪[K̄]` local / a `ValuationRing` / the residue iso.

No new axiom; no reclassification; ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. D1 N/A; **D2:
decided to be incurred via route (ii)** (the reversal above) — not yet incurred in code (this pass's
brick is norm-free), logged not silent. No new `structure`/`class` (no rule-2). Recovers nothing from an
abstract group.

Ledger delta: **0 / 0** (the route comparison + D2 decision + the bridge's algebraic-half brick;
axiom remains the single open `DEBT`).

### Pass 18 (2026-05-30) — rung L1, route (a): brick 3a (`𝒪[K̄]` local) DONE + the D2 incursion

**Brick 3a DONE.** `Anabelian.isLocalRing_galoisIntegers : IsLocalRing ↥(integralClosure ↥𝒪[K]
(AlgebraicClosure K))` — the last substantial gate of the residue iso — proved via route (ii), the
`spectralNorm` route chosen Pass 17. Standard-axioms-only (in-file `#print axioms`):

```
'Anabelian.isLocalRing_galoisIntegers' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Proof shape: (a) `Valued.integer K̄` for the spectral `Valued` on `K̄` is a `ValuationRing` ⟹
`IsLocalRing` **for free**; (b) the **bridge** `integralClosure 𝒪[K] K̄ = Valued.integer K̄` via the
membership iff `IsIntegral 𝒪[K] x ↔ x ∈ Valued.integer K̄` (`spectralValue_le_one_iff` +
`spectralNorm = spectralValue ∘ minpoly` + Pass-17's `isIntegral_iff_minpoly_coeff_mem` + the
agreement); (c) transport along a `RingEquiv` (`RingEquiv.isLocalRing`). With 3a, `𝔪[K̄]` is THE
maximal ideal of `𝒪[K̄]`, so 3c (`galoisResidueField_isAlgClosed`) gives `𝓀̄` algebraically closed.

**D2 — the `NormedField`-bridge diamond: INCURRED this pass, LOCALIZED + logged (parallel to D1).**
This is the first incursion of D2 (watched Passes 13–17). It is contained exactly as D1 was (D1 used
`attribute [-instance] DivisionRing.toRatAlgebra in <decl>`):
- **Localization mechanism:** the entire spectral/normed setup is a `letI`/`haveI` chain **inside the
  proof of `isLocalRing_galoisIntegers`** — `letI := IsTopologicalAddGroup.rightUniformSpace K`;
  `haveI := isUniformAddGroup_of_addCommGroup`; `letI : (Valued.v (R := K)).RankOne := …`;
  `letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)`;
  `letI : NormedField K̄ := spectralNorm.normedField K K̄`; `letI : Valued K̄ ℝ≥0 := NormedField.toValued`.
  None appears in the **statement** (which is pure `ValuativeRel`: `IsLocalRing ↥(integralClosure
  ↥𝒪[K] K̄)`), so none leaks to any other declaration.
- **The agreement lemma (the fix-once band-aid):** `‖a‖ ≤ 1 ↔ a ∈ 𝒪[K]` reconciling the
  `NormedField`-derived norm with the `ValuativeRel` valuation is **`Iff.rfl`** here, because
  `Valued.v = ValuativeRel.valuation K` (`rfl`, `Topology/Algebra/Valued/ValuativeRel.lean`) and
  `Valuation.mem_integer_iff` is `rfl`. So the diamond is *reconcilable, not a clash* — the spectral
  norm's unit ball on `K` IS the `ValuativeRel` `𝒪[K]`, definitionally.
- **No global instance; not silent:** no `NormedField K`/`Valued K̄` instance is registered globally;
  the incursion is logged here and in `ROADMAP.md` (D2 section). `synthInstance.maxHeartbeats` is
  raised (400000, commented) for the `IsLocalRing (Valued.integer K̄)` search, which is expensive
  under `import Mathlib` + the Anabelian instances — a search-cost matter, not a logical axiom.
- **Re-verification (the primary discipline):** `lake build` is clean (8493 jobs) and 2a
  (`galoisIntegers_algebraIsInvariant`), 2b (`continuousSMul_galoisIntegers`), 3c
  (`galoisResidueField_isAlgClosed`) **still typecheck against the same `𝒪[K]` and remain
  standard-axioms-only** — confirmed by their `#print axioms`. The D2 setup changed nothing in them.

This file uses **`import Mathlib`** (sanctioned fallback, noted): 3a's proof spans the `spectralNorm`,
`Valued`/`NormedValued`, `IsUltrametricDist`, `Valued.integer`/`ValuationRing` APIs across many modules
with uncertain paths/transitive instances.

**`DEBT` status: OPEN — NOT discharged** (the `axiom residueReduction_surjective` is still present).
**Route-steps remaining: [3b residue algebraic; 3d/3e `≅ AlgebraicClosure 𝓀[K]` + `Aut` (supported);
Step 4 apply keystone + delete axiom (perfect-case)].** Done: 1, 1b, 2a, 2b, 3c, **3a (this pass)**.
**Nothing cardinal-sin posited** — 3a is *proved*, not stubbed; no `DEBT` posits `𝒪[K̄]` local / the
residue iso / the surjection. The discharge is ~2 passes out.

No new axiom; no reclassification; ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. D1 N/A; **D2:
incurred, localized, logged** (this pass; a hygiene debt, not a logical axiom — `#print axioms` stays
standard-only). No new `structure`/`class` (no rule-2). Recovers nothing from an abstract group.

Ledger delta: **0 / 0** (brick 3a axiom-free + the localized-D2 incursion; axiom remains the single
open `DEBT`).

### Pass 19 (2026-05-30) — rung L1, route (a): the residue identification (3b/3c/3d/3e) — clean partial

**Built the residue identification + connective tissue** (`Anabelian/ResidueIso.lean`), standard-axioms-
only (in-file `#print axioms`):

```
'Anabelian.galoisIntegers_isLocalHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisResidueEquiv'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisResidueAut'          depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `galoisIntegers_isLocalHom` (**connective tissue**) — `algebraMap 𝒪[K] 𝒪[K̄]` is a `IsLocalHom`:
  `(𝔪[K̄]).comap` is maximal (`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`) hence `= 𝔪[K]`
  (`eq_maximalIdeal`, local), = `local_hom_TFAE` clause 4 ⟹ clause 0. Unlocks `(𝔪[K̄]).LiesOver (𝔪[K])`
  (the keystone's `Q.LiesOver P`) and `Algebra 𝓀[K] 𝓀̄` **for free**.
- `galoisResidueEquiv` (**3b + 3d**) — `𝓀̄ := ResidueField 𝒪[K̄] ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K]`. 3b
  (`Algebra.IsAlgebraic 𝓀[K] 𝓀̄`) element-wise (reduce a lifted monic minpoly: `aeval_map_algebraMap` +
  `aeval_algHom_apply`); with 3c (`IsAlgClosed 𝓀̄`), `IsAlgClosure 𝓀[K] 𝓀̄` ⟹ `IsAlgClosure.equiv`.
- `galoisResidueAut` (**3e**) — `Aut(𝓀̄/𝓀[K]) ≃* Field.absoluteGaloisGroup 𝓀[K]` via `AlgEquiv.autCongr`.

These need **no `PerfectField`** (only Step 4 does). `IsLocalRing 𝒪[K̄]` (3a) is registered as a
`local instance` so the residue-field statements elaborate.

**Step-4 distance (probed, for honesty).** `stabilizerHom_surjective_of_profinite (𝔪[K]) (𝔪[K̄])`
**typechecks** applied to `G = Gal(K̄/K)`, `B = 𝒪[K̄]`, `A = 𝒪[K]` — the only instance it can't
auto-synth is `ContinuousSMul G 𝒪[K̄]`, which is exactly Pass-2b's `continuousSMul_galoisIntegers`
(supply it via `haveI`). So the discharge is **~1 pass out**: keystone application (typechecks) +
`stabilizer G 𝔪[K̄] = ⊤` (pointwise-ideal-maximality + local uniqueness) + the reinterpretation
(`G ≃* stabilizer` via `stabilizer = ⊤`; `B/Q = 𝓀̄`, `A/P = 𝓀[K]` defeq; `galoisResidueAut`) + deleting
the axiom for a `[PerfectField K]` theorem.

**`DEBT` status: OPEN — NOT discharged** (the `axiom residueReduction_surjective` is still present).
This is a **clean partial**: the residue identification is complete; **Step 4 was deliberately NOT
half-assembled** (a half-built Step 4 is worse than a clean partial). **Nothing cardinal-sin posited** —
every brick is *proved*; the surjection is to be *applied* from the present keystone, never stubbed.

No new axiom; no reclassification; ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. D1 N/A; **D2**:
3a's localized incursion (in `GaloisIntegersLocal`) unchanged; this pass introduces **no further D2**
(residue-field/`IsAlgClosure` API is quotient-/`ValuativeRel`-native). `synthInstance.maxHeartbeats`
raised (commented) for one `IsAlgClosure.equiv` search — search-cost, not logical. No new
`structure`/`class` (no rule-2). Recovers nothing from an abstract group. Uses `import Mathlib`
(sanctioned fallback, noted).

Ledger delta: **0 / 0** (the residue-identification bricks axiom-free; axiom remains the single open
`DEBT`, now ~1 pass from discharge).

### Pass 20 (2026-05-30) — rung L1: **THE DISCHARGE.** `residueReduction_surjective`: `DEBT → theorem`

**The project's first (and only) `DEBT` discharged into a proved theorem.** `1 DEBT → 0`.

**Step-4 assembly** (`Anabelian/UnramifiedQuotient.lean`, the `axiom` deleted, a `theorem` in its
place):
- **`ContinuousSMul` plumbing:** `letI : TopologicalSpace 𝒪[K̄] := ⊥`; `DiscreteTopology` (`⟨rfl⟩`);
  `continuousSMul_galoisIntegers K` (Pass 2b); `galoisIntegers_algebraIsInvariant K` (Pass 2a).
- **`stabilizer G 𝔪[K̄] = ⊤`:** `Subgroup.eq_top_iff'` + `MulAction.mem_stabilizer_iff`; then `σ • 𝔪[K̄]
  = (𝔪[K̄]).comap (toRingAut σ).symm` (`Ideal.pointwise_smul_eq_comap`) is maximal
  (`comap_isMaximal_of_equiv`, an instance) so `= 𝔪[K̄]` (`IsLocalRing.eq_maximalIdeal`) — `𝒪[K̄]` local
  (3a) gives uniqueness.
- **Keystone:** `Ideal.Quotient.stabilizerHom_surjective_of_profinite (𝔪[K]) (𝔪[K̄])` — all hypotheses
  in hand; `Gal(K̄/K)` profinite via `[PerfectField K]` ⟹ `IsGalois K K̄`. Gives
  `Surjective (stabilizerHom 𝔪[K̄] 𝔪[K] G : ↥(stabilizer) →* (𝒪[K̄]/𝔪[K̄]) ≃ₐ[𝒪[K]/𝔪[K]] (𝒪[K̄]/𝔪[K̄]))`.
- **Codomain identification (defeq, no transport needed):** `𝒪[K̄]/𝔪[K̄] = ResidueField 𝒪[K̄] = 𝓀̄`,
  `𝒪[K]/𝔪[K] = 𝓀[K]`, and both algebras are `Ideal.Quotient.algebraOfLiesOver` — so the keystone's
  codomain *is* `galoisResidueAut`'s domain `𝓀̄ ≃ₐ[𝓀[K]] 𝓀̄`; `galoisResidueAut K` (3e) maps it to
  `Field.absoluteGaloisGroup 𝓀[K]`.
- **Domain identification:** `ι : Gal K →* ↥(stabilizer)`, `σ ↦ ⟨σ, by rw [hstab]; mem_top⟩`, surjective
  (`fun τ => ⟨τ.1, Subtype.ext rfl⟩`).
- **The surjection** `φ = (galoisResidueAut K).toMonoidHom ∘ stabilizerHom ∘ ι`; surjective as a
  composition of two bijections (`galoisResidueAut`, `ι`) with the surjective keystone.

**Discharge-moment checklist (all five run):**
1. **Statement preserved:** the `theorem` states `∃ φ : Field.absoluteGaloisGroup K →*
   Field.absoluteGaloisGroup 𝓀[K], Function.Surjective φ`, with `[PerfectField K]` added — identical
   existence claim, not weakened/vacuous.
2. **`#print axioms` standard-only, theorem AND downstream:** `residueReduction_surjective`,
   `unramifiedQuotient_iso`, `residue_procyclic`, `unramifiedQuotient_procyclic` all
   `[propext, Classical.choice, Quot.sound]`. `residueReduction_surjective` is **gone** from every audit
   as an axiom; **no new axiom** replaced it. Project-wide: **zero `axiom` declarations**.
3. **Anti-circularity:** the proof *applies* `stabilizerHom_surjective_of_profinite` to the assembled
   axiom-free bricks — not a re-posit, not circular, no hidden `sorry`/axiom (confirmed standard-only).
4. **Narrowing propagation:** `[PerfectField K]` added to `unramifiedQuotient_iso`/`_procyclic` (they
   call the theorem); `residue_procyclic` left as-is (independent, no `PerfectField` needed — not
   over-constrained). Docstrings updated. Imperfect case = tracked remainder in `ROADMAP.md`.
5. **Ledger `1 DEBT → 0`:** recorded `0 FOUNDATIONAL / 0 DEBT`.

D1 N/A. **D2** unchanged: 3a's localized incursion (in `GaloisIntegersLocal`) is the only D2; Step 4
adds none (it works over the discrete topology + the existing instances). `synthInstance`/`maxHeartbeats`
raised (commented) for the heavy keystone instance/elaboration searches — search-cost, not logical
(`#print axioms` standard-only). No new `structure`/`class` (no rule-2). **Recovers nothing from an
abstract group** — the surjection is a map between the Galois groups of *given* fields (`K`, `𝓀[K]`),
not a reconstruction; R1–R3 remain distant and untouched.

Ledger delta: **`DEBT` −1 (discharged into a theorem); `FOUNDATIONAL` 0.** Headline:
**`0 FOUNDATIONAL / 1 DEBT` → `0 FOUNDATIONAL / 0 DEBT`.** The project's first `DEBT`-discharged-into-
theorem — the genuine progress signal the discipline exists to produce.

### Pass 21 (2026-06-10) — rung L1, post-discharge: the named residue reduction + `ker = inertia`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Executed the first of the two
Pass-20-pointer options: **(a) tie `N` (the residue-reduction kernel) to the inertia subgroup** —
chosen over (b) opening L2 because L2's filtration *sits on* this identification (`G_0` *is* the
inertia subgroup; an anonymous existential kernel cannot anchor a filtration), so (a) gates (b).

**The Pass-20 discharge was an existential** (`∃ φ, Surjective φ`) — the concrete map was buried in
the proof. `Anabelian/GaloisInertia.lean` names it and identifies its kernel (in-file `#print axioms`,
all standard-only):

```
'Anabelian.galoisIntegers_stabilizer_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisToStabilizer'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisToStabilizer_surjective'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.residueReductionHom'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.residueReductionHom_surjective'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisInertia'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_galoisInertia_iff'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_residueReductionHom'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.galoisInertia_normal'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.unramifiedQuotientEquiv'         depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `galoisIntegers_stabilizer_eq_top` — **decomposition = ⊤** (extracted from the Pass-20 proof as a
  named lemma; no `PerfectField`).
- `residueReductionHom : Gal(K̄/K) →* Gal(𝓀̄/𝓀)` — **THE residue reduction, named** (`galoisResidueAut
  ∘ stabilizerHom ∘ galoisToStabilizer`); the *map* needs **no `PerfectField`** — only surjectivity
  does (`residueReductionHom_surjective`, the Pass-20 keystone assembly restated for the named map;
  `residueReduction_surjective` in `UnramifiedQuotient.lean` is now its one-line existential corollary).
- `galoisInertia : Subgroup (Field.absoluteGaloisGroup K)` — **the inertia subgroup, named**:
  Mathlib's `Ideal.inertia` of `𝔪[K̄]` = `{σ | ∀ b ∈ 𝒪[K̄], σ b − b ∈ 𝔪[K̄]}` (the classical
  `v(σx − x) > 0`; Serre, *Local Fields*, ch. IV §1).
- **`ker_residueReductionHom` — the identification `ker = galoisInertia`, the headline.** Rests on
  Mathlib's `Ideal.Quotient.ker_stabilizerHom` (**found by inventory, not reproved** — the Pass-21
  probe discovered `Ideal.inertia` + `ker_stabilizerHom` + `map_ker_stabilizer_subtype` are PRESENT
  in `RingTheory/Ideal/Over.lean`) + `stabilizer = ⊤` + injectivity of `galoisResidueAut`.
  **Unconditional — no `PerfectField`** (the identification holds for the map, surjective or not).
- `galoisInertia_normal` — inertia is normal in the full `Gal(K̄/K)` (it is a kernel). Unconditional.
- `unramifiedQuotientEquiv [PerfectField K]` — **the classical unramified-quotient theorem in its
  standard form**: `Gal(K̄/K) ⧸ galoisInertia K ≃* Gal(𝓀̄/𝓀)` — upgrading Pass 5/20's `∃ N, …`
  (`unramifiedQuotient_iso`) to the concrete named statement.

**Honesty.** Connective, not a new hard theorem: the surjectivity was earned in Passes 11–20 and the
kernel lemma is Mathlib's; the pass's content is the *correct packaging* (named map, named kernel,
single group-instance path — a real Lean-architecture constraint: the `AlgEquiv.aut` vs derived-`Group`
instance mismatch forced `galoisInertia` to be typed over `Field.absoluteGaloisGroup K`) plus the
honest closing of the Pass-5 "tie `N` to inertia" sub-target. The *literal*
`ValuationSubring.inertiaSubgroup`-form translation is **deliberately not pursued** (it would put the
spectral `Valued` structure on `K̄` into *statements* — a statement-level D2 incursion); the
`Ideal.inertia` form is canonical for the project. **Continuity** of `residueReductionHom` (it is a
map of profinite groups) is true but not proved — logged as remaining L1 refinement in `ROADMAP.md`.

No new `structure`/`class` (no rule-2 model obligation). No new owed witness (`[PerfectField K]` on
the two surjectivity-dependent results is the *tracked owed generality* — we claim the statement is
true *without* it — not a load-bearing-hypothesis claim). D1 N/A (no `Algebra ℚ (AlgebraicClosure ℚ)`).
**D2 unchanged** (3a's localized incursion only; `Ideal.inertia` is valuation-free). File-wide
`synthInstance.maxHeartbeats` raise (commented) — the same stabilizer/`MulAction (Gal K) (Ideal 𝒪[K̄])`
search cost as Pass 20; search-cost, not logical. Recovers nothing from an abstract group; R1–R3
untouched.

Ledger delta: **0 / 0** — axiom-free; no `DEBT`, no `FOUNDATIONAL`; the Pass-5 sub-target
"tie `N` to the inertia subgroup" is **closed**.

### Pass 22 (2026-06-10) — L2 opening verdict: naive lower numbering DEGENERATE (proved) + the `Ẑ` payoff

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. The planned L2 opening —
define `G_i := (𝔪[K̄]^(i+1)).inertia Gal(K̄/K)` on the absolute group and prove antitone/normal —
was **refuted in-pass before being committed**, and the refutation is the deliverable
(`Anabelian/RamificationDegeneracy.lean`, in-file `#print axioms` all standard-only):

```
'Anabelian.maximalIdeal_galoisIntegers_sq'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.maximalIdeal_galoisIntegers_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.inertia_maximalIdeal_pow_collapse'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.unramifiedQuotientZHat'             depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`maximalIdeal_galoisIntegers_sq` — `𝔪[K̄]² = 𝔪[K̄]`** (idempotent): every `x ∈ 𝔪[K̄]` has a
  square root in the algebraically closed `K̄`, integral (monic `T² − x` + transitivity), a non-unit,
  hence in `𝔪[K̄]`; so `x ∈ 𝔪²`. (Divisible value group ⟹ no minimal positive valuation.)
- `maximalIdeal_galoisIntegers_pow_eq` — `𝔪[K̄]^n = 𝔪[K̄]` (`n ≠ 0`).
- **`inertia_maximalIdeal_pow_collapse` — the would-be `G_i` all equal `G_0 = galoisInertia K`.**
  The naive definition would compile and its "theorems" (antitone, normal) would hold **vacuously**
  — the groups never come apart for distinct `i`. This is the rule-2 discipline applied *preemptively*:
  the come-apart failure is **proved** (a constructible witness, the project's currency), not asserted,
  and the vacuous `structure`-free definition was never committed.
- **Corrected L2 architecture recorded in `ROADMAP.md`** (Serre, *Local Fields*, ch. IV): lower
  numbering lives at **finite levels** `L/K` (DVR `𝒪_L` — `Ideal.inertia` on `𝔪_L^(i+1)` is still the
  right device, at the right level); the absolute-group filtration is **upper numbering** via Herbrand
  `φ`/`ψ` (which is exactly what survives the limit — the degeneracy is the lower numbering's failure
  to, seen at the limit). Mathlib gaps re-verified (Pass 22): `RamificationGroup.lean` still the entire
  ramification API (definition-only); no Herbrand; no finite-extension-of-local-field instances.
- **The `Ẑ` payoff** (`UnramifiedQuotient.lean`): `unramifiedQuotientZHat [PerfectField K] :
  Gal(K̄/K) ⧸ galoisInertia K ≃* Ẑ` — the quantitative unramified-quotient theorem, a two-line
  assembly of Pass 21's `unramifiedQuotientEquiv` and Pass 10's `galoisContinuousMulEquivZHat` at the
  (finite) residue field. Group form only (the topological form awaits the logged continuity
  refinement); stated for `K : Type` — a universe artifact of the Pass 6–10 `ProfiniteGrp` packaging,
  documented in the docstring, not mathematics.

No new `structure`/`class`; no new owed witness; D1 N/A; **D2 unchanged** (no valuation on `K̄` in any
statement). Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. L2 status: **architecture fixed (degenerate route closed,
proved); finite-level content NOT-STARTED.**

### Pass 23 (2026-06-10) — rung L2 OPENED: lower-numbering ramification filtration + basic theory

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Fills (at project level) the
literal Mathlib TODO in `RingTheory/Valuation/RamificationGroup.lean` — *"Define higher ramification
groups in lower numbering"* — in that file's own `ValuationSubring` setting (Pass 4's setting), on the
Pass-22-corrected architecture: the filtration is developed **with the separation hypothesis
explicit**, because both regimes are now proved (Pass 22: collapse at idempotent `𝔪[K̄]`; this pass:
separation under Krull). `Anabelian/RamificationFiltration.lean` (in-file `#print axioms`, all
standard-only):

```
'Anabelian.ramificationGroup'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_ramificationGroup_iff'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smul_mem_maximalIdeal_pow'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_antitone'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_zero'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_normal'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.iInf_ramificationGroup_eq_bot'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.iInf_ramificationGroup_eq_bot_of_isNoetherianRing'
                                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_notMem_ramificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `ramificationGroup K A i` — **`G_i` in lower numbering** (Serre IV §1): `Ideal.inertia` of
  `𝔪_A^(i+1)` under the decomposition-group action (the Pass-21 device, at the non-degenerate level).
  ℕ-indexed, `G_0` = inertia; Serre's `G_{−1}` = the ambient decomposition group.
- `smul_mem_maximalIdeal_pow` — the crux: the action preserves `𝔪_A^n` (ring automorphisms of a local
  ring fix `𝔪` setwise — `map_isMaximal_of_equiv` + `eq_maximalIdeal` + `Ideal.map_pow`).
- `ramificationGroup_antitone`; **`ramificationGroup_zero : G_0 = inertiaSubgroup`** (ties the
  filtration base to Mathlib's/Pass-4's inertia via `residue_smul` + `mem_inertiaSubgroup_iff`);
  **`ramificationGroup_normal`** (normal in the decomposition group, Serre IV §1 Prop. 1).
- **`iInf_ramificationGroup_eq_bot`** — separation under the explicit Krull hypothesis
  `⨅ 𝔪_A^n = ⊥`: a `σ` in every `G_i` fixes `A` pointwise hence all of `L` (valuation-subring
  dichotomy `mem_or_inv_mem`) hence `= 1`. **Discharged in the Noetherian case**
  (`iInf_ramificationGroup_eq_bot_of_isNoetherianRing`, via Mathlib's Krull intersection
  `Ideal.iInf_pow_eq_bot_of_isLocalRing`) — Noetherian valuation ring = field-or-DVR, exactly the
  finite-level regime. Plus the per-element escape (`exists_notMem_ramificationGroup`).

**Honesty.** The hypothesis-parametrized shape is *forced* by Pass 22, and **no claim is made that the
Krull hypothesis is irremovable from the separation conclusion** (that would need a constructed `A`
with non-separating powers *and* a nontrivial inertia element — not attempted; no rule-2 obligation
incurred, none dodged: `ramificationGroup` is a `Subgroup`-valued `def`, not a `structure`/`class`).
The named remaining L2 work (in `ROADMAP.md`): a **concrete properly-decreasing chain** (`G_0 ≠ G_1`
for an explicitly ramified extension — the come-apart exhibit the definition eventually deserves),
eventual triviality for finite decomposition groups, the tame/wild structure, Herbrand/upper
numbering, and the local-field instantiation `A = 𝒪_L` (blocked on the re-verified-absent
finite-extension `IsNonarchimedeanLocalField` instances).

No new `structure`/`class`; no new owed witness; D1 N/A; **D2 N/A** (the file is
`ValuationSubring`-native — no spectral structure anywhere). Recovers nothing from an abstract group;
R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **L2: lower numbering defined + basic theory proved** (the
rung's first real content).

### Pass 24 (2026-06-10) — rung L2: the tame character `θ₀ : G₀ →* 𝓀ˣ` (hom + kernel) + eventual triviality

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. The first structurally rich
L2 theorem (Serre IV §2, the level-0 map), scoped *up front* to the hom + kernel half — injectivity
deliberately not claimed (see Honesty). `Anabelian/TameCharacter.lean` + the warm-up appended to
`RamificationFiltration.lean` (in-file `#print axioms`, all standard-only):

```
'Anabelian.exists_ramificationGroup_eq_bot'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smulUnit'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_smul_uniformizer_eq'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameUnit_spec' / '_unique'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.residue_smul_eq_of_mem_ramificationGroup_zero'    — standard-only
'Anabelian.tameCharacter'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameCharacter_eq_one'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameQuotientHom'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameCharacter_eq_of_span_eq'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameCharacterOfIrreducible'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Setting:** a uniformizer `π` (`𝔪_A = (π)`, `π ≠ 0`) — exactly what a DVR supplies
  (`tameCharacterOfIrreducible` is the DVR entry point via `irreducible_iff_uniformizer`).
- `tameUnit` — `σπ = π·u_σ` with `u_σ` a *unique* unit (`σ` preserves `(π)` both ways ⟹
  `π ∣ σπ ∣ π` ⟹ `associated_of_dvd_dvd`).
- **`tameCharacter : G_0 →* 𝓀ˣ`** — the cocycle `(στ)π = π·u_σ·σ(u_τ)` is a *crossed* homomorphism
  in general; it straightens to an honest one **because inertia fixes residues** (`σ(u_τ) ≡ u_τ`)
  — the mathematical reason `θ₀` is defined on `G_0`, not the decomposition group.
- **`tameCharacter_eq_one` — `G_1 ≤ ker θ₀`** (`σπ − π = π(u_σ−1) ∈ (π²)`, cancel `π`), giving
  **`tameQuotientHom : G_0/G_1 →* 𝓀ˣ`** (`QuotientGroup.lift`; normality from Pass 23).
- **`tameCharacter_eq_of_span_eq`** — uniformizer-independence (`u'_σ = w⁻¹·u_σ·σ(w)`, inertia
  fixes `w`'s residue): `θ₀` is **canonical**.
- **`exists_ramificationGroup_eq_bot`** — eventual triviality for finite decomposition groups under
  separation (closes the Pass-23 logged epsilon): per-element escape indices are finitely many,
  bound them, antitone finishes. (Lean note: the `whnf`-timeout trap here was an un-annotated
  anonymous constructor inside a one-liner `exact`; restructured with `Set.finite_range.bddAbove`.)

**Honesty.** **Injectivity of `G_0/G_1 →* 𝓀ˣ` is NOT claimed or attempted** — classically it needs
`σ ∈ G_i` to be detectable on `π` alone (`v(σπ−π) ≥ i+1 ⟹ σ ∈ G_i`), which requires the
totally-ramified subextension to be monogenic (Serre IV §1 Prop. 5; from completeness/Eisenstein) —
genuinely absent at the bare-`ValuationSubring` abstraction level. That, with its corollaries
(`G_0/G_1` abelian/cyclic) and wild `G_1` pro-`p`, is the named next L2 rung. The `𝔪 = (π)`/`π ≠ 0`
hypotheses are used *constructively* to build the map (not claimed-essential-for-a-theorem) — no
rule-2 obligation incurred. No new `structure`/`class`; no new owed witness; D1 N/A; **D2 N/A**
(`ValuationSubring`-native). Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **L2: the tame character exists, is canonical, and kills
`G_1`** — the first map out of the filtration.

### Pass 25 (2026-06-10) — rung L2: tame injectivity `G₀/G₁ ↪ 𝓀ˣ` under explicit monogenicity

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Completes the level-0
quotient structure (Serre IV §2 Prop. 7 at `i = 0`) **conditionally on an explicit monogenicity
hypothesis** — the Pass-23 Krull pattern: the input Mathlib cannot yet discharge is named in the
binders, never assumed silently. Pre-pass housekeeping: the 2026-05-31 orphaned-session incident
was resolved (12 uncommitted files discarded, user decision — see the NOTES.md incident entry) and
the commit-per-pass convention added to `CLAUDE.md`. `Anabelian/TameInjectivity.lean` (in-file
`#print axioms`, all standard-only):

```
'Anabelian.smul_sub_dvd_of_mem_closure'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_ramificationGroup_of_smul_uniformizer_sub_mem'
                                                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_tameCharacter'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameQuotientHom_injective'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameQuotient_mul_comm'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameQuotient_isCyclic'                    depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Setting:** Pass 24's (`𝔪_A = (π)`, `π ≠ 0`) plus the **monogenicity hypothesis**: an
  inertia-fixed `A₀ : Subring ↥A` with `Subring.closure (↑A₀ ∪ {π}) = ⊤` (i.e. `A = A₀[π]`).
  Monogenicity is a true theorem for `A = 𝒪_L` (complete DVR, separable residue extension — Serre
  IV §1 Prop. 5's own proof) and **absent from Mathlib as a general lemma** (re-verified this
  pass: only `PowerBasis.adjoin_gen_eq_top`-adjacent machinery) — so it enters as a *named
  hypothesis*, not an axiom.
- `smul_sub_dvd_of_mem_closure` — the engine: `(σπ − π) ∣ (σx − x)` for every
  `x ∈ closure (A₀ ∪ {π})`, by `Subring.closure_induction` (the induction *is* Serre's
  telescoping; the `mul` case is `σ(xy) − xy = σx·(σy − y) + (σx − x)·y`).
- **`mem_ramificationGroup_of_smul_uniformizer_sub_mem`** — **detection on `π`** (Serre IV §1
  Prop. 5, monogenic form): `σπ − π ∈ 𝔪^(i+1) ⟹ σ ∈ G_i` (divide, land via
  `Ideal.mul_mem_right`). Stated for all `i` — also the engine for the future `i ≥ 1` additive
  story.
- **`ker_tameCharacter` — `ker θ₀ = G₁`** (as `(G₁).subgroupOf G₀`): `⊇` is Pass 24's
  `tameCharacter_eq_one`; `⊆` reads `θ₀(σ) = 1` as `u_σ ≡ 1 mod 𝔪`, whence
  `σπ − π = π(u_σ − 1) ∈ 𝔪²`, and detection at `i = 1` finishes.
- **`tameQuotientHom_injective` — `G₀/G₁ ↪ 𝓀ˣ`** (`QuotientGroup.ker_lift` + the kernel
  identification + `QuotientGroup.map_mk'_self`).
- Corollaries: **`tameQuotient_mul_comm`** (`G₀/G₁` abelian — injects into `𝓀ˣ`) and
  **`tameQuotient_isCyclic`** (finite `G₀` ⟹ `G₀/G₁` cyclic, via
  `isCyclic_of_injective_ringHom` into the residue field).

**Honesty.** The monogenicity hypothesis is **not claimed irremovable** from any conclusion — no
constructed non-monogenic counterexample is attempted, so per the extended rule-2 no
load-bearing claim is made and no owed witness is incurred (none dodged; the hypothesis is used
constructively — the Pass-23 Krull precedent). **Discharging the hypothesis** for `A = 𝒪_L`
(`L/K` finite) is the named follow-on, blocked on the (verified absent) finite-extension
`IsNonarchimedeanLocalField` instances. The `i ≥ 1` additive analogues (`G_i/G_{i+1} ↪ 𝓀⁺`) are
named, not attempted. No new `structure`/`class`; no new owed witness; D1 N/A; **D2 N/A**
(`ValuationSubring`-native). Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **L2: the tame quotient `G₀/G₁ ↪ 𝓀ˣ` is a proved embedding
(monogenicity-conditional), abelian, and cyclic when `G₀` is finite.**

### Pass 26 (2026-06-10) — rung L2: the come-apart exhibit — `G₀ ≠ G₁`, constructed (obligation discharged)

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Discharges the obligation
logged since Pass 23 ("the come-apart exhibit the definition deserves"): a fully concrete
`(K, L, A)` where the ramification filtration **provably decreases at the first step** — the
rule-2 currency (a constructed witness, not prose) applied to the L2 definition itself, the
separating counterpart of Pass 22's proved collapse. `Anabelian/RamificationExhibit.lean`
(in-file `#print axioms`, all standard-only):

```
'Anabelian.laurentNegXAlgEquiv'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.maximalIdeal_laurentIntegers_eq_span'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.laurentNegX_mem_decompositionSubgroup'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.laurentNegXDecomp_mem_ramificationGroup_zero'
                                                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.laurentNegXDecomp_notMem_ramificationGroup_one'
                                                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.laurentRamificationGroup_zero_ne_one'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_zero_ne_one_rat'         depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **The exhibit:** `L = k⸨X⸩` (Mathlib's `X`-adic `Valued` instance), `A = {v ≤ 1} ≅ k⟦X⟧`
  (`laurentIntegers`, membership = "is a power series" via `val_le_one_iff_eq_coe`), `K = k`
  the constants, and `σ : f(X) ↦ f(−X)` — `PowerSeries.evalNegHom` lifted along the localization
  `k⸨X⸩ = k⟦X⟧[X⁻¹]` (`IsLocalization.lift`; an involution, hence a `k`-algebra equivalence).
  The classical tame quadratic picture (`k⸨X⸩/k⸨X²⸩`, `e = 2`) with the base enlarged to the
  constants — which only enlarges `L ≃ₐ[K] L`; the membership facts are identical.
- `maximalIdeal_laurentIntegers_eq_span` — **`𝔪_A = (π)`, `π = X`** (constant-coefficient
  unit-detection both ways), `π ≠ 0`: the uniformizer package of Passes 24–25, instantiated
  concretely for the first time.
- **`σ ∈ G₀`** — `σ` moves every integer by a constant-term-zero series, i.e. by an element of
  `(π)`.
- **`σ ∉ G₁`** (`(2 : k) ≠ 0`) — **detected by Pass 24's tame character**: `σπ = π·(−1)` gives
  `tameUnit σ = −1` (`tameUnit_unique`), so `θ₀(σ) = −1`; `G₁`-membership would force
  `θ₀(σ) = 1` (`tameCharacter_eq_one`), and `−1 = 1` in `𝓀` pushes down (via
  `ofPowerSeries_injective` at the constant coefficient) to `2 = 0` in `k`. The exhibit
  *exercises* the Pass-24/25 tame structure: `θ₀` is exactly the invariant that sees the jump.
- **`laurentRamificationGroup_zero_ne_one`** — `G₀ ≠ G₁` for `(k, k⸨X⸩, A)`, `(2 : k) ≠ 0`; and
  **`ramificationGroup_zero_ne_one_rat`** — the **fully closed witness** at `k = ℚ`: no
  hypotheses, no variables.

**Honesty.** This pass discharges an obligation rather than incurring one. NOT claimed: anything
about the rest of the ambient filtration (`G₁ ≠ ⊥` here — wild automorphisms live in the large
decomposition group; the classical `G₀ ⊃ G₁ = ⊥` chain for the quadratic subextension needs the
subfield `k⸨X²⸩` and is named, not attempted). No new `structure`/`class`; no new owed witness;
D1 N/A; **D2 N/A** (the `Valued` structure on `k⸨X⸩` is Mathlib's own canonical instance on a
concrete type — nothing imposed, nothing leaking into the abstract files). Recovers nothing from
an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **L2: the filtration provably comes apart — `G₀ ≠ G₁`,
witnessed over `ℚ⸨X⸩` with every hypothesis closed.**

### Pass 27 (2026-06-10) — rung L2: the additive characters `θ_i : G_i →* 𝓀⁺` (`i ≥ 1`) + the `i = 0` failure witness

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Completes the
finite-level quotient structure across **all** levels (Serre IV §2 Prop. 7): with Pass 24's
multiplicative `θ₀` at level 0, every quotient `G_i/G_{i+1}` now carries its classical character
— additive for `i ≥ 1` — an **embedding** under the Pass-25 monogenicity hypothesis (whose
detection engine covered all `i`, as designed). The `1 ≤ i` gate is **claimed load-bearing and
the claim is discharged in-pass** by a constructed counterexample on the Pass-26 exhibit (the
extended-rule-2 obligation that would otherwise be owed — no witness left open).
`Anabelian/AdditiveCharacter.lean` (in-file `#print axioms`, all standard-only):

```
'Anabelian.additiveCoeff'                              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveCharacter'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveCharacter_eq_one'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveQuotientHom'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_additiveCharacter'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveQuotientHom_injective'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveQuotient_mul_comm'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveCoeff_residue_not_additive_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `additiveCoeff` (defined for **every** level): the unique `a_σ` with `σπ − π = π^(i+1)·a_σ`
  (cancellation in the domain `↥A`), with `_spec`/`_unique`/`_one` and
  `smul_uniformizer_eq_mul` (`σπ = π(1 + π^i a_σ)`).
- **`additiveCharacter (hi : 1 ≤ i) : G_i →* Multiplicative 𝓀`** — the pass's heart: the
  cocycle `a_{στ} = a_σ + (1 + π^i a_σ)^(i+1)·σ(a_τ)` straightens to additivity by exactly two
  inputs: inertia fixes residues (Pass 24's lemma, via antitonicity `G_i ≤ G₀`), and
  `1 + π^i a_σ ≡ 1 mod 𝔪` — **which uses `i ≥ 1`**.
- **`additiveCharacter_eq_one`** — `G_{i+1} ≤ ker θ_i`; **`additiveQuotientHom`** —
  `G_i/G_{i+1} →* 𝓀⁺` (`QuotientGroup.lift`).
- Under monogenicity (Pass-25 binders, unchanged): **`ker_additiveCharacter`** —
  `ker θ_i = G_{i+1}` (detection at `i+1`); **`additiveQuotientHom_injective`** — the embedding
  `G_i/G_{i+1} ↪ 𝓀⁺`; **`additiveQuotient_mul_comm`** — the higher quotients are abelian.
- **`additiveCoeff_residue_not_additive_at_zero`** — **the `i = 0` failure witness**: on the
  Pass-26 exhibit (`ℚ⸨X⸩`, `σ : X ↦ −X`), `σ² = 1` gives `a_{σσ} = 0` while
  `res(a_σ) + res(a_σ) = −4 ≠ 0` (since `4` is a unit of `ℚ⟦X⟧`) — so the additive recipe is
  provably **not** a homomorphism at level 0, where the multiplicative `θ₀` (Pass 24) is the
  correct structure. The `1 ≤ i` hypothesis is load-bearing, *witnessed*, not asserted.

**Honesty.** Monogenicity exactly as in Pass 25 (named, not claimed irremovable — no new
obligation). **Cut from scope mid-pass** (the Pass-22/24 under-promise discipline applied to
ourselves): the uniformizer-twist law `res(w)^i·res(a'_σ) = res(a_σ)` — mathematically routine,
but its *statement* hits a reproducible `whnf` divergence elaborating `additiveCoeff` at the
composite uniformizer `π * ↑w` (not cured by 800k heartbeats, coercion ascriptions, or
`subst`-elimination; root cause unisolated — logged in NOTES as a known elaboration pathology).
Its better formulation is the twist-free canonical map into `𝔪^i/𝔪^(i+1)` — named future work.
Also not attempted: wild `G₁` pro-`p` (needs `char 𝓀 = p`); the local-field instantiation. No
new `structure`/`class`; no owed witness (one *discharged*); D1 N/A; D2 N/A. Recovers nothing
from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **L2: the full ladder of quotient characters exists —
`θ₀ : G₀/G₁ ↪ 𝓀ˣ` and `θ_i : G_i/G_{i+1} ↪ 𝓀⁺` (`i ≥ 1`, monogenicity-conditional) — with the
level-0/level-positive dichotomy constructively witnessed.**

### Pass 28 (2026-06-10) — rung L2: wild inertia — `G₁` is a `p`-group, `p ∤ |G₀/G₁|`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. The capstone of the
finite-level arc (Serre IV §2, corollaries): in residue characteristic `p`, the two character
embeddings have opposite torsion, and chaining the additive one through the eventually-trivial
filtration makes `G₁` the **normal Sylow `p`-subgroup of the inertia group** — the wild inertia.
`Anabelian/WildInertia.lean` (in-file `#print axioms`, all standard-only; **compiled clean on the
first build** — the probe-first discipline's first zero-iteration pass):

```
'Anabelian.additiveQuotient_pow_eq_one'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.pow_mem_ramificationGroup_succ'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.pow_pow_mem_ramificationGroup'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isPGroup_ramificationGroup_one'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.tameQuotient_pow_prime_eq_one_imp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.not_dvd_natCard_tameQuotient'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `additiveQuotient_pow_eq_one` — **exponent `p`** on `G_i/G_{i+1}` (`i ≥ 1`, `[CharP 𝓀 p]`,
  monogenicity): the Pass-27 embedding + `p • c = 0` in `𝓀` (via `toAdd`/`CharP.cast_eq_zero`).
- `pow_mem_ramificationGroup_succ` / `pow_pow_mem_ramificationGroup` — `σ ∈ G_i ⟹ σ^p ∈
  G_{i+1}`, iterated to `σ ∈ G₁ ⟹ σ^(p^k) ∈ G_{1+k}` (the fixed-ring hypothesis taken once over
  `G₀`, restricted by antitonicity).
- **`isPGroup_ramificationGroup_one`** — `IsPGroup p G₁` for finite decomposition groups under
  separation + monogenicity: the chain above meets Pass 24's `exists_ramificationGroup_eq_bot`.
  Notably `p` need not be assumed prime.
- `tameQuotient_pow_prime_eq_one_imp` — **no `p`-torsion in `G₀/G₁`** (`p` prime): the tame
  embedding lands in `𝓀ˣ` where **Frobenius injectivity** (`frobenius_inj`) kills `p`-torsion.
- **`not_dvd_natCard_tameQuotient`** — `p ∤ |G₀/G₁|` by Cauchy's theorem
  (`exists_prime_orderOf_dvd_card`), contrapositive.

**Honesty.** Hypotheses are exactly the Pass-25/27 stack plus `[CharP (ResidueField ↥A) p]` and
(only where needed: the tame side, Cauchy) `[Fact p.Prime]`; finiteness + separation only where
consumed. NOT attempted: Mathlib `Sylow p` packaging (routine atop these two results — named);
the **pro-`p` limit statement** for the absolute group (upper-numbering territory); the
local-field instantiation (where `char 𝓀 = p` holds automatically). No new `structure`/`class`;
no new owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **L2 finite-level arc COMPLETE (modulo the named
monogenicity hypothesis): filtration, both regime witnesses, all quotient characters, and the
wild/tame dichotomy — `G₁` pro-`p` at finite level, `G₀/G₁` tame of order prime to `p`.**

### Pass 29 (2026-06-10) — the descent, rung 1: `𝒪_L` as a valuation subring; separation + eventual triviality DISCHARGED at `𝒪_L`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Opens the
finite-extension local-field block (user-approved direction): for `K` nonarchimedean local and
`L/K` **finite**, `Anabelian/ExtensionIntegers.lean` builds the object all of L2 was
parametrized by — and discharges, at `A = 𝒪_L`, two of the abstract theory's standing
hypotheses. (In-file `#print axioms`, all standard-only; **first-try clean build**, the second
in a row.)

```
'Anabelian.isIntegral_iff_minpoly_coeff_mem_findim'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionIntegers'                                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_extensionIntegers_iff'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isNoetherianRing_extensionIntegers'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.iInf_ramificationGroup_extensionIntegers'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_ramificationGroup_extensionIntegers_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`extensionIntegers K L : ValuationSubring L`** — `𝒪_L = integralClosure 𝒪[K] L`, a genuine
  valuation subring: `mem_or_inv_mem` **is** the unique-extension-of-valuations theorem for the
  complete `K`, proved via the spectral norm with the **entire normed structure localized inside
  the proof field** (the Pass-18 `letI` discipline; the statement is `integralClosure`-pure —
  the D2 containment pattern reused, nothing new to watch). `IsLocalRing 𝒪_L` is then **free**
  (`ValuationSubring → ValuationRing → IsLocalRing`).
- `isIntegral_iff_minpoly_coeff_mem_findim` — the Pass-17 algebraic bridge, `L`-version
  (norm-free).
- `isNoetherianRing_extensionIntegers` (`[Algebra.IsSeparable K L]`) — Mathlib's
  `IsIntegralClosure.isNoetherianRing` over the DVR `𝒪[K]`, transported along the carrier
  identity.
- **`iInf_ramificationGroup_extensionIntegers`** — Pass 23's Krull separation hypothesis,
  **discharged**: `⨅ i, G_i(L/K) = ⊥` for finite separable `L/K`, a theorem.
- `Finite (decompositionSubgroup)` instance (`AlgEquiv.fintype`) and
  **`exists_ramificationGroup_extensionIntegers_eq_bot`** — Pass 24's finiteness + eventual
  triviality, **discharged**.

**Honesty.** The `[Algebra.IsSeparable K L]` hypothesis on the Noetherian-side results is what
Mathlib's integral-closure finiteness consumes (char 0: automatic; equal char: a real, named
restriction — same boundary family as the Pass-14 perfect-case narrowing). Remaining rungs of
the block, named: `IsDiscreteValuationRing 𝒪_L`; finite residue field; the
`IsNonarchimedeanLocalField L` assembly; the **monogenicity discharge** (the Passes-25/27/28
hypothesis becomes a theorem here, eventually); `e·f = n` bookkeeping. No new
`structure`/`class` (a witness for Mathlib's `ValuationSubring`, already rule-2-calibrated by
the Pass-22/26 collapse-vs-separation pair); no owed witness; D1 N/A; **D2: Pass-18 pattern
reused, contained**. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **The descent has its foundation: the L2 filtration now
lives on actual finite extensions of local fields, with separation and eventual triviality
proved rather than hypothesized.**

### Pass 30 (2026-06-10) — the descent, rung 2: `𝒪_L` is a DVR; the uniformizer package DISCHARGED

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**.
`Anabelian/ExtensionUniformizer.lean` (in-file `#print axioms`, all standard-only):

```
'Anabelian.algebraMap_mem_extensionIntegers_iff'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.maximalIdeal_extensionIntegers_ne_bot'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isDiscreteValuationRing_extensionIntegers' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_uniformizer_extensionIntegers'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionTameCharacter'                    depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`algebraMap_mem_extensionIntegers_iff`** — the integrally-closed intersection
  `𝒪_L ∩ K = 𝒪[K]` (via `isIntegral_algebraMap_iff` + `IsIntegrallyClosed.isIntegral_iff`).
- **`maximalIdeal_extensionIntegers_ne_bot`** — `𝒪_L` is not a field: the base uniformizer
  `ϖ_K` stays a nonzero non-unit (a unit-inverse would land in `𝒪_L ∩ K = 𝒪[K]`).
- **`isDiscreteValuationRing_extensionIntegers`** (`[Algebra.IsSeparable K L]`) — Noetherian
  (Pass 29) + Bezout (valuation ring) ⟹ PID (`IsBezout.TFAE`), local, `𝔪 ≠ ⊥`: **`𝒪_L` is a
  DVR.**
- **`exists_uniformizer_extensionIntegers`** — `∃ π, 𝔪_L = (π) ∧ π ≠ 0`: the `(π, hspan, hπ0)`
  hypothesis triple of every character theorem since Pass 24, now a **theorem** at `𝒪_L`.
- **`extensionTameCharacter`** — the showcase: the tame character
  `θ₀ : G₀(L/K) →* 𝓀_Lˣ` of a finite separable extension of local fields exists (Pass 24's
  `tameCharacterOfIrreducible` instantiated; canonical by `tameCharacter_eq_of_span_eq`).

**Honesty.** `[Algebra.IsSeparable K L]` exactly where Pass-29 Noetherian-ness is consumed.
Remaining rungs: finite residue field (`CharP 𝓀_L p` concrete), `IsNonarchimedeanLocalField L`
assembly, the monogenicity discharge, `e·f = n`. No new `structure`/`class`; no owed witness;
D1 N/A; D2 N/A (`integralClosure`-native; the spectral structure stays sealed in Pass 29).
Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **Of the abstract L2 theory's hypothesis stack —
separation, finiteness, eventual triviality, uniformizer package, monogenicity — only
monogenicity now remains open at `𝒪_L`.**

### Pass 31 (2026-06-10) — the descent, rung 3: the residue field `𝓀_L` is FINITE; `CharP` concrete

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Two files
(`Anabelian/ExtensionResidue.lean` — the local-hom half, unconditional;
`Anabelian/ExtensionResidueFinite.lean` — the finiteness half; split for build-granularity per
the NOTES environment log). In-file `#print axioms`, all standard-only:

```
'Anabelian.extensionAlgebraMap'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isUnit_extensionAlgebraMap_iff'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.finite_residueField_extensionIntegers'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.charP_residueField_extensionIntegers'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `extensionAlgebraMap : 𝒪[K] →+* 𝒪_L`; **`isUnit_extensionAlgebraMap_iff`** (unit transfer —
  Pass 30's argument abstracted to every element); **`IsLocalHom` instance** (the finite-level
  Pass-19 brick) ⟹ the residue extension `𝓀[K] →+* 𝓀_L` exists (`ResidueField.map`).
- **`finite_residueField_extensionIntegers`** (`[Algebra.IsSeparable K L]`) — `𝓀_L` is finite:
  module-finiteness of `𝒪_L` over `𝒪[K]` (Pass 29) pushed to the residue level through the
  local hom (all module/algebra structures `letI`-local), then finite-dimensional over the
  finite `𝓀[K]`.
- **`charP_residueField_extensionIntegers`** — the residue characteristic transfers along the
  injective residue extension: **Pass 28's `CharP 𝓀 p` hypothesis is concrete at `𝒪_L`.**

**Honesty.** Separability exactly where module-finiteness is consumed. Remaining rungs: the
`IsNonarchimedeanLocalField L` assembly; the **monogenicity discharge** (the last open
hypothesis of the abstract theory); `e·f = n`. No new `structure`/`class`; no owed witness;
D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **At `𝒪_L`, the Pass-28 wild/tame dichotomy now has every
hypothesis concrete except monogenicity: finite decomposition group ✓, separation ✓, uniformizer
✓, `CharP 𝓀_L p` ✓.**

### Pass 32 (2026-06-10) — the descent, rung 4: the MONOGENICITY ENGINE (totally-ramified case)

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. The deepest rung of the
block: the **monogenicity package of Passes 25/27/28, discharged for totally-ramified data**.
Two files (`Anabelian/ExtensionMonogenic.lean` — structures + the free half;
`Anabelian/ExtensionMonogenicTop.lean` — the engine). In-file `#print axioms`, standard-only:

```
'Anabelian.smul_extensionAlgebraMap_range_eq'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.closure_range_union_uniformizer_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Global `Algebra 𝒪[K] 𝒪_L` and `Module.Finite 𝒪[K] 𝒪_L` instances (promoting Pass 31's
  proof-local structures; canonical, no competing instances).
- **`smul_extensionAlgebraMap_range_eq`** — the **`hfix` half is free** for
  `A₀ = range(𝒪[K] → 𝒪_L)`: decomposition elements are `K`-algebra equivalences
  (`AlgEquiv.commutes`).
- **`closure_range_union_uniformizer_eq_top`** — the **`hgen` half** (Serre I §6 Prop. 18's
  skeleton, Nakayama-finished): given `hres` (residues covered by the base — trivial residue
  extension) and `he` (`𝔪_L^e ≤ (ι 𝔪[K])·𝒪_L`) — together, "totally ramified" — the finite
  π-adic digit expansion runs to depth `e`, the error lands in `𝔪[K]·𝒪_L`, and **Nakayama**
  (module-finiteness over the local `𝒪[K]` — *no completeness needed*) closes
  `Subring.closure (A₀ ∪ {π}) = ⊤`.

**Honesty.** `hres`/`he` are honest named data (= totally ramified), to be supplied by the
`e·f = n` bookkeeping (next rung) or by hand in concrete cases; no irremovability claimed (used
constructively — no rule-2 obligation). The general case (`A₀ = 𝒪_{L₀}`, maximal unramified
subextension) is named future work; the classical reduction runs through exactly this engine
over `L₀`. No new `structure`/`class` beyond the two canonical instances; no owed witness;
D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **For totally-ramified data, the monogenicity hypothesis
of the abstract L2 theory is DISCHARGED — the full tame/wild quotient structure (P24–P28)
instantiates on totally-ramified finite separable extensions of local fields, end to end.**

### Pass 33 (2026-06-10) — the descent, rung 5: the engine's data discharged; the SHOWCASE assembled

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Two files
(`Anabelian/ExtensionRamificationData.lean`, `Anabelian/ExtensionTotallyRamified.lean`).
In-file `#print axioms`, all standard-only:

```
'Anabelian.exists_pow_maximalIdeal_le_map'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.residue_sub_mem_of_surjective'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.closure_eq_top_of_residue_surjective'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_tameCharacter_extensionIntegers'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`exists_pow_maximalIdeal_le_map`** — the engine's `he` input holds **unconditionally** for
  every finite separable `L/K`: in the DVR `𝒪_L`, `(ι ϖ_K)` is automatically a power of `𝔪_L`
  (ideal classification; the exponent is the ramification index, no numerical bookkeeping
  needed). *One of the engine's two "totally-ramified" hypotheses was never a hypothesis.*
- **`residue_sub_mem_of_surjective`** — the `hres` input reduces to surjectivity of the residue
  extension `𝓀[K] → 𝓀_L` (`f = 1`: the honest totally-ramified datum).
- **`closure_eq_top_of_residue_surjective`** — the complete `hgen` package (engine + both data).
- **`ker_tameCharacter_extensionIntegers`** — **the showcase**: for totally ramified finite
  separable `L/K` and ANY uniformizer of `𝒪_L`, **`ker θ₀ = G₁`** — Pass 25's kernel
  identification with every hypothesis a theorem; with Pass 24's `tameQuotientHom`,
  `G₀/G₁ ↪ 𝓀_Lˣ` — **Serre IV §2 Prop. 7 at level 0, as a statement about actual local
  fields**.

**Honesty.** `hsurj` is the totally-ramified datum in its honest form; the general case routes
through the maximal unramified subextension `L₀` (named, the block's remaining depth). No new
`structure`/`class`; no owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group;
R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **The descent block's promise is delivered: every
hypothesis the abstract L2 theory accumulated (Passes 23–28) is now PROVED for totally ramified
finite separable extensions of nonarchimedean local fields — five rungs, zero axioms.**

### Pass 34 (2026-06-10) — the descent, rung 6: the inertia-fixed integers; the engine generalized; the GENERAL kernel theorem

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Two files
(`Anabelian/InertiaFixedIntegers.lean`, `Anabelian/ExtensionMonogenicGeneral.lean`). In-file
`#print axioms`, all standard-only (both files first-try clean builds):

```
'Anabelian.inertiaFixedIntegers'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smul_inertiaFixedIntegers_eq'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionAlgebraMap_mem_inertiaFixedIntegers' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.closure_subring_union_uniformizer_eq_top'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_tameCharacter_of_inertiaFixed_cover'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`inertiaFixedIntegers K L : Subring 𝒪_L`** — the working incarnation of `𝒪_{L₀}`: elements
  fixed by every inertia element. **`hfix` is free by definition**; the base image embeds
  (Pass 32's `AlgEquiv.commutes` lemma).
- **`closure_subring_union_uniformizer_eq_top`** — the Pass-32 engine **generalized to any base
  subring containing the image of `𝒪[K]`**: the Nakayama spine never used the specific base —
  only `S ⊇ range ι` (for the `𝒪[K]`-module structure) and residues-from-`A₀`. Same proof,
  abstracted binder.
- **`ker_tameCharacter_of_inertiaFixed_cover`** — **the general kernel theorem**: for ANY finite
  separable `L/K` and any uniformizer, if the inertia-fixed integers cover the residue field
  (`hresid`), then `ker θ₀ = G₁`. With Pass 33's unconditional `he`, **the general case of
  Serre IV §2 Prop. 7 (level 0) on actual local fields now hangs on exactly one named classical
  lemma** — `hresid` ("`L/L₀` is totally ramified", always true), whose proof path is the
  finite-level keystone surjectivity `G/G₀ ↠ Gal(𝓀_L/𝓀[K])` + finite Galois descent of
  residues: the block's next rung.

**Honesty.** `hresid` named, constructive, not claimed irremovable; the field `L₀` itself and
`inertiaFixedIntegers = 𝒪_{L₀}` are not needed and not built. Rule-2 note for the new
`Subring`-valued def: pinned by genuinely different models (totally ramified: as small as the
base closure; unramified: all of `𝒪_L`). No owed witness; D1 N/A; D2 N/A. Recovers nothing from
an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **General-case tame injectivity is one lemma away.**

### Pass 35 (2026-06-10) — the descent, rung 7 (first half): the inertia orbit polynomial

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**.
`Anabelian/InertiaCharpoly.lean` — the two bricks of the `hresid` proof (in-file
`#print axioms`, standard-only):

```
'Anabelian.coeff_inertiaCharpoly_mem'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_residue_inertiaCharpoly'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`coeff_inertiaCharpoly_mem`** — the coefficients of the inertia orbit polynomial
  `∏_{σ∈G₀}(X − σ•b)` (Mathlib's `MulSemiringAction.charpoly` over the subgroup, whose
  `Subgroup.mulSemiringAction` instance exists) are **inertia-fixed**
  (`smul_coeff_charpoly` — the symmetric-function invariance, free from Mathlib).
- **`map_residue_inertiaCharpoly`** — its residue is **`(X − b̄)^{|G₀|}`** (Pass 24's
  residue-fixing collapses every factor).

Hence: every coefficient of `(X − b̄)^{|G₀|}` is the residue of an inertia-fixed integer — the
raw material for `hresid`. The second half (Pass 36): write `|G₀| = p^a·m` (`p ∤ m`), extract
the `X^{p^a(m−1)}`-coefficient `±m·b̄^{p^a}` via freshman's dream, invert `m`, and run the
cyclic-generator argument (`b̄` a generator of `𝓀_Lˣ` ⟹ `b̄^{p^a}` a generator ⟹ the residue
image of the inertia-fixed integers is all of `𝓀_L`) — no Hensel, no Lucas, no completeness.

**Honesty.** Bricks only; `hresid` not claimed. No new `structure`/`class`; no owed witness;
D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free.

### Pass 36 (2026-06-10) — the descent finale: `hresid` proved; the unconditional kernel theorem

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**.
`Anabelian/InertiaResidueCover.lean` — `hresid` and the finale (in-file `#print axioms`,
standard-only; build host-verified, warning-clean):

```
'Anabelian.map_residue_inertiaFixedIntegers_eq_top'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.inertiaFixedIntegers_residue_cover'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_tameCharacter_extensionIntegers_general' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`map_residue_inertiaFixedIntegers_eq_top`** — the residue image `F` of the inertia-fixed
  integers is **all of `𝓀_L`**. For any `b̄`: every coefficient of `(X − b̄)^{|G₀|}` lies in `F`
  (the Pass-35 bricks); `|G₀| = p^e·m`, `p ∤ m` (`Nat.exists_eq_pow_mul_and_not_dvd`); the
  freshman's dream (`sub_pow_expChar_pow_of_commute` — the ExpChar-era name) plus
  `Polynomial.expand`/`coeff_expand`/`coeff_X_add_C_pow` identify the
  `X^{p^e(m−1)}`-coefficient as `−(b̄^{p^e})·m`; `p ∤ m` makes `m ≠ 0` in `𝓀_L`
  (`CharP.cast_eq_zero_iff`) and `m` inverts by `m^{q−2}` (`pow_card_sub_one_eq_one`), so
  `b̄^{p^e} ∈ F`; the `p^e`-power map is the **iterated Frobenius** — a ring hom out of a
  field, injective, hence surjective on the finite `𝓀_L` — so `F = 𝓀_L`.
- **`inertiaFixedIntegers_residue_cover`** — **`hresid` verbatim**: every `x ∈ 𝒪_L` is
  congruent mod `𝔪_L` to an inertia-fixed integer.
- **`ker_tameCharacter_extensionIntegers_general`** — **the finale**: Pass 34's reduction +
  `hresid` ⟹ `ker θ₀ = G₁` for ANY finite separable extension of nonarchimedean local
  fields, **unconditionally**. Serre IV §2 Prop. 7 (level 0), general case, on actual local
  fields.

Two deviations from the Pass-35 sketch, both simplifications: **no cyclic generator** of
`𝓀_Lˣ` (iterated-Frobenius surjectivity replaces the generator transport — the sketch's own
"or argue via the Frobenius automorphism" parenthetical was the better route), and **no
subfield structure** on `F` (`m⁻¹ = m^{q−2}` keeps the argument in subring-membership
arithmetic). `p := ringChar 𝓀_L` is derived internally (finite field ⟹ prime char), so the
Pass-31 `CharP`-transfer lemma is not consumed.

**Honesty.** `[Finite G₀]` (the proposition, per the `unusedFintypeInType` linter — `Fintype`
only proof-locally via `Fintype.ofFinite`) and `[Algebra.IsSeparable K L]` exactly where
consumed. Classically the content is "`L/L₀` is totally ramified" (Serre I §7), proved here
directly, without constructing `L₀`. No new `structure`/`class`; no owed witness; D1 N/A;
D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **The descent block (Passes 29–36) is closed: every
hypothesis of the abstract L2 lower-numbering theory is a theorem on actual local fields, in
the general case — not just the totally ramified one.**

### Pass 37 (2026-06-10) — consolidation: the P27/P28 quotient theory concrete at `𝒪_L`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**.
`Anabelian/ExtensionWildTame.lean` — five theorems (in-file `#print axioms`, standard-only;
host-verified `lake build`, warning-clean):

```
'Anabelian.closure_inertiaFixedIntegers_union_uniformizer_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ker_additiveCharacter_extensionIntegers'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.additiveQuotientHom_injective_extensionIntegers'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isPGroup_wildInertia_extensionIntegers'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.not_dvd_natCard_tameQuotient_extensionIntegers'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`closure_inertiaFixedIntegers_union_uniformizer_eq_top`** — the **general monogenicity
  theorem at `𝒪_L`**: the integers of any finite separable extension are ring-generated by the
  inertia-fixed integers together with any uniformizer (P34's generalized engine fed by P36's
  residue cover, packaged once as the feeder for every instantiation).
- **`ker_additiveCharacter_extensionIntegers`** / **`additiveQuotientHom_injective_extensionIntegers`**
  — Pass 27 concrete: `ker θ_i = G_{i+1}` and `G_i/G_{i+1} ↪ 𝓀_L⁺` for every `i ≥ 1` (the
  level-`i` fixedness input descends from level 0 along `ramificationGroup_antitone`).
- **`isPGroup_wildInertia_extensionIntegers`** / **`not_dvd_natCard_tameQuotient_extensionIntegers`**
  — Pass 28 concrete: `G₁` is a `p`-group and `p ∤ |G₀/G₁|`, `p` the residue characteristic of
  the base — **`G₁` is the normal Sylow `p`-subgroup of `G₀`, unconditionally**. Inputs all
  named priors: `hsep` via the P23 Krull idiom (`Ideal.iInf_pow_eq_bot_of_isLocalRing` +
  P29's `isNoetherianRing_extensionIntegers`), `CharP 𝓀_L p` via **P31's transfer lemma,
  consumed here for the first time**.

**Honesty.** No new mathematics: the pass's content is that the abstract P27/P28 theory and
the descent **compose with zero residue**. No `Finite`/`Fintype` hypotheses appear on any
statement — the decomposition subgroup's finiteness is a P29 *instance* and subgroup
finiteness synthesizes from it (this also reveals the `[Finite G₀]`-style hypotheses of
P35/P36 as synthesizable — candidate cleanup, not done this pass). No new `structure`/`class`;
no owed witness; D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **Serre IV §§1–2 at finite level is now complete and
unconditional on actual local fields: filtration, tame character, additive characters, and
the wild/tame Sylow dichotomy.**

### Pass 38 (2026-06-11) — the assembly, rung 1: the valuative structure on `L`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**.
`Anabelian/ExtensionLocalField.lean` — toward `IsNonarchimedeanLocalField L` (in-file
`#print axioms`, standard-only; host-verified `lake build`, warning-clean):

```
'Anabelian.extensionValuativeRel'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isNontrivial_ofValuation'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isNontrivial_extensionValuativeRel'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isValuativeTopology_extensionValuativeRel'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`extensionValuativeRel`** — the valuative relation on `L` from `𝒪_L`'s valuation
  (`ValuativeRel.ofValuation`), deliberately a `def`, NOT an instance: its base-independence
  across towers (`extensionValuativeRel K L` vs the relation from an intermediate base) is a
  **named canonicity obligation** for the pass that introduces towers; a global instance would
  turn that propositional identity into a diamond. Mathlib's own `ValuativeRel.topologicalSpace`
  is a `local instance` upstream "to avoid diamonds" — the design matches.
- **`isNontrivial_ofValuation`** — reusable abstract bridge: a valuation on a field with an
  element of value in `(0, 1)` induces a nontrivial valuative relation (via the
  `Valuation.Compatible` API: `vle_iff_le`/`vlt_iff_lt` against the canonical valuation).
- **`isNontrivial_extensionValuativeRel`** — **parent 3 of the class, discharged**: a Pass-30
  uniformizer (`ValuationSubring.valuation_lt_one_iff` + `Valuation.ne_zero_iff`) witnesses
  nontriviality.
- **`isValuativeTopology_extensionValuativeRel`** — **parent 1, free**: under the valuative
  topology, Mathlib's upstream `IsValuativeTopology` instance applies on the nose.

**Honesty.** NOT claimed: `LocallyCompactSpace L` (parent 2 — next rung),
`IsNonarchimedeanLocalField L` itself, base-independence. Rule-2 note: the construction is
pinned against the degenerate model — the trivial relation also exists on `L`, and the
nontriviality theorem is precisely the separation from it. No new `structure`/`class`; no
owed witness (the canonicity obligation is a named future theorem, not an unproved
load-bearing-hypothesis claim — categories kept distinct); D1 N/A; D2 respected by
construction. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **Two of the three parents of
`IsNonarchimedeanLocalField L` are discharged; the assembly hangs on local compactness.**

### Pass 39 (2026-06-11) — the assembly, rung 2: the `Valued` framework on `L`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**.
`Anabelian/ExtensionValued.lean` — six theorems (in-file `#print axioms`, standard-only;
host-verified `lake build`, warning-clean):

```
'Anabelian.valued_integer_eq_of_compatible'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isDiscreteValuationRing_of_subring_eq'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.finite_residueField_of_subring_eq'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.valued_integer_extensionValuativeRel'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isDiscreteValuationRing_valued_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.finite_residueField_valued_integer'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **The design discovery**: Mathlib's locally-compactness characterization for valued fields
  (`CompactSpace 𝒪 ↔ CompleteSpace 𝒪 ∧ IsDiscreteValuationRing 𝒪 ∧ Finite 𝓀`,
  `Topology/Algebra/Valued/LocallyCompact.lean`) is **`Valued`-native**, and Mathlib's
  porting-helper instance makes `L` a `Valued` field **on the rung-1 structures, adopting the
  given uniformity** — so the feared topology-identification seam does not exist:
  `Valued.v = valuation L` is `rfl`. The spectral norm is needed only for the completeness
  conjunct (deferred), not for the framework.
- **`valued_integer_eq_of_compatible`** (abstract, reusable) — the helper-`Valued` integer
  ring equals the valuation subring of any `Compatible` valuation (pure
  `vle_iff_le`/`valuation_le_one_iff` bookkeeping).
- **Transports** along subring equality via `RingEquiv.subringCongr`: DVR-ness
  (`IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`) and residue-finiteness
  (`ResidueField.mapEquiv`).
- **Concrete trio**: under the rung-1 `letI`-tower, `L` is `Valued` with integer ring `= 𝒪_L`
  (as subrings), which is a DVR (Pass 30, transported) with finite residue field (Pass 31,
  transported) — **two of the three compactness conjuncts, discharged**.

**Honesty.** NOT claimed: `CompleteSpace` (the third conjunct), `CompactSpace` of the
integers, `LocallyCompactSpace L`, the class assembly. No global instances — the
`letI`-tower in the statements is the hypothesis-parametrized pattern in topological
clothing; D2 intact. No new `structure`/`class`; no owed witness; D1 N/A. Recovers nothing
from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **The compactness criterion is two-thirds discharged;
the assembly hangs on the completeness conjunct.**

### Pass 40 (2026-06-11) — the assembly, rung 3: the spectral seam, crossed as equalities

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Two files (in-file
`#print axioms`, standard-only; host-verified `lake build`, warning-clean):

`Anabelian/ValuativeRelCongr.lean` (abstract, project-agnostic):

```
'Anabelian.ofValuation_congr'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ofValuation_eq_of_same_subring'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.uniformSpace_eq_of_isUniformAddGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`ofValuation_congr`** — equivalent valuations induce **equal** valuative relations (the
  class is `@[ext]`; `IsEquiv` is the pointwise `vle`-iff). Downstream topology
  identifications become `rw`s.
- **`ofValuation_eq_of_same_subring`** — same unit ball ⟹ same relation
  (`isEquiv_iff_val_le_one` + `valuation_le_one_iff`).
- **`uniformSpace_eq_of_isUniformAddGroup`** — at most one group uniformity per topology
  (`uniformity_eq_comap_nhds_zero` on both sides; the `IsRightUniformAddGroup` refinement is
  instance-derived).

`Anabelian/ExtensionSpectralSeam.lean` (concrete, under P29's spectral `letI` block, same
`maxHeartbeats` raise, same reason):

```
'Anabelian.mem_extensionIntegers_iff_mem_valued_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionValuativeRel_eq_spectral'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.completeSpace_spectral'                       depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`mem_extensionIntegers_iff_mem_valued_integer`** — **Pass 29's `hmem`, exported**: `𝒪_L`
  is the spectral unit ball (proof verbatim from inside the `extensionIntegers` definition).
- **`extensionValuativeRel_eq_spectral`** — the rung-1 relation **equals** the spectral one.
- **`completeSpace_spectral`** — `L` complete in the spectral norm
  (`spectralNorm.normedSpace` + `FiniteDimensional.complete` over the Pass-17 bridge).

**Honesty.** NOT claimed: completeness on the rung-1 tower (needs the
`IsValuativeTopology`-uniqueness lemma — Pass 41, probed route), `CompactSpace`,
`LocallyCompactSpace L`, the class assembly. No new `structure`/`class`; no owed witness;
D1 N/A; D2 intact. Recovers nothing from an abstract group; R1–R3 untouched.

Ledger delta: **0 / 0** — axiom-free. **All three conjuncts of the compactness criterion are
now proved on one side of the seam or the other; Pass 41 carries them across and assembles.**

### Pass 41 (2026-06-24) — the assembly closes: `IsNonarchimedeanLocalField L`

Introduced **zero** axioms; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. One file
(`Anabelian/ExtensionLocalFieldInstance.lean`; in-file `#print axioms` standard-only; host
`lake build` warning-clean; `scripts/preflight.sh` CLEAN, 8520 jobs, 44 files chain-checked):

```
'Anabelian.isValuativeTopology_unique'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.locallyCompactSpace_extensionValuativeRel' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isNonarchimedeanLocalField_extension'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`isValuativeTopology_unique`** (abstract, reusable) — two topologies that are both valuative
  for the *same* valuative relation are **equal**. `IsValuativeTopology.mem_nhds_iff` characterizes
  `s ∈ 𝓝 x` purely by the relation (the RHS is topology-independent), so the neighborhood filters
  agree pointwise (`TopologicalSpace.ext_nhds`).
- **`locallyCompactSpace_extensionValuativeRel`** — **parent 2, discharged**: `L` is locally
  compact in its rung-1 valuative topology. The honest conceptual proof: `L` is
  finite-dimensional over the locally compact field `K` (spectral norm) ⟹ **proper**
  (`FiniteDimensional.proper`) ⟹ locally compact; the rung-1 topology **equals** the spectral
  topology (P40's `extensionValuativeRel_eq_spectral` + `isValuativeTopology_unique`; the spectral
  side is `IsValuativeTopology` for the relation via `IsValuativeTopology.of_zero` +
  `Valued.mem_nhds_zero` + `Valuation.exists_setOf_restrict_le_iff`), carrying the property across.
- **`isNonarchimedeanLocalField_extension`** — **THE ASSEMBLY THEOREM**: every finite separable
  `L/K` of nonarchimedean local fields is itself a nonarchimedean local field. Parents 1
  (`IsValuativeTopology`) and 3 (`IsNontrivial`) from Pass 38, parent 2 (`LocallyCompactSpace`)
  here, on the rung-1 valuative structure `extensionValuativeRel` (induced by `𝒪_L`, Pass 29).

**Honesty.** The compactness-criterion route (Passes 39–40 discharged all three of its conjuncts:
DVR, finite residue, completeness) would *also* assemble parent 2; this pass takes the shorter
finite-dimensional-properness route for `LocallyCompactSpace` directly. The Pass 39/40 structural
theorems remain genuine and independently useful — they are the local-field structure of `L`, now
*also* recovered for free **from** `IsNonarchimedeanLocalField L` by Mathlib's derived instances.
**Not the cardinal sin**: the assembly is a structural fact *about* a given extension's topology,
strictly below R1; nothing is recovered from an abstract group. NOT claimed: base-independence of
`extensionValuativeRel` across towers (the **canonicity obligation** — Pass 42; gates `M/L/K`
iteration). No new `structure`/`class`; no owed witness; D1 N/A; D2 intact (spectral structures
live entirely inside proofs via `letI`, none in any statement).

Ledger delta: **0 / 0** — axiom-free. **The assembly opened at Pass 38 is COMPLETE:
`IsNonarchimedeanLocalField L` holds for every finite separable extension of nonarchimedean local
fields — the gate to towers `M/L/K`, intermediate base fields, and hence the ascent (Herbrand,
upper numbering, Serre IV §3) is now OPEN.**

### Pass 42 (2026-06-24) — governance: an unledgered orphan found and discarded; count stays 0 / 0

**No axiom entered the build; the active count is unchanged at `0 FOUNDATIONAL / 0 DEBT`.** Recorded
here because the ledger's history must reflect a near-miss against its own central discipline.

The session-start clean-tree check found `Anabelian/Reconstruction/Inputs.lean` — untracked since
2026-06-12, never imported, never committed, **never entered in this ledger** — declaring **two
`FOUNDATIONAL` axioms** (`localReciprocity_abelianization`, `padicUnitGroup_structure`; abelianized
local reciprocity + the `Kˣ` structure theorem, for a conditional R1-floor). The committed ledger
read `0 / 0` while the tree carried two axioms: the precise "working tree silently contradicts the
ledger" failure the convention forbids. Because the file was never wired into `Anabelian.lean`,
**no headline `#print axioms` was ever affected** — the `0 / 0` was and remains truthful for the
committed build — but invisible-axiom work is not a permitted state.

**Disposition: discarded** (host-side; user decision = cleanup-only, the R1-floor direction NOT
adopted this session). Full incident record, including the two axiom statements preserved verbatim
for a future *deliberate* R1-floor decision, is in `NOTES.md`'s Pass-42 entry. **Reclassification log
untouched** (nothing was reclassified — the axioms never legitimately existed in the project).
**Active axioms table unchanged:** still `*(none)* — 0 FOUNDATIONAL, 0 DEBT`.

Should the R1-floor ever be taken deliberately, A1/A2 would be the ledger's first `FOUNDATIONAL`
entries since the Pass-20 discharge, and would require: full schema entries here, a `ROADMAP.md`
R1-spine section, and — because A1+A2 sit close to handing `q` to `G_K^ab` — an explicit argument
that the conditional theorem does **not** trivially imply R1 (rule 5). Not this session.

### Pass 43 (2026-06-24) — the canonicity obligation DISCHARGED; count stays 0 / 0

Introduced **zero** axioms; **discharged the canonicity obligation** deferred since Pass 38 — the
base-independence of `extensionValuativeRel` across towers, the very reason it is a `def` and not an
instance. `Anabelian/ExtensionCanonical.lean` proves (standard axioms only — in-file `#print axioms`):

```
'Anabelian.integer_extensionValuativeRel_eq'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isIntegral_base_iff'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionIntegers_base_independent'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionValuativeRel_base_independent'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`integer_extensionValuativeRel_eq`** — *self-consistency of the assembly*: under
  `extensionValuativeRel K K'`, the integer ring `𝒪[K']` is exactly `extensionIntegers K K'` (the
  integral closure of `𝒪[K]` in `K'`). Pure `Compatible` bookkeeping on the canonical valuation —
  the `K'`-analogue of Pass 39's `valued_integer_eq_of_compatible`, without the `Valued`/uniformity
  layer. (The high-confidence anchor; it built axiom-clean already in the draft.)
- **`isIntegral_base_iff`** — *the transitivity engine*: for `x : L`, `IsIntegral ↥𝒪[K] x ↔
  IsIntegral ↥(extensionIntegers K K') x`. Forward by base enlargement (`IsIntegral.tower_top`);
  backward because `extensionIntegers K K'` is integral over `𝒪[K]` (`isIntegral_trans`, with the
  `Algebra.IsIntegral ↥𝒪[K] ↥(extensionIntegers K K')` instance built from `mem_extensionIntegers_iff`
  via `isIntegral_algebraMap_iff` through the injective subring inclusion). The two scalar towers
  `𝒪[K] → 𝒪_{K'} → K'` and `𝒪[K] → 𝒪_{K'} → L` are built on Mathlib's **ambient** subring-algebra
  instance (`Algebra.ofSubsemiring`, since `extensionIntegers K K'` is a subring of `K'` acting on
  `L`) via the `extensionAlgebraMap` coercion (`coe_extensionAlgebraMap`) — no hand-rolled `Algebra`
  instance (the draft's `algBL` conflicted with the ambient one and was deleted).
- **`extensionIntegers_base_independent`** — the two valuation subrings of `L` coincide
  (`extensionIntegers K L = extensionIntegers K' L`): `SetLike.ext` + `mem_extensionIntegers_iff`
  reduces to `isIntegral_base_iff`, with the final bridge `IsIntegral ↥(extensionIntegers K K') x ↔
  IsIntegral ↥𝒪[K'] x` along self-consistency (`RingEquiv.isIntegral_iff (RingEquiv.subringCongr …)`).
- **`extensionValuativeRel_base_independent`** — **THE CANONICITY THEOREM**: for a tower
  `K ⊆ K' ⊆ L` of finite separable extensions, `extensionValuativeRel K L = extensionValuativeRel
  K' L`. `congrArg (ofValuation ∘ ·.valuation)` of the subring equality. It rests **only** on the
  proved self-consistency + transitivity — not behind a hypothesis that trivially gives it away.

**Mathlib API that did the real work:** `IsIntegral.tower_top` + `isIntegral_trans` (integral-closure
transitivity), `isIntegral_algebraMap_iff` (reflect integrality through the injective subring
inclusion), `RingEquiv.isIntegral_iff` (transport along self-consistency),
`IsScalarTower.of_algebraMap_eq`, and the ambient `Algebra ↥(extensionIntegers K K') L`
(`Algebra.ofSubsemiring`).

**Not the cardinal sin**: a structural fact *about* the tower's valuation theory — the relation
depends only on `𝒪_L`, which is base-independent by integral-closure transitivity — strictly below
R1; recovers nothing from an abstract group. No new `structure`/`class`; no owed witness; D1 N/A;
D2 untouched (integrality is the native characterisation, `mem_extensionIntegers_iff` is `Iff.rfl` —
no spectral structure enters any statement). With this discharged, `extensionValuativeRel` could be
promoted to an instance; we keep it a `def` (upstream diamond-avoidance) and expose the equality as a
theorem, exactly as Mathlib does for its own local valuative structures.

**Ledger delta: 0 / 0.** Axiom-free. **The last L-rung prerequisite before the ascent is
discharged** — the theory may now iterate up towers `M/L/K` with intermediate fields as base fields.
Next: the **ascent** (Herbrand `φ`/`ψ`, upper numbering — Serre IV §3).

### Pass 44 (2026-06-24) — the ascent opens: the Herbrand function `φ` defined + foundational properties; count stays 0 / 0

Introduced **zero** axioms; **opened the ascent** (Serre IV §3) by constructing the **Herbrand
function** `φ`, genuinely **absent from Mathlib** (verified: `grep` for `herbrand` /
`upperRamification` / `upperNumbering` over Mathlib = 0 hits; `RingTheory/Valuation/RamificationGroup.lean`
defines only `G_0` and carries a literal `TODO: Define higher ramification groups in lower numbering`).
Built on the project's own lower-numbering filtration (`ramificationGroup`, Pass 23).
`Anabelian/HerbrandFunction.lean` proves (standard axioms only — in-file `#print axioms`, all 18 decls):

```
'Anabelian.herbrandPhi'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_strictMono'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_continuous'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_eq_id'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_le_self'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`herbrandPhi K A`** — Serre's `φ(u) = ∫_0^u dt/(G_0 : G_t)`, defined *literally as the integral*.
  Split into a reusable analytic engine `herbrandPhiSeq` on an abstract decreasing order-sequence
  `g i = |G_i|`, then instantiated on the real ramification orders `Nat.card (ramificationGroup K A i)`.
- The key enabling observation: the integrand `t ↦ g_{⌈t⌉}/g_0` is **antitone** (because the
  filtration decreases — `ramificationGroup_antitone`), hence interval-integrable
  (`Antitone.intervalIntegrable`), making the whole analysis clean.
- Properties (all instantiated, all standard-axioms-only): `herbrandPhi_zero` (`φ(0)=0`),
  **`herbrandPhi_strictMono`** (strictly increasing — integrand `> 0` since every `|G_i| ≥ 1`),
  `herbrandPhi_monotone`, **`herbrandPhi_continuous`** (`continuous_primitive`), `herbrandPhi_eq_id`
  (`φ(u)=u` for `u ≤ 0`), `herbrandPhi_le_self` (`φ(u) ≤ u` for `u ≥ 0` — slopes `≤ 1` as `G_t ≤ G_0`,
  the ramification content separating `φ` from `id`). **StrictMono + Continuous are exactly the
  precondition for the inverse `ψ = φ⁻¹`** (the next rung).

**Mathlib API that did the real work:** `intervalIntegral` (the construction is a literal interval
integral); `Antitone.intervalIntegrable`; `intervalIntegral.integral_add_adjacent_intervals` +
`integral_nonneg` (monotone) and `intervalIntegral_pos_of_pos_on` (strictMono); `continuous_primitive`
(continuity); `integral_mono_on` + `integral_const` (`φ ≤ id`); `Subgroup.card_le_of_le` + `Nat.card_pos`
(the orders are positive and decreasing, given `[Finite (A.decompositionSubgroup K)]`).

**Not the cardinal sin / rule-2.** `φ` is a structural invariant — a reparametrisation of a given
extension's ramification filtration — strictly below R1; recovers nothing from an abstract group. No
new `structure`/`class` (the objects are `def`s of real functions). The instantiation carries
`[Finite (A.decompositionSubgroup K)]`, which is **automatic at the intended finite level**
(`A = 𝒪_L`, `L/K` finite, `decompositionSubgroup ⊆ L ≃ₐ[K] L`) and is needed only so the orders are
positive (else `Nat.card = 0` and `φ ≡ 0`); a standing finiteness, **not** a claimed-essential
hypothesis — no rule-2 come-apart, no owed witness. D1 N/A; D2 N/A (real analysis + `ramificationGroup`,
no spectral/normed structure).

**Ledger delta: 0 / 0.** Axiom-free. **The ascent is open and its first rung is built.** Next: the
inverse `ψ = φ⁻¹` (reachable now from StrictMono + Continuous), then the upper numbering
`G^v = G_{ψ(v)}` and Herbrand's theorem (Serre IV §3).

### Pass 45 (2026-06-24) — the ascent, rung 2: the inverse `ψ = φ⁻¹` and the upper numbering; count stays 0 / 0

Introduced **zero** axioms; continued the ascent (Serre IV §3) by **inverting `φ`** and **defining
the upper numbering** `G^v(L/K)`. Both absent from Mathlib. `Anabelian/UpperNumbering.lean` proves
(standard axioms only — in-file `#print axioms`, all 21 decls; key headlines):

```
'Anabelian.herbrandPsi'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPsi_continuous'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.upperRamificationGroup'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.upperRamificationGroup_zero'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.upperRamificationGroup_antitone'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.upperRamificationGroup_eventually_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`φ` surjective** (`herbrandPhiSeq_surjective`): `φ` is continuous, `→ +∞` at `+∞` (it dominates
  `u/g_0`, the new lower bound `herbrandPhiSeq_div_le` since every order `≥ 1`) and `→ -∞` at `-∞`
  (it is `id` there), hence onto `ℝ` (`Continuous.surjective`). With Pass 44's strict monotonicity,
  `φ` is a homeomorphism `ℝ ≃ ℝ`.
- **`ψ = φ⁻¹`** (`herbrandPsi`, via `Function.invFun`), with inverse identities `herbrandPhi_psi`
  (`φ(ψ v)=v`), `herbrandPsi_phi` (`ψ(φ u)=u`), and `ψ` **strictly monotone**, **continuous** (via
  `StrictMono.orderIsoOfSurjective` → `OrderIso.toHomeomorph`), `ψ(0)=0`, `ψ=id` on `(-∞,0]`. Built
  abstractly (`herbrandPsiSeq`, reuse of Pass 44's pattern), then instantiated.
- **The upper numbering** `G^v(L/K) = G_{⌈ψ(v)⌉}` (`upperRamificationGroup`) with **`G^0 = G_0`**
  (inertia, `upperRamificationGroup_zero`), **antitone in `v`** (`upperRamificationGroup_antitone`),
  and **eventually `⊥`** (`upperRamificationGroup_eventually_bot`, under the same separation
  hypothesis as the lower numbering — via `ψ(φ i) = i`).

**Mathlib API that did the real work:** `Continuous.surjective` + `tendsto_atTop_mono'` /
`Tendsto.congr'` (surjectivity); `Function.invFun` + `rightInverse_invFun`/`leftInverse_invFun` (the
inverse); `StrictMono.orderIsoOfSurjective` + `OrderIso.toHomeomorph` (ψ continuity);
`intervalIntegral.integral_mono_on` (the `u/g_0` lower bound); `Nat.ceil_mono`/`Nat.ceil_natCast`,
`exists_ramificationGroup_eq_bot` (the upper-numbering properties).

**Not the cardinal sin / rule-2.** `ψ` and `G^v` are structural invariants of a given extension's
ramification filtration — strictly below R1; nothing recovered from an abstract group. No new
`structure`/`class` (`ψ` is a `def` of a real function; `G^v` a `def` of a `Subgroup`-valued
function). `upperRamificationGroup` is **not vacuous** (`G^0 = G_0`, antitone, eventually `⊥` are
proved constraints), but its **defining property — quotient-compatibility (Herbrand's theorem) — is
the next rung, not claimed here.** The instantiation's `[Finite (A.decompositionSubgroup K)]` is
automatic at the finite level and only gives `|G_i| ≥ 1` (needed for surjectivity / for `ψ` to
exist) — a standing finiteness, not a claimed-essential hypothesis, so no owed witness. D1 N/A; D2
N/A.

**Ledger delta: 0 / 0.** Axiom-free. **The upper numbering exists.** Next: **Herbrand's theorem**
`(G/H)^v = G^v H/H` and its prerequisites — the lower-numbering subgroup compatibility `H_u = H ∩
G_u` and `φ`-transitivity `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` (Serre IV §3), where Pass 43's canonicity
and the tower theory earn their keep.

### Pass 46 (2026-06-25) — toward Herbrand: lower-numbering subgroup compatibility `H_u = H ∩ G_u` (Serre IV §1 Prop. 2); count stays 0 / 0

Introduced **zero** axioms; built the first prerequisite for **Herbrand's theorem** — how the
lower-numbering filtration behaves under a sub-extension. `Anabelian/RamificationSubgroup.lean`
proves (standard axioms only — in-file `#print axioms`, all 7 decls):

```
'Anabelian.decompositionRestrict'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionRestrict_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_eq_comap'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_map_eq'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`ramificationGroup_eq_comap`** — Serre, *Local Fields*, IV §1 Prop. 2: for a tower `K ⊆ K' ⊆ L`,
  `ramificationGroup K' A i = (ramificationGroup K A i).comap decompositionRestrict` (the comap form
  of `H_u = H ∩ G_u`), with the textbook intersection form `ramificationGroup_map_eq`
  (`(G_i^{K'}).map decompositionRestrict = decompositionRestrict.range ⊓ G_i^K`).
- **`decompositionRestrict`** — the restriction-of-scalars monoid hom `Gal(L/K') →* Gal(L/K)`
  (`AlgEquiv.restrictScalars`), injective; the tower's group inclusion.
- The mathematical point: the lower numbering is **intrinsic to `L`** (the condition `∀ a, σa − a ∈
  𝔪_A^{i+1}` depends only on the action on `A`, not the base field), so for the *same* `A` it
  transfers verbatim along restriction of scalars. The **action agreement is `rfl`**
  (`decompositionRestrict_smul`), so the whole proposition is subring/stabilizer bookkeeping. Using
  the *same* `A` is exactly legitimised by **Pass 43** (`𝒪_L` base-independent across the tower).

**Mathlib API that did the real work:** `AlgEquiv.restrictScalars` (`restrictScalars_apply`/
`coe_restrictScalars` are `rfl`, so the actions agree definitionally);
`ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`, `MulAction.mem_stabilizer_iff`
(the valuation-subring action / stabilizer bookkeeping); `Subgroup.mem_comap`,
`Subgroup.map_comap_eq` (the two Prop-2 forms); the project's `mem_ramificationGroup_iff`.

**Not the cardinal sin / rule-2.** A structural fact about a tower's ramification filtration —
strictly below R1; recovers nothing from an abstract group. Stated for a **general** `A :
ValuationSubring L` (no finiteness / local-field structure needed); local-field relevance is via
`A = 𝒪_L` (base-independent by Pass 43). No new `structure`/`class` (`decompositionRestrict` is a
`def` of a `MonoidHom`; the results are about `Subgroup`s); no owed witness; D1 N/A; D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free. **Prop. 2 done.** Next toward Herbrand: **`φ`-transitivity**
`φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` (Serre IV §3 Prop. 15 — uses Prop. 2 to relate the order sequences),
then the quotient relationship `(G/H)^v = G^v H/H` (Prop. 14) itself.
