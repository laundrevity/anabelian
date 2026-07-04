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

### Pass 47 (2026-06-25) — the slope `φ'(u) = 1/(G_0 : G_u)`; count stays 0 / 0

Introduced **zero** axioms; proved the **defining derivative property** of the Herbrand function
(Serre IV §3) — `φ` is affine on each `(n, n+1)` with slope `|G_{n+1}|/|G_0| = 1/(G_0 : G_u)`. This
is the clean, self-contained prerequisite for the *differentiation* route to `φ`-transitivity.
`Anabelian/HerbrandSlope.lean` proves (standard axioms only — in-file `#print axioms`, all 8 decls):

```
'Anabelian.herbrandPhi_hasDerivAt_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_hasDerivAt_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_deriv_Ioo'      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_deriv_neg'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`herbrandPhi_hasDerivAt_Ioo`** — for `u ∈ (n, n+1)`, `HasDerivAt (herbrandPhi K A)
  (|G_{n+1}|/|G_0|) u`; with `herbrandPhi_hasDerivAt_neg` (`HasDerivAt φ 1 u` for `u < 0`, where
  `φ = id`) and the two `deriv` forms. Abstract engines `herbrandPhiSeq_hasDerivAt_Ioo`/`_neg`.
- **The method:** `φ(u) = ∫_0^u dt/(G_0 : G_t)` is a literal interval integral (Pass 44); its
  integrand is **locally constant off the integer breakpoints** (`Nat.floor_eq_on_Ico`), hence
  continuous there (`EventuallyEq` to a constant ⟹ `ContinuousAt`), and the **fundamental theorem of
  calculus** (`intervalIntegral.integral_hasDerivAt_right`) differentiates the primitive. The slope
  value `|G_{n+1}|/|G_0|` equals `1/(G_0 : G_{n+1}) = 1/(G_0 : G_u)` (Lagrange; `G_u = G_{⌈u⌉}`).

**Mathlib API that did the real work:** `intervalIntegral.integral_hasDerivAt_right` (FTC);
`Nat.floor_eq_on_Ico` (floor locally constant); `Filter.EventuallyEq.continuousAt`/`.eq_of_nhds`;
`Antitone.measurable` (the `StronglyMeasurableAtFilter` hypothesis); Pass 44's
`herbrandPhiSeq_intervalIntegrable`/`herbrandIntegrand_antitone`.

**Not the cardinal sin / rule-2.** A structural fact about a given extension's `φ` — strictly below
R1; recovers nothing from an abstract group. No new `structure`/`class`. The instantiation's
`[Finite (A.decompositionSubgroup K)]` is automatic at the finite level and only gives `|G_i| ≥ 1` —
a standing finiteness, no owed witness. D1 N/A; D2 N/A.

**Honest scope: this is NOT `φ`-transitivity.** It is the slope, a *prerequisite* for the
differentiation argument. Full transitivity `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` additionally needs the
**index-multiplicativity** relating `|G_i|`, `|H_i| = |H ∩ G_i|` (Pass 46), and `|(G/H)_j|` across
the tower (Serre's Lemma 5 / the quotient half of Herbrand's theorem) — the genuinely multi-pass
arithmetic wall, deliberately **not** half-built here (a clean partial beats a half-discharge).

**Ledger delta: 0 / 0.** Axiom-free. **The slope is in hand.** Next toward transitivity/Herbrand:
either the quotient relationship `(G/H)_{φ(u)} = G_u H/H` (the hard arithmetic), or further clean
`φ`-deepening now unlocked by the slope (the explicit piecewise-linear formula, concavity).

### Pass 48 (2026-06-26) — the explicit piecewise-linear formula for `φ`; count stays 0 / 0

Introduced **zero** axioms; proved the **closed form** of the Herbrand function (Serre IV §3):
`φ(n) = (|G_1|+…+|G_n|)/|G_0|` and, on `[n,n+1]`, `φ(u) = (|G_1|+…+|G_n|+(u−n)·|G_{n+1}|)/|G_0|` —
the concrete counterpart of Pass 47's slope. Confirmed first the transitivity/Herbrand **wall is
real** (`grep` over Mathlib: no higher-ramification quotient API), so took this clean, high-value
`φ`-deepening. `Anabelian/HerbrandFormula.lean` proves (standard axioms only — in-file `#print
axioms`, all 7 decls):

```
'Anabelian.herbrandPhi_natCast'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_eq_affine_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`herbrandPhi_eq_affine_formula`** (headline) — for `u ∈ [n, n+1]`, the explicit formula;
  **`herbrandPhi_natCast`** — the integer values `φ(n) = (Σ_{i<n} |G_{i+1}|)/|G_0|`. Abstract engines
  `herbrandPhiSeq_eq_affine_formula`/`_natCast`/`_affine` on an order sequence `g`.
- **The method (read off the integral, not the slope):** because `φ(u) = ∫_0^u dt/(G_0:G_t)` (Pass
  44), the integrand is the constant `g_{n+1}/g_0` on each unit interval — and crucially the interval
  integral `∫_a^b` only sees `Ι a b = Ioc a b`, which **excludes the left endpoint**, so the sole
  a.e.-exceptional point is the right breakpoint (null). Hence `herbrandSeq_integral_sub_Icc`
  (`∫_a^b = (b−a)·g_{n+1}/g_0` for `[a,b] ⊆ [n,n+1]`, via `integral_congr_ae`), then
  `sum_integral_adjacent_intervals` (split `∫_0^n`) for the integer values and
  `integral_add_adjacent_intervals` for the affine remainder. This sidesteps the breakpoint-derivative
  bookkeeping the slope route would have needed.

**Mathlib API that did the real work:** `intervalIntegral.integral_congr_ae` (+ `Set.uIoc_of_le`,
`measure_singleton`/`compl_mem_ae_iff` for the a.e. statement); `sum_integral_adjacent_intervals`,
`integral_add_adjacent_intervals`, `integral_const`; `Nat.floor_eq_on_Ico`; Pass 44's
`herbrandPhiSeq_intervalIntegrable`.

**Not the cardinal sin / rule-2.** A structural fact about a given extension's `φ` — strictly below
R1; recovers nothing from an abstract group. No new `structure`/`class`. The instantiation's
`[Finite (A.decompositionSubgroup K)]` is automatic at the finite level (gives `|G_i| ≥ 1`) — a
standing finiteness, no owed witness. D1 N/A; D2 N/A.

**Honest scope: still NOT `φ`-transitivity.** The closed form makes the order-arithmetic across a
tower explicit (a genuine prerequisite), but transitivity additionally needs the quotient
relationship `(G/H)_{φ(u)} = G_u H/H` (Serre Lemma 5) — the multi-pass wall verified absent from
Mathlib, deliberately not half-built.

**Ledger delta: 0 / 0.** Axiom-free. **The `φ` analytic theory is now concrete** (slope + closed
form). Next toward transitivity/Herbrand: the quotient relationship (the wall), or the remaining
clean `φ`/`ψ`-deepening (concavity, the `ψ` slope/formula).

### Pass 49 (2026-06-26) — the slope of the inverse `ψ`; count stays 0 / 0

Introduced **zero** axioms; proved the derivative of `ψ = φ⁻¹` (Serre IV §3), the symmetric
counterpart of Pass 47's `φ` slope. Where `ψ(v) ∈ (n, n+1)`, `ψ'(v) = |G_0|/|G_{n+1}| =
(G_0 : G_{ψ(v)})` — the ramification *index* itself, exactly inverting `φ' = 1/(G_0 : G_u)`. (Chose
this clean fallback after re-confirming the transitivity wall and finding **concavity blocked** —
Mathlib's `concaveOn_of_deriv` needs `DifferentiableOn`, which `φ` fails at its breakpoints.)
`Anabelian/HerbrandPsiSlope.lean` proves (standard axioms only — in-file `#print axioms`, all 8 decls):

```
'Anabelian.herbrandPsi_hasDerivAt'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPsi_hasDerivAt_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPsi_deriv'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPsi_deriv_neg'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`herbrandPsi_hasDerivAt`** — `ψ'(v) = |G_0|/|G_{n+1}|` where `ψ(v) ∈ (n, n+1)`; with
  `herbrandPsi_hasDerivAt_neg` (`ψ' = 1` for `v < 0`, where `ψ = id`) and the two `deriv` forms.
  Abstract engines `herbrandPsiSeq_hasDerivAt`/`_neg`.
- **The method:** the **inverse function theorem** `HasDerivAt.of_local_left_inverse`, fed by Pass
  47's `φ` slope (`herbrandPhiSeq_hasDerivAt_Ioo` at `ψ(v) ∈ (n,n+1)`), Pass 45's `ψ` continuity, and
  the inverse identity `φ ∘ ψ = id` (`herbrandPhiSeq_psiSeq`); `(g_{n+1}/g_0)⁻¹ = g_0/g_{n+1}` by
  `inv_div`. The negative side: `ψ = id` near `v < 0` (Pass 45's `herbrandPsiSeq_eq_id`) ⟹
  `congr_of_eventuallyEq` of `hasDerivAt_id`.

**Mathlib API that did the real work:** `HasDerivAt.of_local_left_inverse` (inverse function
theorem); `inv_div`; `HasDerivAt.congr_of_eventuallyEq` + `hasDerivAt_id`; Pass 47's `φ` slope,
Pass 45's `herbrandPsiSeq_continuous`/`herbrandPhiSeq_psiSeq`/`herbrandPsiSeq_eq_id`.

**Not the cardinal sin / rule-2.** A structural fact about a given extension's `ψ` — strictly below
R1; recovers nothing from an abstract group. No new `structure`/`class`. The instantiation's
`[Finite (A.decompositionSubgroup K)]` is automatic at the finite level (gives `|G_i| ≥ 1`, so `φ` is
a bijection and `ψ` exists) — a standing finiteness, no owed witness. D1 N/A; D2 N/A.

**Honest scope: still NOT `φ`-transitivity.** The `φ`/`ψ` derivative picture is now complete and
symmetric, but transitivity still needs the quotient relationship `(G/H)_{φ(u)} = G_u H/H` (Serre
Lemma 5), the multi-pass wall verified absent from Mathlib, not touched here.

**Ledger delta: 0 / 0.** Axiom-free. **The Herbrand pair's derivative theory is complete.** Next
toward transitivity/Herbrand: the quotient relationship (the wall — would need a project-built
quotient-ramification theory), or the remaining clean deepening (the `φ`/`ψ` closed forms,
concavity via a from-scratch piecewise argument).

### Pass 50 (2026-07-02) — the quotient-restriction skeleton; count stays 0 / 0

**No axiom added, none needed.** Pass 50 opened the quotient-ramification theory (toward Serre IV
§3 Lemma 5 → `φ`-transitivity → Herbrand's theorem) with its group-theoretic skeleton, all proved:
`Anabelian/RamificationQuotient.lean`, 11 declarations, all standard-axioms-only.

```
'Anabelian.restrictNormalHom_smul_comap'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_stabilizer_restrictNormalHom'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.algebraMap_decompositionQuotient_smul'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_comp_decompositionRestrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_ker'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.comapRingHom'                                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_maximalIdeal_of_comapRingHom'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_mem_ramificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_zero_map_le'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.inertiaSubgroup_map_le'                          depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`decompositionQuotient`** — the quotient restriction `D(A) →* D(A ∩ K')` along
  `Gal(L/K) ↠ Gal(K'/K)` for a tower `K ⊆ K' ⊆ L` with `K'/K` normal (`A ∩ K'` =
  `A.comap (algebraMap K' L)`; for `A = 𝒪_L` this is `𝒪_{K'}`, unambiguous by Pass 43 canonicity)
  — the quotient counterpart of Pass 46's `decompositionRestrict`.
- **`decompositionQuotient_ker`** — the headline: **exactness of
  `Gal(L/K') → Gal(L/K) → Gal(K'/K)` at the decomposition level**,
  `ker (decompositionQuotient) = range (decompositionRestrict)`.
- **Inertia preservation** — `G_0(L/K)` maps into `G_0(K'/K)`
  (`decompositionQuotient_mem_ramificationGroup_zero`, + `map ≤` and `inertiaSubgroup` forms):
  the `i = 0`, renumbering-free base case of Lemma 5 (`φ_{L/K'}(0) = 0`).

**Mathlib API that did the real work:** `AlgEquiv.restrictNormalHom` +
`AlgEquiv.restrictNormal_commutes` (the whole quotient direction); `AlgEquiv.ofRingEquiv` (the
kernel's converse: a `σ` fixing `K'` *is* a `K'`-automorphism);
`ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`; `mem_maximalIdeal`/`mem_nonunits_iff` +
`IsUnit.map` (the inclusion `A ∩ K' →+* A` reflects `𝔪`).

**Not the cardinal sin / rule-2.** Group-theoretic bookkeeping for a tower of given fields —
strictly below R1; recovers nothing from an abstract group. No new `structure`/`class`
(`decompositionQuotient`/`comapRingHom` are `def`s of homs). `[Normal K K']` is a definitional
prerequisite (without it `Gal(K'/K)` receives no restriction map), not a removable theorem
hypothesis — no owed witness. D1 N/A; D2 N/A.

**Honest scope: the skeleton, NOT the arithmetic.** Deliberately absent (unbuilt rather than
half-built): surjectivity of `decompositionQuotient` (needs Galois transitivity on the valuation
subrings above a given one) and the higher-`i` image — the latter is exactly Lemma 5
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` with its `φ`-renumbering, i.e. the `i_{K'/K}` vs `i_{L/K}`
arithmetic, the multi-pass wall.

**Ledger delta: 0 / 0.** Axiom-free. Next: the ramification arithmetic of the quotient
(Serre Lemma 5), then `φ`-transitivity (Prop. 15) and Herbrand's theorem (Prop. 14).

### Pass 51 (2026-07-03) — Serre's `i_G` function (`lowerIndex`); count stays 0 / 0

**No axiom added, none needed.** Pass 51 minted the currency the quotient-ramification arithmetic
(Serre IV §1 Prop. 3 → IV §3 Lemma 5 → `φ`-transitivity → Herbrand) is denominated in: Serre's
`i_G` function, generator-free, with IV §1 Lemma 1 (abstract form) and its calculus.
`Anabelian/RamificationIndex.lean`, 13 declarations, all standard-axioms-only.

```
'Anabelian.enat_le_of_forall_natCast_lt'                    depends on axioms: [propext, Quot.sound]
'Anabelian.enat_eq_of_forall_natCast_lt_iff'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex'                                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smul_sub_mem_pow_of_le'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_ramificationGroup_iff_lt_lowerIndex'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_ramificationGroup_iff_add_one_le_lowerIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_one'                                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_eq_top_iff_forall'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_eq_top_iff'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_inv'                                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.min_lowerIndex_le_lowerIndex_mul'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_conj'                                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_decompositionRestrict'                depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`lowerIndex K A σ : ℕ∞`** — `i_G(σ) = sup {n | ∀ a ∈ A, σa − a ∈ 𝔪_A^n}`: the filtration
  side of Serre's Lemma 1 taken as the *definition* (generator-free — no monogenicity needed at
  this level). `i_G(1) = ⊤`; `= ⊤ ↔ σ ∈ every G_i`; `= ⊤ ↔ σ = 1` under Krull separation (via
  Pass 23's `iInf_ramificationGroup_eq_bot`, same governance as there).
- **`mem_ramificationGroup_iff_lt_lowerIndex`** — the headline (IV §1 Lemma 1, abstract form):
  `σ ∈ G_i ↔ i < i_G(σ)`; Serre's inequality form `↔ i + 1 ≤ i_G(σ)` alongside.
- **The calculus** — `i(σ⁻¹) = i(σ)`, `i(στ) ≥ min (i(σ), i(τ))`, `i(τστ⁻¹) = i(σ)` (class
  function, via Pass 23 normality): each a one-liner from Lemma 1 + the `G_i` subgroup structure.
- **`lowerIndex_decompositionRestrict`** — IV §1 Prop. 2's *second half* (Pass 46 proved the
  subgroup half): `i_H = i_G` on `H` for the tower `K ⊆ K' ⊆ L` — **proved by `rfl`** (the
  condition is intrinsic to `A`; Pass 46's action agreement is definitional).

**Mathlib API that did the real work:** `lt_biSup_iff`/`le_biSup` (the sup characterization);
`ENat.add_one_le_iff`, `ENat.eq_top_iff_forall_gt` (the `ℕ∞` interface, plus two small project
lemmas `enat_le_of_forall_natCast_lt`/`enat_eq_of_forall_natCast_lt_iff` — naturals are cofinal
below any `x : ℕ∞`); `Ideal.pow_le_pow_right` (downward closure); `Subgroup.Normal.conj_mem`.

**Not the cardinal sin / rule-2.** Structure of the Galois action of given fields — strictly
below R1; recovers nothing from an abstract group. No new `structure`/`class` (`lowerIndex` is a
`def` into `ℕ∞`). The separation hypothesis in `lowerIndex_eq_top_iff` is inherited from Pass
23's `iInf_ramificationGroup_eq_bot` (holds at finite level, provably fails at `𝒪[K̄]`; as in
Pass 23, no claim that it is irremovable from this conclusion) — no owed witness. D1 N/A; D2 N/A.

**Honest scope: the currency, NOT the sum formula.** Deliberately absent: Serre IV §1 Prop. 3
`i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` (the real arithmetic wall — needs monogenicity and
the lift analysis) and the concrete identification `i_G(σ) = v_L(σx − x)` (needs the
`ExtensionMonogenic*` arc; deferred to the pass that consumes it).

**Ledger delta: 0 / 0.** Axiom-free. Next: Prop. 3 (the sum formula), feeding Lemma 5, then
`φ`-transitivity (Prop. 15) and Herbrand's theorem (Prop. 14).

### Pass 52 (2026-07-03) — surjectivity of the quotient restriction; count stays 0 / 0

**No axiom added, none needed.** Pass 52 discharged one of Pass 50's two named gaps: the
quotient restriction `decompositionQuotient : D(A) →* D(A ∩ K')` is **surjective** at the
canonical `A = 𝒪_L`, and with Pass 50's exactness this packages into the first isomorphism
`D(A) ⧸ H ≃* D(A ∩ K')`. `Anabelian/RamificationQuotientSurjective.lean`, 7 declarations, all
standard-axioms-only.

```
'Anabelian.decompositionQuotient_surjective'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionRestrict_range_normal'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotientEquiv'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smul_extensionIntegers'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionSubgroup_extensionIntegers_eq_top'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_extensionIntegers_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotientEquiv_extensionIntegers'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`smul_extensionIntegers`** — `σ • 𝒪_L = 𝒪_L` for every `σ ∈ Gal(L/K)`: Pass 29's
  membership is `IsIntegral 𝒪_K` definitionally, and integrality transfers along the
  `𝒪_K`-algebra map `σ` (`IsIntegral.map`, both ways via `σ⁻¹`). Hence
  **`D(𝒪_L) = ⊤`** (`decompositionSubgroup_extensionIntegers_eq_top`) — the integral-closure
  form of "the valuation of a complete field extends uniquely" (why Serre's decomposition group
  is the whole Galois group).
- **`decompositionQuotient_surjective`** — abstract: full stability of `A` + `L/K`, `K'/K`
  normal ⟹ surjective (lift via `AlgEquiv.restrictNormalHom_surjective`, stability lands it in
  `D(A)`). Stability is *sufficient*, discharged at `𝒪_L`; no necessity claim.
- **`decompositionQuotientEquiv`** — `D(A) ⧸ range (decompositionRestrict) ≃* D(A ∩ K')`
  (`decompositionRestrict_range_normal`: the range is a kernel by Pass 50, hence normal;
  `QuotientGroup.quotientKerEquivOfSurjective` + `quotientMulEquivOfEq`). Instantiated at
  `𝒪_L`: the subextension's decomposition data **is** the quotient `G/H` — the object of
  Herbrand's theorem `(G/H)^v = G^v H/H`, realized.

**Mathlib API that did the real work:** `AlgEquiv.restrictNormalHom_surjective` (the lift);
`IsIntegral.map` + `AlgEquiv.restrictScalars` (Galois-stability of the integral closure);
`QuotientGroup.quotientKerEquivOfSurjective` / `quotientMulEquivOfEq`; `Subgroup.eq_top_iff'`.

**Not the cardinal sin / rule-2.** Group-theoretic structure of a tower of given fields —
strictly below R1; recovers nothing from an abstract group. No new `structure`/`class`
(`decompositionQuotientEquiv` is a `def` of a `MulEquiv`). The abstract stability hypothesis is
discharged at the instantiation (sufficient, not claimed necessary) — no owed witness. D1 N/A;
D2 stays inside Pass 29's proof (this file touches `extensionIntegers` only through its
`IsIntegral` membership; all `#print axioms` standard-only).

**Honest scope: the lifts exist; the sum over them is still the wall.** Serre IV §1 Prop. 3
`i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` remains untouched — it needs the concrete
`i_G(σ) = v(σx − x)` (monogenicity) and the actual lift-set arithmetic.

**Ledger delta: 0 / 0.** Axiom-free. Next: the concrete `i_G` via monogenicity, then Prop. 3,
feeding Lemma 5 → `φ`-transitivity → Herbrand's theorem.

### Pass 53 (2026-07-03) — the concrete `i_G(σ) = v_L(σx − x)`; count stays 0 / 0

**No axiom added, none needed.** Pass 53 supplied the concrete half of Serre IV §1 Lemma 1:
under the monogenicity package (named binders, the Pass-25/27/28 discipline — nothing enters
the kernel), Pass 51's generator-free `lowerIndex` **is** the valuation of the generator
displacement. `Anabelian/RamificationIndexGenerator.lean`, 5 declarations, all
standard-axioms-only.

```
'Anabelian.mem_maximalIdeal_pow_iff_le_addVal'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.forall_smul_sub_mem_iff_generator'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_ramificationGroup_iff_smul_generator_sub_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_eq_addVal'                            depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.lowerIndex_extensionIntegers_eq_addVal'          depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`mem_maximalIdeal_pow_iff_le_addVal`** — the DVR bridge `x ∈ 𝔪^n ↔ (n : ℕ∞) ≤ addVal R x`
  (`𝔪^n = (ϖ^n)` + `addVal_le_iff_dvd` + `addVal (ϖ^n) = n`) — Mathlib has the ingredients but
  not the statement.
- **`forall_smul_sub_mem_iff_generator`** — the one-generator collapse
  `(∀ a, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n`: `⟸` is Pass 25's telescoping detection
  (`smul_sub_dvd_of_mem_closure` / `mem_ramificationGroup_of_smul_uniformizer_sub_mem`), `⟹`
  is `a := x`. Hence **Lemma 1 in generator form**
  (`mem_ramificationGroup_iff_smul_generator_sub_mem`): `σ ∈ G_i ↔ σx − x ∈ 𝔪^(i+1)`.
- **`lowerIndex_eq_addVal`** — the headline: on a DVR valuation subring, under the package,
  `i_G(σ) = addVal (σ • x − x) = v_L(σx − x)` — the exact currency Serre IV §1 Prop. 3
  computes with. At `𝒪_L` (`lowerIndex_extensionIntegers_eq_addVal`): `hfix` free (Pass 32),
  DVR instance from Pass 35; **only `hgen` remains a named binder**.

**The monogenicity hypothesis, honestly.** `hgen : Subring.closure (↑A₀ ∪ {x}) = ⊤` is carried
as a **named hypothesis binder** — exactly as Passes 25/27/28 carried it — NOT an `axiom`
(nothing in the kernel, `#print axioms` standard-only), NOT claimed discharged. Its in-project
discharge (Serre III §6 Prop. 12: local fields with separable residue extension are monogenic)
is named future work in `ROADMAP.md` L2. No load-bearing claim is made for `hgen`/`hfix`
(sufficient conditions, necessity not asserted) — no owed witness.

**Mathlib API that did the real work:** `IsDiscreteValuationRing.addVal` +
`addVal_le_iff_dvd` + `Irreducible.addVal_pow` + `Irreducible.maximalIdeal_eq` +
`Ideal.span_singleton_pow` (the bridge); Pass 25's closure-induction engine; Pass 51's
`enat_eq_of_forall_natCast_lt_iff` + `mem_ramificationGroup_iff_lt_lowerIndex`;
`ENat.add_one_le_iff` + `norm_cast`.

**Not the cardinal sin / rule-2.** Structure of the Galois action of given fields — strictly
below R1; recovers nothing from an abstract group. No new `structure`/`class`. D1 N/A; D2
stays inside Pass 29's proofs. R1–R3 untouched.

**Ledger delta: 0 / 0.** Axiom-free. Next: Prop. 3 (the sum formula — lifts exist by P52,
currency concrete by P53), or first the `hgen` discharge (Serre III §6 Prop. 12).

### Pass 54 (2026-07-03) — the monogenicity discharge: `𝒪_L = 𝒪_K[x]`; count stays 0 / 0

**No axiom added, none needed — and a standing named hypothesis became a theorem.** Pass 53's
concrete-`i_G` theory carried one named binder: `hgen` (a single ring generator of `𝒪_L` over
`𝒪_K`). Pass 54 proves it — Serre III §6 Prop. 12 in the finite-residue case — so the concrete
`i_G` at `𝒪_L` is now **unconditional**. `Anabelian/ExtensionMonogenicDischarge.lean`,
5 declarations, all standard-axioms-only.

```
'Anabelian.exists_pow_one_add_eq'                       depends on axioms: [propext]
'Anabelian.maximalIdeal_eq_span_of_mem_of_notMem_sq'    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.closure_union_singleton_eq_top'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_generator_extensionIntegers'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_generator_lowerIndex_eq_addVal'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`exists_generator_extensionIntegers`** (headline) — **`𝒪_L` is monogenic over `𝒪_K`** for
  every finite separable `L/K` over a nonarchimedean local field:
  `∃ x, Subring.closure (range (𝒪_K → 𝒪_L) ∪ {x}) = ⊤`. The route exploits **finite** residue
  fields (Pass 36) to avoid all minimal-polynomial/Taylor machinery: lift a cyclic generator
  `g` of `𝓀_L^×` (covers all residues: `0` or `g^k`); `y₀ := x₀^n − 1` (`n = |𝓀_L^×|`) lies in
  `𝔪` (Lagrange); if `y₀ ∈ 𝔪²`, correct `x := x₀(1+π₀)` — the binomial tail
  `(1+π₀)^n = 1 + nπ₀ + π₀²a` gives `x^n − 1 = y₀ + (n·x₀^n)π₀ + (…)π₀²` with `n·x₀^n` a
  **unit** (`(n : 𝓀_L) = |𝓀_L| − 1 = −1 ≠ 0`), so `x^n − 1 ∈ 𝔪 ∖ 𝔪²` — a uniformizer
  **inside `𝒪_K[x]`**; Pass 32's generation engine (+ Pass 33's unconditional `he`) closes it.
- **`exists_generator_lowerIndex_eq_addVal`** (payoff) — `∃ x, ∀ σ, i_G(σ) = v_L(σx − x)`,
  unconditional: Pass 53's identification with its last named hypothesis discharged. The
  `i_G` theory (P51–54) now has **zero** named hypotheses at `𝒪_L`.
- Supporting bricks: the **binomial tail** `(1+t)^m = 1 + mt + t²a` (any `CommRing`; audits
  `propext`-only) and the **DVR brick** `𝔪 ∖ 𝔪² spans 𝔪`
  (`maximalIdeal_eq_span_of_mem_of_notMem_sq`, via Pass 53's `addVal` bridge) — both reusable.

**What this does NOT discharge.** The Pass-25/27/28 *character* theorems' `(hgen, hfix)`
package needs an *inertia-fixed* generating subring; `𝒪_K[x]` is not inertia-fixed. That route
was closed separately (Passes 32–34, `inertiaFixedIntegers`). No conflation.

**Mathlib API that did the real work:** `IsCyclic.exists_generator` + `pow_card_eq_one'` +
`Nat.card_units` + `FiniteField.cast_card_eq_zero` (the residue arithmetic);
`isOfFinOrder_of_finite` + `IsOfFinOrder.mem_powers_iff_mem_zpowers` (`ℤ`-powers → `ℕ`-powers);
`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`/`addVal_def'`/`addVal_uniformizer`/
`irreducible_iff_uniformizer` + `Associated.irreducible` (the DVR brick); Pass 32's
`closure_subring_union_uniformizer_eq_top` + Pass 33's `exists_pow_maximalIdeal_le_map`;
`Ideal.Quotient.eq_zero_iff_mem`/`mk_eq_mk_iff_sub_mem`.

**Not the cardinal sin / rule-2.** Structure of given fields — strictly below R1; recovers
nothing from an abstract group. No new `structure`/`class`; no owed witness; D1 N/A; D2 stays
inside the Pass-29 proofs. R1–R3 untouched.

**Ledger delta: 0 / 0** (and one long-standing named hypothesis of the `i_G` arc eliminated —
the same species of progress as an axiom discharge, one level down). Next: Serre IV §1
Prop. 3 — the sum formula — the last wall before Lemma 5.

### Pass 55 (2026-07-03) — the subextension characteristic polynomial; count stays 0 / 0

**No axiom added, none needed.** Pass 55 built the substrate both divisibility directions of
Serre IV §1 Prop. 3 run through: Serre's polynomial `f = ∏_{h ∈ Gal(L/K')} (X − h·x)` and its
descent to `𝒪_L ∩ K'`. `Anabelian/SubextensionCharPoly.lean`, 11 declarations, all
standard-axioms-only.

```
'Anabelian.fullProdXSubSMul'                                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullProdXSubSMul_monic'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullProdXSubSMul_natDegree'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullProdXSubSMul_eval'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullProdXSubSMul_smul'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullProdXSubSMul_coeff'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_comapRingHom_eq_of_forall_smul_eq'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_fullProdXSubSMul_lift'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionSubgroup_extensionIntegers_restrict_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_fullProdXSubSMul_lift_extensionIntegers'  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.extensionIntegers_comap_algebraMap'              depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`fullProdXSubSMul G R x = ∏ g : G, (X − C (g·x))`** — the product over **all** of `G`
  (with multiplicity). Mathlib's `prodXSubSMul` ranges over the orbit `G ⧸ stabilizer` — the
  wrong primitive for Prop. 3, whose lift-set product `∏_{s ↦ σ̄}` counts multiplicities.
  Four properties by the Mathlib file's own techniques: monic, `natDegree = |G|`, kills `x`,
  and `G`-invariance (left-translation reindex, `Equiv.prod_comp (Equiv.mulLeft g)`), hence
  `G`-fixed coefficients.
- **`exists_comapRingHom_eq_of_forall_smul_eq`** — the fixed-points descent: a
  `Gal(L/K')`-fixed element of `𝒪_L` lies in `K'` (`IsGalois.mem_range_algebraMap_iff_fixed`)
  and hence in `A ∩ K'` along Pass 50's `comapRingHom`. The integral `L^H = K'`.
- **`exists_fullProdXSubSMul_lift`** (headline) — under `D_{K'}(A) = ⊤`, a **monic** `F` over
  `A ∩ K'` with `F.map (comapRingHom K' A) = fullProdXSubSMul` and equal degree
  (`Polynomial.lifts_iff_coeff_lifts` + `lifts_and_degree_eq_and_monic`). Hypothesis-free at
  `𝒪_L`: `decompositionSubgroup_extensionIntegers_restrict_eq_top` shows `D_{K'}(𝒪_L) = ⊤`
  for ANY intermediate `K'` (Pass 52's Galois-stability transported along Pass 46's
  `restrictScalars_smul_valuationSubring`), giving
  `exists_fullProdXSubSMul_lift_extensionIntegers`.
- **`extensionIntegers_comap_algebraMap`** — `𝒪_L ∩ K = 𝒪_K` (same base), from Pass 35's
  `algebraMap_mem_extensionIntegers_iff` — bookkeeping the Prop.-3 `addVal` comparison will
  need.

**Mathlib API that did the real work:** the `prodXSubSMul` proof techniques
(`Finset.smul_prod'`, `Polynomial.smul_X/C`, `coeff_smul`); `Equiv.prod_comp` +
`Equiv.mulLeft`; `IsGalois.mem_range_algebraMap_iff_fixed` (fixed points);
`Polynomial.lifts_iff_coeff_lifts` + `lifts_and_degree_eq_and_monic` (the monic lift);
`monic_prod_of_monic`/`natDegree_prod_of_monic`/`eval_prod`/`prod_eq_zero`.

**Not the cardinal sin / rule-2.** Substrate for a tower of given fields — strictly below R1;
recovers nothing from an abstract group. No divisibility and no part of the sum formula is
claimed. No new `structure`/`class` (`fullProdXSubSMul` is a `def` of a polynomial); no owed
witness; D1 N/A; D2 stays inside the Pass-29 proofs.

**Ledger delta: 0 / 0.** Axiom-free. Next: Prop. 3's two divisibilities — `a ∣ b`
(coefficient-telescoping on `σ̄f − f`, evaluated at `x`) and `b ∣ a` (the monic division
`g(X) − y = f·q` pushed along `σ̄`), then the `addVal` bookkeeping.

### Pass 56 (2026-07-03) — the lift-set identity; count stays 0 / 0

**No axiom added, none needed.** Pass 56 made Prop. 3's product `∏_{s ↦ σ̄} (s·x − x)`
computable: the fiber of `decompositionQuotient` is a coset of `H` **explicitly** (a
bijection, not just the abstract first-isomorphism statement of Pass 52), and transporting
Serre's polynomial (Pass 55) along a lift **is** the fiber product.
`Anabelian/RamificationLiftSet.lean`, 6 declarations, all standard-axioms-only.

```
'Anabelian.map_fullProdXSubSMul'                            depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_fullProdXSubSMul_eval'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_decompositionRestrict'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_mul_decompositionRestrict' depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionFiberEquiv'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionFiberEquiv_apply_coe'               depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`decompositionFiberEquiv`** — for any `s₀`, `h ↦ s₀ · decompositionRestrict h` is a
  bijection `D_{K'}(A) ≃ {s | decompositionQuotient s = decompositionQuotient s₀}`:
  injectivity from Pass 46 (`decompositionRestrict_injective` + left cancellation),
  surjectivity from Pass 50's exactness (`s₀⁻¹s ∈ ker = range`). Sums and products over the
  lifts of `σ̄` transport to `H` along it (`_apply_coe` is `rfl`, the `Equiv.prod_comp` hook).
- **`map_fullProdXSubSMul`** (headline) — `(∏_{h ∈ H} (X − h·x)).map s₀ = ∏_{h ∈ H}
  (X − (s₀ · dr h)·x)`: `map` distributes over the product and the per-factor identity
  `s₀ • (h • x) = (s₀ · dr h) • x` is **definitional** (Pass 46's action agreement is `rfl` —
  the proof is four lines). Evaluated at `x` (`map_fullProdXSubSMul_eval`): `∏_{h} (x −
  (s₀ · dr h)·x)` — Prop. 3's product over the lifts, `H`-parametrized, up to sign.
- Pointwise composite triviality (`decompositionQuotient_decompositionRestrict = 1`) and
  fiber-stability (`decompositionQuotient_mul_decompositionRestrict`) as the supporting
  bookkeeping.

**Mathlib API that did the real work:** `Polynomial.map_prod`/`map_sub`/`map_X`/`map_C` +
`Polynomial.eval_prod`; `Equiv.ofBijective`; `MonoidHom.mem_ker` + `mul_inv_cancel_left`/
`mul_left_cancel`; `MulSemiringAction.toRingAut` (Pass 23's device, now transporting
polynomials).

**Not the cardinal sin / rule-2.** Reindexing bookkeeping for a tower of given fields —
strictly below R1; recovers nothing from an abstract group. Neither divisibility of Prop. 3
is claimed. No new `structure`/`class` (`decompositionFiberEquiv` is a `def` of an `Equiv`);
no owed witness; D1 N/A; D2 untouched.

**Ledger delta: 0 / 0.** Axiom-free. Next: the telescoping direction `a ∣ b` (P25's engine on
`σ̄F − F` over `𝒪_L ∩ K'`, now reducible to bookkeeping via the P55 descent + this pass's
transport), or the division direction `b ∣ a`.

### Pass 57 (2026-07-03) — `𝒪_L ∩ K' = 𝒪_{K'}` + the coefficient telescoping; count stays 0 / 0

**No axiom added, none needed.** Pass 57 closed the transport gap flagged in Pass 56's handoff
(the quotient theory speaks of `B = 𝒪_L ∩ K'`, the generator technology of `𝒪_{K'}`) and
delivered the arithmetic half of Prop. 3's direction (i) plus the concrete left side of the
sum formula. `Anabelian/ExtensionComapIntegers.lean`, 9 declarations, all
standard-axioms-only.

```
'Anabelian.extensionIntegers_comap_eq'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.comapIntegersEquiv'                              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isDiscreteValuationRing_comap'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.baseToComapRingHom'                              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.coe_baseToComapRingHom'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.comapIntegersEquiv_comp_extensionAlgebraMap'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_generator_comap'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smul_baseToComapRingHom_range_eq'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_generator_comap_spec'                     depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`extensionIntegers_comap_eq`** — `(extensionIntegers K L).comap (algebraMap K' L) =
  extensionIntegers K K'`: integrality of a `K'`-element over `𝒪_K` is the same tested in
  `K'` or `L` (`isIntegral_algebraMap_iff` along the injective `K' ↪ L`) — the `comap`-level
  form of Pass 43's base-independence, in 4 lines. With: the value-preserving iso
  `comapIntegersEquiv` (`Subtype.ext rfl` fields), the **DVR instance on `B`**
  (`RingEquivClass.isDiscreteValuationRing` transport of Pass 35), and the base map
  `baseToComapRingHom : 𝒪_K →+* B` matched to Pass 29's `extensionAlgebraMap` along the iso.
- **`exists_generator_comap`** — `B` is monogenic over `𝒪_K`: Pass 54's generator
  transported (`RingHom.map_closure` + image-of-union bookkeeping + surjectivity of the iso).
- **`exists_generator_comap_spec`** (headline) — one `y ∈ B` with **(1)** generation,
  **(2)** the coefficient telescoping `(σ̄y − y) ∣ (σ̄c − c)` for every `σ̄ ∈ D(B)`, `c ∈ B`
  (Pass 25's `smul_sub_dvd_of_mem_closure`, its `hgen`/`hfix` hypotheses now theorems — the
  arithmetic half of Prop. 3's `a ∣ b`), and **(3)** `i_{K'/K}(σ̄) = addVal_B (σ̄y − y)` for
  every `σ̄` (Pass 53's `lowerIndex_eq_addVal`, hypothesis-free at `B`) — the left side of
  Prop. 3's sum formula in concrete form.

**Mathlib API that did the real work:** `isIntegral_algebraMap_iff` (the identification);
`IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`; `RingHom.map_closure` +
`Set.image_union`/`image_singleton`/`range_comp` + `RingHom.coe_range` (the closure
transport); `AlgEquiv.commutes` (the `hfix`); Pass 25's telescoping engine and Pass 53's
`addVal` identification as black boxes.

**Not the cardinal sin / rule-2.** Structure of a tower of given fields — strictly below R1;
recovers nothing from an abstract group. Direction (i)'s *evaluation* half (applying the
telescoping to Pass 55's coefficients at `x`) is NOT claimed — next brick. No new
`structure`/`class` (an equiv and a hom, both `def`s); no owed witness; D1 N/A; D2 stays
inside the Pass-29 proofs.

**Ledger delta: 0 / 0.** Axiom-free. Next: finish direction (i) (telescoping × P55 descent ×
P56 lift-set identity, evaluated at `x` ⟹ `a ∣ b`), then direction (ii), then the `addVal`
bookkeeping.

### Pass 58 (2026-07-03) — Prop. 3 direction (i): `a ∣ b`, PROVED; count stays 0 / 0

**No axiom added, none needed.** The first of Serre IV §1 Prop. 3's two divisibilities is a
theorem: `ι(σ̄y − y) ∣ ∏_{s ↦ σ̄} (x − s·x)` in `𝒪_L` — abstract and hypothesis-free at
`𝒪_L`. `Anabelian/RamificationLiftDvd.lean`, 5 declarations, all standard-axioms-only.

```
'Anabelian.dvd_eval_of_dvd_coeff'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.comapRingHom_decompositionQuotient_smul'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_comapRingHom_smul'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.comapRingHom_smul_sub_dvd_liftProd'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_generator_dvd_liftProd'                   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **The equivariance** — `comapRingHom (σ̄ • c) = s₀ • comapRingHom c` for `σ̄ =
  decompositionQuotient s₀` (`Subtype.ext` of Pass 50's
  `algebraMap_decompositionQuotient_smul`), lifted to polynomials
  (`map_comapRingHom_smul`: `(σ̄ • F).map ι = (F.map ι).map s₀`, coefficient-wise).
- **`dvd_eval_of_dvd_coeff`** — dividing every coefficient divides every evaluation
  (`eval_eq_sum_range` + `Finset.dvd_sum`); generic, reusable.
- **`comapRingHom_smul_sub_dvd_liftProd`** (abstract headline) — with Pass 55's descent and
  Pass 57's telescoping: every coefficient of `σ̄F − F` is divisible by `a = σ̄y − y`; push
  along `ι`, evaluate at `x`; the value computes to `(σ̄f)(x) − f(x) = ∏_h (x − (s₀·dr h)·x)
  − 0` by Pass 56's lift-set identity and Pass 55's `f(x) = 0`. Hence `ι(a) ∣ ∏`.
- **`exists_generator_dvd_liftProd`** (the `𝒪_L` form) — one `y ∈ B = 𝒪_L ∩ K'` carrying
  simultaneously the concrete `i_{K'/K}(σ̄) = addVal_B(σ̄y − y)` (Pass 57) and the
  divisibility for **every** `x ∈ 𝒪_L` and every lift `s₀`. Passes 55–57 assembled;
  hypothesis-free.

**Mathlib API that did the real work:** `Polynomial.coeff_smul`/`coeff_sub`/`coeff_map` +
`map_sub`/`eval_sub`/`eval_eq_sum_range`; `Finset.dvd_sum` + `Dvd.Dvd.mul_right`; `map_dvd`;
Passes 50/55/56/57 as black boxes.

**Not the cardinal sin / rule-2.** One direction of a comparison of elements attached to a
given tower — strictly below R1; recovers nothing from an abstract group. The converse
`b ∣ a` and the `addVal` bookkeeping are NOT claimed. No new `structure`/`class`; no owed
witness; D1 N/A; D2 stays inside the Pass-29 proofs.

**Build note:** this file elaborates slowly (~15 min wall-clock; heavy instance search in the
`𝒪_L` instantiation's context) — compiles clean within default heartbeats, but future passes
touching it should expect the cost.

**Ledger delta: 0 / 0.** Axiom-free. Next: direction (ii) (`b ∣ a`, the monic division), then
the `addVal` bookkeeping (fiber sum + `e'`-dilation), then the Prop. 3 assembly.

### Pass 59 (2026-07-03) — the `addVal` bookkeeping; count stays 0 / 0

**No axiom added, none needed.** Both sides of Prop. 3's sum formula are now `addVal`-readable:
the left through the `e'`-dilation, the right through the fiber sum.
`Anabelian/RamificationAddVal.lean`, 5 declarations, all standard-axioms-only.

```
'Anabelian.addVal_neg'                                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.addVal_prod'                                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isUnit_comapRingHom_iff'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.addVal_comapRingHom'                             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.addVal_liftProd'                                 depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`isUnit_comapRingHom_iff`** — units transfer both ways along `ι : B = A ∩ K' → A`:
  forward because the `A`-inverse of `ι c` is the image of `(c : K')⁻¹` (`map_inv₀` +
  inverse uniqueness in `L`), which is integral (it IS the inverse in `A`), hence in `B`.
  The multiplicative counterpart of Pass 50's `mem_maximalIdeal_of_comapRingHom`.
- **`addVal_comapRingHom`** (the `e'`-dilation) — `addVal_A (ι c) = addVal_B c ·
  addVal_A (ι π_B)`: write `c = u·π^n` (`eq_unit_mul_pow_irreducible`), units go to units
  (`addVal_eq_zero_iff`), so the upstairs valuation is `n·e'`; the `c = 0` case is
  `⊤ · e' = ⊤` via `ENat.top_mul` (`e' ≠ 0` because `ι π_B` is a non-unit by the transfer).
- **`addVal_liftProd`** (the fiber sum) — at `𝒪_L` with a generator `x`:
  `addVal (∏_h (x − (s₀·dr h)·x)) = Σ_h lowerIndex K 𝒪_L (s₀·dr h)`: generic `addVal_prod`
  (product ↦ sum, `Finset.induction_on`) + per-factor Passes 53–54
  (`lowerIndex_eq_addVal`, `hfix` free by Pass 32) + `addVal_neg` for the sign.
- Generic bricks `addVal_neg` (mutual divisibility + `addVal_le_iff_dvd`) and `addVal_prod`
  kept reusable.

**Mathlib API that did the real work:** `addVal_le_iff_dvd`, `addVal_eq_zero_iff`,
`addVal_def'`, `addVal_mul`/`addVal_pow`/`addVal_zero`, `eq_unit_mul_pow_irreducible`;
`ENat.top_mul`; `map_inv₀` + `eq_inv_of_mul_eq_one_right` + `mul_inv_cancel₀`;
`Finset.induction_on`; `nsmul_eq_mul`.

**Not the cardinal sin / rule-2.** Valuation bookkeeping for a tower of given fields —
strictly below R1; recovers nothing from an abstract group. No divisibility, no assembly
claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2 stays inside the Pass-29
proofs.

**Ledger delta: 0 / 0.** Axiom-free. The sum formula now lacks only direction (ii)
(`b ∣ a`) and the final assembly.

### Pass 60 (2026-07-03) — polynomial representation + `L = K'(x)`; count stays 0 / 0

**No axiom added, none needed.** The substrate of Prop. 3's direction (ii): membership in the
generated subring IS polynomial representation, and the `𝒪_K`-ring generator of `𝒪_L`
generates `L` as a field over every intermediate `K'`.
`Anabelian/ExtensionGeneratorRep.lean`, 4 declarations, all standard-axioms-only.

```
'Anabelian.exists_polynomial_map_eval_eq'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.comapRingHom_comp_baseToComapRingHom'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_polynomial_generator_rep'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.adjoin_generator_eq_top'                         depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`exists_polynomial_map_eval_eq`** (generic) — every element of
  `Subring.closure (range f ∪ {x})` is `(P.map f).eval x` (`Subring.closure_induction`:
  constants ↦ `C`, generator ↦ `X`, ring ops ↦ polynomial ops). At `𝒪_L`
  (`exists_polynomial_generator_rep`): with Pass 54's generator, **every integer of `L` is
  `(g.map (extensionAlgebraMap K L)).eval x`** for a `g` over `𝒪_K` — in particular the `ι y`
  of the coming division argument.
- **`comapRingHom_comp_baseToComapRingHom`** — the commuting square
  `ι ∘ (𝒪_K → B) = extensionAlgebraMap K L` (values: the scalar tower).
- **`adjoin_generator_eq_top`** — **`L = K'(x)`**: `IntermediateField.adjoin K' {x} = ⊤` for
  any intermediate `K'`. Closure induction puts every integer in the adjoin (base elements
  are `K`-scalars, hence `K'`-scalars via the tower); the valuation dichotomy
  (`mem_or_inv_mem`) extends to all of `L`. The input to direction (ii)'s degree count
  (`natDegree F = |H| = [L : K'] = deg (minpoly K' x)`).

**Mathlib API that did the real work:** `Subring.closure_induction` (twice);
`Polynomial.map_C/X/add/neg/mul` + `eval_*`; `IntermediateField.algebraMap_mem`/
`subset_adjoin`/`inv_mem`; `IsScalarTower.algebraMap_apply`; `mem_or_inv_mem`.

**Not the cardinal sin / rule-2.** Representation bookkeeping for a tower of given fields —
strictly below R1; recovers nothing from an abstract group. Neither the division nor
`b ∣ a` is claimed. No new `structure`/`class`; no owed witness; D1 N/A; D2 stays inside the
Pass-29 proofs.

**Ledger delta: 0 / 0.** Axiom-free. Next: direction (ii)'s remainder-vanishing (the minpoly
degree count), then the division and `b ∣ a`, then the Prop. 3 assembly.

### Pass 61 (2026-07-03) — the remainder-vanishing brick; count stays 0 / 0

**No axiom added, none needed.** The last genuinely new mathematics before Prop. 3: a
polynomial over `B = 𝒪_L ∩ K'` of degree `< |D_{K'}(𝒪_L)| = [L : K']` whose `ι`-image kills
the generator `x` is zero. `Anabelian/RamificationMinpolyBound.lean`, 1 declaration,
standard-axioms-only.

```
'Anabelian.eq_zero_of_map_comapRingHom_eval_eq_zero'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Move the coefficients to `K'` (`Polynomial.map_injective` along `B.subtype` preserves
  nonvanishing); the two evaluation routes `B → 𝒪_L → L` and `B → K' → L` agree
  (`hom_eval₂`/`eval₂_map` + a `rfl`-level hom identity), so the `K'`-polynomial kills `x`.
- The degree count: `deg (minpoly K' x) = finrank K' K'⟮x⟯` (`adjoin.finrank`) `= [L : K']`
  (Pass 60's `adjoin_generator_eq_top` + `finrank_top'`) `= Nat.card Gal(L/K')`
  (`IsGalois.card_aut_eq_finrank` — Nat.card-valued in current Mathlib) `= |D_{K'}(𝒪_L)|`
  (Pass 55's `D = ⊤` + `Subgroup.card_top`).
- `minpoly.degree_le_of_ne_zero` forbids the smaller-degree annihilator; `omega` closes.

**Not the cardinal sin / rule-2.** A degree bound for a tower of given fields — strictly
below R1. No new `structure`/`class`; no owed witness; D1 N/A; D2 untouched.

**Ledger delta: 0 / 0.** Axiom-free. Next: the division ⟹ `b ∣ a` (gluing), then the
Prop. 3 assembly.

### Pass 62 (2026-07-03) — Prop. 3 direction (ii): `b ∣ a`, PROVED; count stays 0 / 0

**No axiom added, none needed.** The second divisibility of Serre IV §1 Prop. 3:
`∏_{s ↦ σ̄} (x − s·x) ∣ ι(σ̄y − y)` in `𝒪_L`, for **every** `y ∈ B` and every lift `s₀`
(the division argument is uniform in `y`). `Anabelian/RamificationDivision.lean`,
1 declaration, standard-axioms-only.

```
'Anabelian.liftProd_dvd_comapRingHom_smul_sub'              depends on axioms: [propext, Classical.choice, Quot.sound]
```

Serre's monic division, every step a named brick: `ι y = g(x)` with `g` over `𝒪_K` (P60
representation); `g` moves to `B[X]` (P60 commuting square); `G = g_B − C y` kills `x` after
`ι`; division by P55's monic `F` (`modByMonic_add_div` — hypothesis-free in current Mathlib)
has remainder killing `x` of degree `< natDegree F = |H|` (P55 degree + `degree_modByMonic_lt`
+ `natDegree_lt_natDegree`), hence ZERO (P61); the exact identity `G = F·(G /ₘ F)` transports
along `σ̄` (base coefficients `σ̄`-fixed — P57's `smul_baseToComapRingHom_range_eq`
coefficient-wise; `C y ↦ C (σ̄y)`); mapping along `ι` and evaluating at `x`:
LHS `= ι y − ι(σ̄y) = −ι(a)`, RHS `= (∏_h (x − (s₀·dr h)·x))·(…)` (P58's
`map_comapRingHom_smul` + P56's `map_fullProdXSubSMul_eval`); `dvd_neg` finishes.

**Not the cardinal sin / rule-2.** One direction of a comparison for a given tower —
strictly below R1. The assembly is NOT claimed. No new `structure`/`class`; no owed witness;
D1 N/A; D2 untouched.

**Ledger delta: 0 / 0.** Axiom-free. Both Prop. 3 divisibilities now hold for the same `y`
and the same product; only the assembly remains.

### Pass 63 (2026-07-03) — SERRE IV §1 PROP. 3, PROVED; count stays 0 / 0

**No axiom added, none needed — the quotient-arithmetic wall is down, axiom-free.** The sum
formula, Serre IV §1 Prop. 3:

> `i_{K'/K}(σ̄) · e' = Σ_{h ∈ H} i_{L/K}(s₀ · dr h)`

for every `σ̄ = decompositionQuotient s₀` and every irreducible `π` of `B = 𝒪_L ∩ K'`
(`e' = addVal_{𝒪_L}(ι π)`), for a tower `K ⊆ K' ⊆ L` over a nonarchimedean local field
(`K'/K` normal, `L/K'` Galois). `Anabelian/RamificationSumFormula.lean`, 1 declaration,
standard-axioms-only.

```
'Anabelian.lowerIndex_decompositionQuotient_mul_eq_sum'     depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **Generator-free**: `i` is Pass 51's `lowerIndex`; the `x` and `y` of the proof do not
  appear in the statement. **No `σ̄ ≠ 1` hypothesis**: `ℕ∞` handles it (both sides `⊤`).
- **Eight lines of assembly over fourteen passes of substrate**: choose `x` (P54) and `y`
  (P57); `ι(σ̄y − y)` and `∏_{s ↦ σ̄}(x − s·x)` divide each other (P58 + P62); mutual
  divisibility ⟹ equal `addVal` (`addVal_le_iff_dvd` + `le_antisymm`); left side reads as
  `i_{K'/K}(σ̄)·e'` (P59 dilation + P57(3)), right side as the fiber sum (P59, per-factor
  P53–54).
- This was the wall first named at **Pass 47** ("the transitivity wall — the quotient
  relationship, not half-built") and re-verified absent from Mathlib at Passes 48–49. It
  fell in fourteen single-rung passes (P50–63), each axiom-free, none half-built.

**Not the cardinal sin / rule-2.** A quantitative identity for a given tower — strictly
below R1; recovers nothing from an abstract group. Lemma 5 / `φ`-transitivity / Herbrand are
NOT claimed (Prop. 3 is their input; the `φ`-renumbering conversion is real further work).
No new `structure`/`class`; no owed witness; D1 N/A; D2 stays inside the Pass-29 proofs.

**Ledger delta: 0 / 0. Prop. 3 rests on `propext`, `Classical.choice`, `Quot.sound` — and
nothing else.** Next: Serre IV §3 Lemma 5, then Prop. 15 (`φ`-transitivity) and Prop. 14
(Herbrand's theorem).

### Pass 64 (2026-07-03) — governance: the flat→folders refactor; count stays 0 / 0

**No axiom added, none needed; no mathematical content changed.** The structural refactor
deferred since Pass 42 (`scripts/refactor.sh`, "its own dedicated pass") executed: the flat
`Anabelian/` tree (64 files) became nine content folders — `Galois`, `FiniteField`,
`Reduction`, `Ramification`, `Herbrand`, `Extension`, `LocalField`, `Quotient`,
`ForMathlib`. The script's table was extended from its Pass-40 snapshot (44 entries) to all
64 files (the P41–63 additions: `LocalField/Instance`, `LocalField/Canonical`, the
`Herbrand/` arc P44–49, `Ramification/Subgroup`+`LowerIndex`+`LowerIndexGenerator`,
`Extension/MonogenicDischarge`, and the eleven-file `Quotient/` arc P50–63 ending in
`Quotient/SumFormula` = Prop. 3). All moves are git-tracked renames; **module paths changed,
declaration names unchanged**; import lines rewritten by exact-line match; the root
`Anabelian.lean` regenerated sorted. `scripts/preflight.sh` (line-length glob, named-binder
grep) and `scripts/chain_check.py` (file walk) updated to recurse into folders. Full
rebuild + preflight verified post-move (all `#print axioms` re-ran: standard-only
throughout).

**Ledger delta: 0 / 0** — nothing proved, nothing assumed; the audit surface is unchanged
and re-verified under the new paths.

### Pass 65 (2026-07-03) — the fiber index profile (Lemma 5, brick A); count stays 0 / 0

**No axiom added, none needed.** The first brick of Serre IV §3 Lemma 5: with a fiber
maximizer `s₁` (`j = i(s₁)` — Serre's `j(σ̄)`), the lower indices over the whole fiber are
`i_{L/K}(s₁·h) = min(i_H(h), j)`, so Pass 63's sum formula reads
`e'·i_{K'/K}(σ̄) = Σ_{h ∈ H} min(i_H(h), j)`. `Anabelian/Quotient/IndexProfile.lean`,
4 declarations, all standard-axioms-only.

```
'Anabelian.lowerIndex_mul_decompositionRestrict_eq_min'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_coset_lowerIndex_eq_min'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.exists_fiber_lowerIndex_eq_min'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.sum_lowerIndex_fiber_eq_sum_min'                 depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`lowerIndex_mul_decompositionRestrict_eq_min`** (the heart, abstract and `Normal`-free):
  `s₁` maximal on its coset ⟹ `i(s₁·dr h) = min(i_H(h), i(s₁))`. Pure Pass 51 calculus:
  `≥` is `min_lowerIndex_le_lowerIndex_mul` + `i_H = i_G` (`rfl`); `≤` in the hard case via
  `dr h = s₁⁻¹·(s₁·dr h)` + `lowerIndex_inv`, on pain of `i_H(h) < i_H(h)`.
- Maximizers exist by finiteness (`Finset.exists_max_image`; `[Finite]` in the types,
  `Fintype.ofFinite` in proofs — the `unusedFintypeInType` linter enforced the distinction);
  fiber-language packaging via Pass 56's coset stability; and the **`Σ min` sum form**.

**Not the cardinal sin / rule-2.** Order bookkeeping for a given tower — strictly below R1.
Lemma 5 itself is NOT claimed. No new `structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free. Next: the `Σ min`-vs-`φ` counting (the double-count
`Σ_h min(i_H(h), m) = Σ_{k<m} |H_k|`, then P48's `φ`-formula), toward
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)`.

### Pass 66 (2026-07-03) — the double count (Lemma 5, brick B1); count stays 0 / 0

**No axiom added, none needed.** `Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|` for any extension's
decomposition group (`Anabelian/Ramification/LowerIndexCount.lean`, 2 declarations, all
standard-axioms-only).

```
'Anabelian.enat_min_coe_eq_sum'                             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.sum_min_lowerIndex_eq'                           depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`enat_min_coe_eq_sum`** (generic `ℕ∞`): `min x m = Σ_{k<m} [k < x]` — the level-set
  decomposition, by induction on `m`.
- **`sum_min_lowerIndex_eq`**: decompose, swap (`Finset.sum_comm`), and each level set IS a
  ramification group — Pass 51's Lemma 1 `k < i(σ) ↔ σ ∈ G_k` — so the inner sum is
  `|G_k|` (`Finset.sum_boole` + `Fintype.card_subtype` + `Nat.card_eq_fintype_card`).
- With Pass 63 + Pass 65, the sum formula now reads
  **`e'·i_{K'/K}(σ̄) = Σ_{k<j} |H_k|`** — the numerator of Pass 48's `φ`-formula up to the
  `k = 0` term.

**Not the cardinal sin / rule-2.** Counting for a given filtration — strictly below R1. The
`φ`-bridge and Lemma 5 are NOT claimed. No new `structure`/`class`; no owed witness;
D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free. Next: the `φ`-bridge (P48's formula + casts) and the
`e' = |H_0|` identification, toward `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)`.

### Pass 67 (2026-07-03) — the `φ`-bridge (Lemma 5, brick B2); count stays 0 / 0

**No axiom added, none needed.** `Anabelian/Herbrand/SumBridge.lean`, 3 declarations, all
standard-axioms-only.

```
'Anabelian.sum_ramificationOrders_range_succ'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.natCast_sum_natCard_eq'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.sum_natCard_enat_eq'                             depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`sum_ramificationOrders_range_succ`** — `Σ_{k ≤ n} |G_k| = |G_0|·(φ(n) + 1)`: Pass 48's
  `herbrandPhi_natCast` with the `k = 0` term absorbed (`Finset.sum_range_succ'` +
  `mul_div_cancel₀`).
- The two cast forms tie it to Pass 66's `ℕ∞` output: `natCast_sum_natCard_eq` (the
  `Nat.card` sum read in `ℝ` — `ramificationOrders` is definitionally the cast) and
  `sum_natCard_enat_eq` (`ℕ∞` sum = cast of `ℕ` sum, `Nat.cast_sum`).
- The Lemma-5 numerical chain is now fully typed: P63 + P65 + P66 in `ℕ∞`, cast down to `ℕ`
  and up to `ℝ`, then this bridge — pending only `e' = |H_0|`.

**Not the cardinal sin / rule-2.** Cast/sum bookkeeping — strictly below R1. No new
`structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free. Next: `e' = |H_0|` (the classical `e = |G_0|` at the
subextension), the last input to `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)`.

### Pass 68 (2026-07-03) — `e'` in ideal form (toward `e' = |H_0|`); count stays 0 / 0

**No axiom added, none needed — and a discovery**: Mathlib HAS `|inertia| = e`
(`Ideal.card_inertia_eq_ramificationIdxIn`, Dedekind + separable residue, both satisfied
here), so `e' = |H_0|` is an identification program, not a re-proof. This pass is its left
half. `Anabelian/Quotient/RamificationIdx.lean`, 4 declarations, all standard-axioms-only.

```
'Anabelian.comapAlgebra'                                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.algebraMap_comapAlgebra'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_maximalIdeal_comapRingHom'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationIdx_comapRingHom'                    depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`comapAlgebra`** — `Algebra ↥B ↥(𝒪_L)` via `comapRingHom.toAlgebra` (Mathlib's
  `RamificationInertia` API is Algebra-based; no canonical instance exists between these
  subtypes, so no diamond; `algebraMap_comapAlgebra` is `rfl`).
- **`map_maximalIdeal_comapRingHom`** — `𝔪_B·𝒪_L = 𝔪_L^n` with `(n:ℕ∞) = addVal(ι π_B)`:
  `𝔪_B = (π_B)`, `ι π_B = u·ϖ^n`, spans of associates agree.
- **`ramificationIdx_comapRingHom`** — `Ideal.ramificationIdx 𝔪_B 𝔪_L = n`
  (`ramificationIdx_spec`; the strictness `𝔪^n ⊄ 𝔪^{n+1}` via Pass 53's `addVal` bridge):
  **Pass 59's `addVal`-form `e'` IS Mathlib's ideal-theoretic ramification index.**

**Not the cardinal sin / rule-2.** DVR/ideal bookkeeping — strictly below R1. `e' = |H_0|`
NOT claimed (its right half — instance package + inertia matching — is next). The
`comapAlgebra` instance instantiates the existing `Algebra` class (no new `structure`/
`class`, no rule-2 obligation); no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free.

### Pass 69 (2026-07-03) — the `IsGaloisGroup` package (toward `e' = |H_0|`); count stays 0 / 0

**No axiom added, none needed.** `D_{K'}(𝒪_L)` is a Galois group for `B ⊆ 𝒪_L` in Mathlib's
sense — the gateway hypothesis of `card_inertia_eq_ramificationIdxIn`.
`Anabelian/Quotient/GaloisGroup.lean`, 4 instances, all standard-axioms-only.

```
'Anabelian.faithfulSMul_decomposition'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.smulCommClass_decomposition'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isInvariant_decomposition'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isGaloisGroup_decomposition'                     depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`faithfulSMul_decomposition`** (abstract, any `(K', A)`): automorphisms agreeing on the
  integers agree on `L` — the valuation dichotomy (`mem_or_inv_mem` + `map_inv₀`), the P23
  ending as an instance.
- **`smulCommClass_decomposition`** (abstract): `g • (b • s) = b • (g • s)` — `b • s =
  ι(b)·s` (P68's `comapAlgebra` + `Algebra.smul_def`), `smul_mul'`, and decomposition
  elements fix `ι(b)` (`AlgEquiv.commutes`).
- **`isInvariant_decomposition`** (at `𝒪_L`): fixed points of the action = image of `B` —
  P55's `exists_comapRingHom_eq_of_forall_smul_eq`, with `D_{K'}(𝒪_L) = ⊤` (P55) converting
  subgroup-fixedness to `Gal(L/K')`-fixedness.
- **`isGaloisGroup_decomposition`** — the bundle.

**Not the cardinal sin / rule-2.** Instance packaging of existing project theorems into
existing Mathlib classes — strictly below R1; no new `structure`/`class`; no owed witness;
D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free. Next: the remaining instance package
(Dedekind/Module.Finite/torsion-free/LiesOver/separable-residue) + the inertia matching.

### Pass 70 (2026-07-03) — remaining instances + the inertia matching; count stays 0 / 0

**No axiom added, none needed.** Every hypothesis of Mathlib's
`card_inertia_eq_ramificationIdxIn` is now available.
`Anabelian/Quotient/InertiaSetup.lean`, 7 declarations, all standard-axioms-only.

```
'Anabelian.ramificationGroup_zero_eq_inertia'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isTorsionFree_comap'                             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.liesOver_maximalIdeal'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.baseComapAlgebra'                                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isScalarTower_baseComap'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.moduleFinite_comap'                              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isSeparable_residue'                             depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **The inertia matching is definitional**: `ramificationGroup K' A 0 = (𝔪_A).inertia
  (D_{K'}(A))` — Pass 23 built the filtration FROM `Ideal.inertia (𝔪^(i+1))`, so the
  anticipated "kernel-vs-kernel comparison" is `rw [ramificationGroup]; norm_num` (i.e.
  `pow_one`). A design dividend four months old.
- `isTorsionFree_comap` (domains + injective inclusion), `liesOver_maximalIdeal` (P50's
  `𝔪`-reflection + P59's two-way unit transfer), `baseComapAlgebra` +
  `isScalarTower_baseComap` (P60's commuting square is literally the tower axiom),
  `moduleFinite_comap` (P32's finiteness restricted along the tower), `isSeparable_residue`
  (P36 finite residue + embedding + finite ⟹ algebraic ⟹ separable over a finite (hence
  perfect) field — Mathlib's chain).
- Probe-verified as automatic: `IsDedekindDomain` for both rings (from the P35/P57 DVR
  instances), and the perfect-field separability chain.

**Not the cardinal sin / rule-2.** Instance plumbing + a definitional matching — strictly
below R1; all declarations instantiate existing Mathlib classes; no new `structure`/`class`;
no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free. Next: the application ⟹ `e' = |H₀|`.

### Pass 71 (2026-07-03) — `e' = |H₀|`, PROVED; count stays 0 / 0

**No axiom added, none needed.** The identification program (P68–71) closes: the classical
`e = |inertia|` for `L/K'`, in the project's vocabulary.
`Anabelian/Quotient/InertiaCard.lean`, 2 declarations, all standard-axioms-only.

```
'Anabelian.natCard_ramificationGroup_zero_eq'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.natCast_card_ramificationGroup_zero_eq_addVal'   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`natCast_card_ramificationGroup_zero_eq_addVal`** — for any irreducible `π` of
  `B = 𝒪_L ∩ K'`: `(Nat.card (ramificationGroup K' (𝒪_L) 0) : ℕ∞) = addVal_{𝒪_L}(ι π)` —
  **`e' = |H₀|`**. Four rewrites: P70's definitional inertia matching → Mathlib's
  `card_inertia_eq_ramificationIdxIn` (hypothesis package P68–70; `𝔪_B ≠ ⊥` from the DVR's
  `not_a_field'`) → `ramificationIdxIn_eq_ramificationIdx` (single prime) → P68's
  `ramificationIdx_comapRingHom`. (`Finite D` was automatic — the `Fintype` hypothesis
  wasn't even needed.)
- **Every input to Lemma 5's numerical heart `i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)` is now
  proved** (P63 sum formula, P65 fiber profile, P66 double count, P67 `φ`-bridge, P71
  `e' = |H₀|`); the assembly is the next pass.

**Not the cardinal sin / rule-2.** The closing application for a given tower — strictly
below R1. No new `structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free.

### Pass 72 (2026-07-03) — THE NUMERICAL LEMMA 5, PROVED; count stays 0 / 0

**No axiom added, none needed.** Serre IV §3's numerical identity — the heart of Lemma 5:

> for every `σ̄ ≠ 1`: **`i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1`**

(`Anabelian/Quotient/NumericalLemmaFive.lean`, `exists_lowerIndex_eq_herbrandPhi` — with the
fiber maximizer `s₁`, its full index profile, and the finiteness data `j(σ̄), i_{K'/K}(σ̄) ∈ ℕ`
all exposed for the set-level consumer). 1 declaration, standard-axioms-only, **no
`Fintype` hypothesis** (finiteness is automatic from finite-dimensionality).

```
'Anabelian.exists_lowerIndex_eq_herbrandPhi'                depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Pure assembly** — every link a named pass: P63 (Prop. 3 at the maximizer) → P65 (fiber
profile `i(s₁h) = min(i_H(h), j)`) → P66 (double count `Σ min = Σ_{k<j} |H_k|`; `j` finite
for `σ̄ ≠ 1` by P51's `lowerIndex_eq_top_iff` under the DVR separations, via P29's
Noetherian + Krull) → P71 (`e' = |H₀|`) → P67 (`ℕ∞`→`ℕ`→`ℝ` casts + the `φ`-bridge
`Σ_{k≤n}|H_k| = |H₀|(φ(n)+1)`); the degenerate `j = 0` case rides on P44's `φ(−1) = −1`.

**Not the cardinal sin / rule-2.** A numerical identity for a given tower — strictly below
R1. The set-level Lemma 5 / Prop. 15 / Prop. 14 are NOT claimed. No new `structure`/`class`;
no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — through 72 passes.

### Pass 73 (2026-07-03) — SERRE IV §3 LEMMA 5, PROVED; count stays 0 / 0

**No axiom added, none needed — Herbrand's renumbering lemma is a theorem.**

> for every `u : ℕ`:
> **`(ramificationGroup K (𝒪_L) u).map (decompositionQuotient)
>   = ramificationGroup K (𝒪_L ∩ K') ⌈φ_{L/K'}(u)⌉₊`**

(`Anabelian/Quotient/LemmaFive.lean`, `map_ramificationGroup_eq_ceil` — Serre's
`(G/H)_{φ_{L/K'}(u)} = G_u H/H`, with the `⌈·⌉₊` convention matching Pass 45's real-indexed
upper numbering). 4 declarations, all standard-axioms-only.

```
'Anabelian.lowerIndex_le_of_profile'                        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.decompositionQuotient_mem_map_iff'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ceil_herbrandPhi_lt_iff'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_ramificationGroup_eq_ceil'                   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `lowerIndex_le_of_profile` — the P72 profile bounds the whole fiber (P56's coset
  bijection). `decompositionQuotient_mem_map_iff` — **`σ̄` has a lift in `G_u ↔ u <
  j(σ̄)`** (P51's Lemma 1 both ways). `ceil_herbrandPhi_lt_iff` — the ceiling bridge
  `⌈φ(u)⌉ < a ↔ u < m` given `a = φ(m−1)+1 ∈ ℕ` (P44's strict monotonicity through
  `Nat.ceil`; `m = 0` rides on `φ(−1) = −1`).
- **`map_ramificationGroup_eq_ceil`** — membership on both sides: lifts exist (P52); for
  `σ̄ ≠ 1`, P72 supplies `(s₁, m, a)` and `σ̄ ∈ LHS ↔ u < m ↔ ⌈φ(u)⌉ < a ↔ σ̄ ∈ RHS`;
  `σ̄ = 1` trivial.

**Not the cardinal sin / rule-2.** The renumbering identity for a given tower — strictly
below R1. Prop. 15 / Prop. 14 NOT claimed. No new `structure`/`class`; no owed witness;
D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 73 passes.

### Pass 74 (2026-07-03) — the card multiplicativity (Prop. 15's arithmetic heart); count stays 0 / 0

**No axiom added, none needed.**

> for every `u : ℕ`: **`|G_u| = |(G/H)_{⌈φ_{L/K'}(u)⌉}| · |H_u|`**

(`Anabelian/Quotient/CardMultiplicativity.lean`, `card_ramificationGroup_eq_mul`; with the
generic count `card_subgroup_eq_card_map_mul : |S| = |S.map f|·|ker f ⊓ S|` and the `u = 0`
base `|G_0| = |(G/H)_0|·|H_0|` — `e_{L/K} = e_{K'/K}·e_{L/K'}` at the inertia level).
3 declarations, all standard-axioms-only; probe compiled first try.

```
'Anabelian.card_subgroup_eq_card_map_mul'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.card_ramificationGroup_eq_mul'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.card_ramificationGroup_zero_eq_mul'              depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Generic count: Lagrange (`Subgroup.card_eq_card_quotient_mul_card_subgroup`) on the
  restriction `f|_S`, first isomorphism (`QuotientGroup.quotientKerEquivRange`), and the
  `subgroupOf` bookkeeping (`inf_subgroupOf_right`, `subgroupOfEquivOfLe`).
- Applied to `dq|_{G_u}`: image = `B`-filtration at `⌈φ_{L/K'}(u)⌉` (**Lemma 5**, P73);
  kernel = `range dr ⊓ G_u` (P50) `= (H_u).map dr` (P46), of card `|H_u|` (P46 injective).
- Dividing `u` by `0` gives `(G_0:G_u) = ((G/H)_0:(G/H)_{⌈φ(u)⌉})·(H_0:H_u)` — the
  chain-rule slope identity for `φ_{K'/K} ∘ φ_{L/K'}` in card form (P47's
  `φ' = 1/(G_0:G_u)`).

**Not the cardinal sin / rule-2.** Counting for a given tower — strictly below R1.
Prop. 15 as an equality of functions is NOT claimed (analytic gluing remains). No new
`structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 74 passes.

### Pass 75 (2026-07-03) — the alignment lemma (the gluing's hard step); count stays 0 / 0

**No axiom added, none needed.**

> **the `B`-filtration is constant on integer indices `w ∈ (φ_{L/K'}(n), ⌈φ_{L/K'}(n+1)⌉]`**

(`Anabelian/Quotient/Alignment.lean`: `ramificationGroup_comap_eq_of_lt`, plus the real-`u`
right-slope form `ramificationGroup_comap_floor_add_one_eq` — `(G/H)_{⌊φ(u)⌋+1} =
(G/H)_{⌈φ(n+1)⌉}` for `u ∈ [n, n+1)`). 2 declarations, all standard-axioms-only.

```
'Anabelian.ramificationGroup_comap_eq_of_lt'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_comap_floor_add_one_eq'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

- The flagged hard step of Prop. 15's analytic gluing ("no interior jump of the quotient
  filtration"), closed with NO measure theory by **Pass 72's integrality**: for `σ̄ ≠ 1`,
  `i_{K'/K}(σ̄) = a ∈ ℕ` and `a − 1 = φ_{L/K'}(j(σ̄) − 1)`. Membership in `(G/H)_w` with
  `φ(n) < w` gives `φ(n) < w ≤ a − 1 = φ(j−1)` (both sides of the first inequality
  integers!), so `j − 1 ≥ n+1` by `φ`'s strict monotonicity (P44), so
  `a ≥ φ(n+1) + 1 > ⌈φ(n+1)⌉` (`Nat.ceil_lt_add_one`) — the membership persists to the
  window's right end. The reverse inclusion is the filtration's antitonicity.
- Consequence: the composite `φ_{K'/K} ∘ φ_{L/K'}` has CONSTANT right-slope on each
  `[n, n+1)`, equal to `φ_{L/K}`'s by P74's multiplicativity — the gluing is now pure
  calculus (right-derivatives + `eq_of_has_deriv_right_eq`).

**Not the cardinal sin / rule-2.** A constancy window for a given tower — strictly below
R1. Prop. 15 NOT claimed. No new `structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 75 passes.

### Pass 76 (2026-07-04) — PROP. 15: φ-TRANSITIVITY, PROVED; count stays 0 / 0

**No axiom added, none needed — Serre IV §3 Proposition 15 is a theorem.**

> for EVERY `u : ℝ`: **`φ_{L/K}(u) = φ_{K'/K}(φ_{L/K'}(u))`**

(`Anabelian/Herbrand/Transitivity.lean`, `herbrandPhi_comp`; with
`herbrandPhi_hasDerivWithinAt_Ici` — the right derivative of `φ` is `|G_{⌊u⌋+1}|/|G_0|` at
EVERY `u ≥ 0`, breakpoints included — and `slope_match`). 3 declarations, all
standard-axioms-only.

```
'Anabelian.herbrandPhi_hasDerivWithinAt_Ici'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.slope_match'                                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandPhi_comp'                                depends on axioms: [propext, Classical.choice, Quot.sound]
```

- The four-step plan of the Pass-75 HANDOFF, executed whole: (1) right derivative from
  P48's affine formula via `congr_of_eventuallyEq` on `𝓝[Ici u] u`; (2) chain rule
  (`HasDerivWithinAt.comp`, `MapsTo` from monotonicity); (3) slope match — P75's alignment
  turns the outer index `⌊φ(u)⌋+1` into `⌈φ(⌊u⌋+1)⌉`, P74's multiplicativity (at `⌊u⌋+1`
  and `0`) collapses the product; (4) `eq_of_has_deriv_right_eq` + P44's continuity +
  `φ(0) = 0`; `u ≤ 0` free by `φ = id`.

**Not the cardinal sin / rule-2.** Transitivity for a given tower — strictly below R1.
Prop. 14 (Herbrand) NOT claimed. No new `structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 76 passes.

### Pass 77 (2026-07-04) — HERBRAND'S THEOREM, PROVED; count stays 0 / 0

**No axiom added, none needed — Serre IV §3 Proposition 14 is a theorem.**

> for EVERY `v : ℝ`: **`(G^v).map (decompositionQuotient) = (G/H)^v`**
> — the upper numbering is compatible with quotients.

(`Anabelian/Herbrand/HerbrandTheorem.lean`, `map_upperRamificationGroup_eq`; with
`herbrandPhi_herbrandPsi_eq` and `ramificationGroup_comap_ceil_collapse`.)
3 declarations, all standard-axioms-only.

```
'Anabelian.herbrandPhi_herbrandPsi_eq'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.ramificationGroup_comap_ceil_collapse'           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_upperRamificationGroup_eq'                   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **The ψ-composition** `φ_{L/K'}(ψ_{L/K}(v)) = ψ_{K'/K}(v)`: Prop. 15 (P76) at
  `ψ_{L/K}(v)`, inverted through `ψ_{K'/K}` (P45's inverse identities).
- **The ceil-collapse** `(G/H)_{⌈φ(⌈x⌉)⌉} = (G/H)_{⌈φ(x)⌉}`: NOT an integer identity (the
  indices can differ) — a group equality: for non-integral `x` both indices land in P75's
  alignment window `(φ(⌊x⌋), ⌈φ(⌊x⌋+1)⌉]` where the quotient filtration is constant. The
  HANDOFF's anticipated Lipschitz-1 route was unnecessary — the alignment lemma was
  already the right tool.
- **The assembly**: unfold `G^v = G_{⌈ψ(v)⌉}` (P45), Lemma 5 at `u = ⌈ψ_{L/K}(v)⌉` (P73),
  rewrite by the ψ-composition, close by the ceil-collapse.

**Not the cardinal sin / rule-2.** Quotient-compatibility for a given tower — strictly
below R1. The L3 upgrades (upper numbering on `Gal(K̄/K)`, Hasse–Arf) NOT claimed. No new
`structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 77 passes, and the QUOTIENT ARC (P50–77) IS CLOSED.

### Pass 78 (2026-07-04) — consolidation: the Herbrand package + canonical carrier; count stays 0 / 0

**No axiom added, none needed.** `Anabelian/Herbrand/Main.lean` — the quotient arc's
one-stop summary: all nine headline theorems (Prop. 2 → Prop. 3 → `e' = |H₀|` → numerical
Lemma 5 → Lemma 5 → e-multiplicativity → Prop. 15 → Herbrand → canonical Herbrand) audited
in a single `#print axioms` block, every one standard-axioms-only. One new theorem:

```
'Anabelian.map_upperRamificationGroup_eq_extensionIntegers' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`map_upperRamificationGroup_eq_extensionIntegers`** — Herbrand's theorem on the
  canonical carrier: comparing images in the common ambient `Gal(K'/K) = (K' ≃ₐ[K] K')`
  (via `.subtype`-maps, which avoids all dependent-type transport), the image of
  `G^v(L/K)` equals `G^v(K'/K)` computed on `𝒪_{K'} = extensionIntegers K K'` itself.
  Proof: P77 + `rw [extensionIntegers_comap_eq]` (P57's subring equality) — the
  `B`-vs-`𝒪_{K'}` carrier wart dissolves in two lines.

**Not the cardinal sin / rule-2.** Transport along a proved equality + re-audit — no new
mathematics. No new `structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 78 passes.

### Pass 79 (2026-07-04) — the L2-capstone design pass; count stays 0 / 0

**No axiom added, none needed — and no code: the dependency map is the deliverable**
(CLAUDE.md rule 3: "an honest dependency map showing what stands between current Mathlib
and the next real theorem" is a valid pass product). Recorded in `ROADMAP.md`:

- **Stratum correction**: extending `G^v` to the absolute group is Serre chapter-IV
  material — **L2's capstone**, not L3. The Pass-77/78 "L3 gateway" label named the
  consumer (L3's ramification correspondence), not the stratum, and is retired. L3 (local
  CFT) remains NOT-STARTED.
- **Carrier decision**: `Gal(K^sep/K)` via Mathlib's `separableClosure` +
  `separableClosure.isGalois` — NOT `Field.absoluteGaloisGroup` (`AlgebraicClosure`-based;
  in char `p` the algebraic closure is inseparable over `K` and the automorphism group is
  the wrong object). Char-`p` honesty preserved.
- **Definition decision**: preimage-intersection `G^v(K^sep/K) := ⨅_L proj_L⁻¹ (G^v(L/K))`
  over `L : FiniteGaloisIntermediateField K K^sep` — no category machinery; equivalent to
  the inverse-limit form once B5 (projection surjectivity) is proved. Mathlib stack
  verified present: `finGaloisGroupFunctor`, `continuousMulEquivToLimit`,
  `restrictNormalHom_continuous`, `isOpen_iff_finite`, the fundamental theorem.
- **Soundness check**: the P50–78 arc requires the local-field structure ONLY at the base
  `K` — towers of intermediate fields need no re-basing (`isNonarchimedeanLocalField_
  extension` is off this path).
- **The ladder**: B1 full-group form (transport along `D = ⊤`, P52/P55; P78's
  common-ambient idiom) → B2 intermediate-field plumbing → B3 the `⨅` definition +
  closedness → B4 functorial P77 → B5 projection surjectivity (the real theorem) → B6+
  Hasse–Arf and the abelian filtration.

**Ledger delta: 0 / 0.** Axiom-free — 79 passes.

### Pass 80 (2026-07-04) — B1: the full-group form; count stays 0 / 0

**No axiom added, none needed.** The L2-capstone ladder's first brick
(`Anabelian/Absolute/FullGroup.lean`): the ramification filtrations on the FULL Galois
group, and the finite arc's headline theorems restated along `AlgEquiv.restrictNormalHom`
— the interface the profinite stack consumes. 5 declarations, all standard-axioms-only.

```
'Anabelian.fullRamificationGroup'                           depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullUpperRamificationGroup'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.subtype_comp_decompositionQuotient'              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_fullRamificationGroup_eq'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_fullUpperRamificationGroup_eq'               depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Definitions by `.map (D.subtype)` — P78's common-ambient idiom promoted; `D = ⊤` under
  normality (P52), nothing lost. The square `dq = restrictNormalHom`-conjugated is `rfl`
  (P50 built it that way). The transports (Lemma 5 + **HERBRAND, full-group**:
  `(G^v(L/K)).map (restrictNormalHom K') = G^v(K'/K)`) are each five rewrites:
  `Subgroup.map_map`, the square, `map_map` back, the finite-arc theorem (P73/P77), P57's
  carrier equality.

**Not the cardinal sin / rule-2.** Images of proved filtrations under a fixed inclusion —
no new constraint content (the filtration's rule-2 witnesses live at Pass 23); strictly
below R1. B3's absolute `G^v` and B5's surjectivity NOT claimed. No owed witness; D1/D2
N/A.

**Ledger delta: 0 / 0.** Axiom-free — 80 passes.

### Pass 81 (2026-07-04) — B2 + B4's heart: the profinite tower plumbing; count stays 0 / 0

**No axiom added, none needed.** `Anabelian/Absolute/Tower.lean`: the `≤`-pair plumbing in
EXACTLY Mathlib's `finGaloisGroupMap` conventions, and — ahead of the B-ladder schedule —
**Herbrand's theorem along the profinite transitions**. 5 declarations, all
standard-axioms-only.

```
'Anabelian.leAlgebra'                                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.leAlgebra_isScalarTower'                         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.leAlgebra_finiteDimensional'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.leAlgebra_isGalois'                              depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_fullUpperRamificationGroup_le'               depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `leAlgebra` (an `abbrev` of `RingHom.toAlgebra ∘ Subsemiring.inclusion` — Mathlib's own
  convention, for definitional alignment with `finGaloisGroupFunctor`) + tower
  (`of_algebraMap_eq' rfl`), finite-dimensionality (from the FINITE level — the ambient is
  infinite), `IsGalois` (`tower_top`). Intermediate-field separability: probe-verified
  already a Mathlib instance.
- **`map_fullUpperRamificationGroup_le`**: for `L₁ ≤ L₂` in
  `FiniteGaloisIntermediateField K E`, any separable `E` over the local base,
  `(G^v(L₂/K)).map (restrictNormalHom ↥L₁) = G^v(L₁/K)` — B1's transport fires at
  `(K, ↥L₁, ↥L₂)` under the pair package. The compatible-system property for B3/B5.

**Not the cardinal sin / rule-2.** Plumbing + one instantiation of a proved theorem —
strictly below R1. B3's absolute `G^v` and B5's surjectivity NOT claimed. The `abbrev`
re-packages an existing Mathlib construction — no new constraint content; no owed witness;
D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 81 passes.

### Pass 82 (2026-07-04) — B3: the absolute `G^v` defined; count stays 0 / 0

**No axiom added, none needed.** `Anabelian/Absolute/UpperNumbering.lean`: the upper
numbering on the (possibly infinite) Galois group, its membership, its closedness, and the
easy half of the projection compatibility. 4 declarations, all standard-axioms-only.

```
'Anabelian.absoluteUpperRamificationGroup'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_absoluteUpperRamificationGroup_iff'          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isClosed_absoluteUpperRamificationGroup'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_absoluteUpperRamificationGroup_le'           depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`absoluteUpperRamificationGroup K E v := ⨅_L (G^v(L/K)).comap (restrictNormalHom L)`**
  over `L : FiniteGaloisIntermediateField K E` — the Pass-79 carrier decision realized; at
  `E = K^sep` this is the upper numbering on the absolute Galois group. Stated for ANY
  `E/K` (no def-level separability/Galois hypotheses) — also covers `K^ab` downstream.
- Closedness in the Krull topology: `coe_iInf`/`coe_comap` + preimages of finite discrete
  levels under `InfiniteGalois.restrictNormalHom_continuous`.
- `map_absoluteUpperRamificationGroup_le`: the projection lands inside each finite level
  (`map_le_iff_le_comap` + `iInf_le`). The REVERSE inclusion (B5, projection surjectivity)
  is the capstone's remaining theorem and is NOT claimed.

**Not the cardinal sin / rule-2.** A `def` (an `iInf` of comaps of proved objects) + three
formal properties — no new constraint content (P23 holds the filtration's witnesses);
strictly below R1. No owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 82 passes.

### Pass 83 (2026-07-04) — B5: PROJECTION SURJECTIVITY — the capstone closes, L2 DONE; count stays 0 / 0

**No axiom added, none needed — and the L2 stratum is complete.**

> for Galois `E/K`, every finite Galois subextension `L`, every `v : ℝ`:
> **`(absoluteUpperRamificationGroup K E v).map (restrictNormalHom L) = G^v(L/K)`**

(`Anabelian/Absolute/Surjectivity.lean`, `map_absoluteUpperRamificationGroup_eq`; with
`restrictNormalHom_comp_of_le` and `mem_fullUpper_of_le`). 3 declarations, all
standard-axioms-only; the main proof compiled FIRST TRY.

```
'Anabelian.restrictNormalHom_comp_of_le'                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.mem_fullUpper_of_le'                             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.map_absoluteUpperRamificationGroup_eq'           depends on axioms: [propext, Classical.choice, Quot.sound]
```

- The absolute upper filtration projects ONTO every finite level — the `⨅`-definition
  (P82) is a genuine inverse limit. Compactness on directed closed fibers: nonemptiness by
  **Herbrand along the transitions** (P81; up the tower `L ≤ L ⊔ M`) +
  `restrictNormalHom_surjective`; directedness by FGIF sups + the downward step;
  `CompactSpace Gal(E/K)` + `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_
  isClosed`. Herbrand's theorem is used exactly where Serre uses it: it makes the finite
  levels a compatible system.
- **L2 is DONE** (ROADMAP section header updated): finite-level theory → descent/assembly
  → Herbrand functions → the quotient arc through Herbrand's theorem → the capstone
  `G^v(K^sep/K)` closed + inverse-limit. Hasse–Arf deferred to its own rung;
  norm-compatibility to L3.

**Not the cardinal sin / rule-2.** The capstone of chapter-IV theory for a given base —
strictly below R1; nothing recovered from an abstract group. No new `structure`/`class`;
no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 83 passes, L0–L2 all axiom-free.

### Pass 84 (2026-07-04) — the Absolute consolidation + THE SEPARATION THEOREM; count stays 0 / 0

**No axiom added, none needed.** `Anabelian/Absolute/Main.lean`: the stratum's one-stop
audit (12 declarations in one block, all standard-only), plus four structural dividends —
the new ones:

```
'Anabelian.fullUpperRamificationGroup_antitone'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fullUpperRamificationGroup_of_nonpos'            depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.absoluteUpperRamificationGroup_antitone'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.absoluteUpperRamificationGroup_of_nonpos'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.iInf_absoluteUpperRamificationGroup_eq_bot'      depends on axioms: [propext, Classical.choice, Quot.sound]
```

- Antitonicity (full-group + absolute; P45's mapped/comap'd) and the `v ≤ 0` constancy
  (`ψ = id` + `⌈·⌉₊ = 0`).
- **THE SEPARATION THEOREM** `⨅_v G^v(E/K) = ⊥`: a `σ ≠ 1` moves some `x`; the finite
  Galois subextension `adjoin K {x}` (Mathlib's FGIF adjoin) sees it; there the filtration
  is eventually `⊥` (P45's `upperRamificationGroup_eventually_bot` + P29's Noetherian
  separation at `𝒪_L`); `restrictNormal_commutes` transfers triviality back to `σ` at
  `x`. The absolute filtration is now: defined, closed, an inverse limit, antitone,
  normalized at `v ≤ 0`, and SEPARATING — the complete chapter-IV package.

**Not the cardinal sin / rule-2.** Consolidation + structural lemmas for a given base —
strictly below R1 (which of these filtrations is group-theoretically DETECTABLE is the R1
question, untouched). No new `structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 84 passes.

### Pass 85 (2026-07-04) — the L3 opening inventory (design pass); count stays 0 / 0

**No axiom added, none needed — and no code: the dependency map is the deliverable**
(CLAUDE.md rule 3, as at Passes 79/85). ROADMAP's L3 section rewritten from a three-line
stub to a five-stage ladder with the July-2026 Mathlib inventory recorded:

- **PRESENT**: group cohomology with explicit `H⁰/H¹/H²`, LES, functoriality, Shapiro,
  **Hilbert 90**, **finite-cyclic periodicity** (the Herbrand-quotient substrate); group
  homology; nascent continuous cohomology; CSA definitions; 1-dim formal group laws.
- **ABSENT**: Tate cohomology, inflation–restriction, cup products, `Br ≃ H²`, the
  invariant map, class formations, Lubin–Tate, norm groups, the existence theorem, any
  `K^ab` object, local/global CFT proper. External Lean developments
  (`mariainesdff/LocalClassFieldTheory`, the FLT project) not in this pin; porting = a
  `FOUNDATIONAL`-vs-`DEBT` decision deferred to the L3.3 gate.
- **The ladder**: L3.0 `K^ab` interface (unblocked; `G^v(K^ab/K)` already expressible via
  P82) → L3.1 cyclic/Herbrand-quotient layer (unblocked; Mathlib's `FiniteCyclic` +
  `Hilbert90` + the project's P24–27 residue characters) → L3.2 unramified cohomology
  (medium; P38–43 completeness strengths) → **L3.3 RECIPROCITY (the wall; route decision:
  Neukirch-style abstract CFT — inputs are exactly L3.1+L3.2, avoiding absent `Ĥ`/cup
  machinery and from-zero formal groups; revisit at the gate)** → L3.4 the ramification
  correspondence `θ(U^n) = G^n(K^ab/K)` (the R1-relevant piece).

**No stub taken; nothing axiomatized.** The wall is named, gated, and routed — not
crossed on paper.

**Ledger delta: 0 / 0.** Axiom-free — 85 passes.

### Pass 86 (2026-07-04) — L3.0: `K^ab` exists; count stays 0 / 0

**No axiom added, none needed.** The L3 ladder's first rung — the stage of local class
field theory — `Anabelian/ClassField/MaximalAbelian.lean` (the stratum's first file).
7 declarations, all standard-axioms-only.

```
'Anabelian.commutatorClosure'                               depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.maximalAbelianSubextension'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.fixingSubgroup_maximalAbelianSubextension'       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.isGalois_maximalAbelianSubextension'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.maximalAbelianGalEquiv'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.maximalAbelianSubextension_mul_comm'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.le_maximalAbelianSubextension'                   depends on axioms: [propext, Classical.choice, Quot.sound]
```

- `maximalAbelianSubextension K E` := the fixed field of the closed commutator subgroup
  (fundamental theorem of infinite Galois theory; at `E = K^sep`: `K^ab`). `IsGalois`
  (via `normal_iff_isGalois` + the correspondence's `fixingSubgroup_fixedField`);
  `Gal(K^ab/K)` = the topological abelianization (`normalAutEquivQuotient`), ABELIAN
  (commutators die in the quotient); **maximality PROVED** (`le_maximalAbelianSubextension`
  — the claiming name carries its justification theorem, per rule-2 discipline);
  `G^v(K^ab/K)` fires as-is (P82's generality, by design).

**Not the cardinal sin / rule-2.** Definitional rung with its own maximality witness —
strictly below R1; the reciprocity map (L3.3) NOT claimed. No new `structure`/`class`; no
owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 86 passes.

### Pass 87 (2026-07-04) — L3.1 opens: the Herbrand quotient; count stays 0 / 0

**No axiom added, none needed.** The cyclic layer's bookkeeping device — verified NOT in
Mathlib — built abstractly. `Anabelian/ClassField/HerbrandQuotient.lean`, 6 declarations,
all standard-axioms-only.

```
'Anabelian.range_le_ker'                                    depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandH'                                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandQuotient'                                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.card_ker_eq_card_herbrandH_mul'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.card_eq_card_ker_mul_card_range'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.herbrandQuotient_eq_one_of_finite'               depends on axioms: [propext, Classical.choice, Quot.sound]
```

- The two-endomorphism form (Serre VIII §4): `herbrandH f g = ker f ⧸ im g` on a
  `CommGroup` with `f∘g = g∘f = 1`; `herbrandQuotient : ℚ`; for a cyclic action
  (`f = N`, `g = σ/1`) these are `Ĥ⁰ = H²` and `Ĥ¹ = H¹` — matching Mathlib's
  `FiniteCyclic` periodicity isos (that bridge: a later brick).
- **The triviality theorem**: finite `M` ⟹ `q(M) = 1` — `|ker f|·|im f| = |M| =
  |ker g|·|im g|` by the P74 Lagrange/first-isomorphism idiom; the exact-sequence calculus
  will use it to discard finite error terms.

**Not the cardinal sin / rule-2.** Abstract bookkeeping strictly below the reciprocity
wall; no CFT claimed. `herbrandH` is a plain quotient `def`; the pair hypotheses appear
only in theorems that visibly use them; no sharpness claimed, no witness owed; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 87 passes.

### Pass 88 (2026-07-04) — the exact-cycle count + herbrandH functoriality; count stays 0 / 0

**No axiom added, none needed.** Two sub-bricks of `q`-multiplicativity
(`Anabelian/ClassField/ExactCycle.lean`, 4 declarations, all standard-axioms-only —
`kerRestrict` needs only `propext`).

```
'Anabelian.card_eq_card_ker_mul_card_range''                depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.card_prod_eq_of_exact_cycle'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.kerRestrict'                                     depends on axioms: [propext]
'Anabelian.herbrandHMap'                                    depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **The 6-cycle alternating-card lemma**: `|A₀||A₂||A₄| = |A₁||A₃||A₅|` for a periodic
  exact sequence — six explicit groups (ZMod-6 indexing hits dependent-type transport),
  NO finiteness hypotheses (the linter itself flagged them unused — `Nat.card = 0`
  conventions carry the identity); each `|Aᵢ| = |im dᵢ₋₁|·|im dᵢ|` and the triple
  products both collect all six ranges.
- **`herbrandHMap`**: pair-intertwining homs induce maps on the Herbrand carriers
  (`kerRestrict` + `QuotientGroup.map`) — the four functorial arrows of the coming
  six-term cycle.

**Not the cardinal sin / rule-2.** Infrastructure below the multiplicativity theorem,
which is NOT claimed (connecting maps + exactness named as next work). No new
`structure`/`class`; no owed witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 88 passes.

### Pass 89 (2026-07-04) — the snake: the connecting homomorphism; count stays 0 / 0

**No axiom added, none needed.** The hard brick of `q`-multiplicativity
(`Anabelian/ClassField/Snake.lean`, 7 declarations, all standard-axioms-only).

```
'Anabelian.snakePull'                                       depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.snakeY'                                          depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.snakePhi'                                        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.snakePsi'                                        depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.snakePhi_ker_le'                                 depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.snakeDelta'                                      depends on axioms: [propext, Classical.choice, Quot.sound]
'Anabelian.snakeDelta_apply'                                depends on axioms: [propext, Classical.choice, Quot.sound]
```

- **`snakeDelta : Ĥ⁰(M'') →* Ĥ¹(M')`** for a pair-equivariant SES, with the computation
  rule `δ(Φ x) = ψ x`. The design kills the classical cocycle bookkeeping: the pullback
  `Y` is a genuine HOM on the lift domain `T = π⁻¹(ker f'')` (`ι`-injectivity forces
  multiplicativity), and the two-step well-definedness merges into the single kernel
  condition `ker Φ ≤ ker ψ`; `δ` is the first-isomorphism factorization. The
  `(f,g)`-swap gives the periodic partner with no new code.

**Not the cardinal sin / rule-2.** Homological infrastructure below the multiplicativity
theorem (NOT yet claimed — exactness remains). No new `structure`/`class`; no owed
witness; D1/D2 N/A.

**Ledger delta: 0 / 0.** Axiom-free — 89 passes.
