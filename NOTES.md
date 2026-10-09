# NOTES.md

Per-pass record: what was proved, the ledger delta, which Mathlib API did the real work, rule-2
evidence for any new structure, and an honest scope paragraph.

---

# Pass 0 — orientation, inventory, seed lemma (2026-05-30)

**Toolchain.** Lean 4 + Mathlib pinned to the stable tag `v4.30.0`
(`lake-manifest` rev `v4.30.0`, Mathlib commit `c5ea00351c`). `lake init … math` →
`lake exe cache get` (8459 cached oleans, no source build). Clean baseline build, then clean
build with content. Mathlib's style linters (`weak.linter.mathlibStandardSet`) are **on** and the
committed file passes them with zero warnings.

## Honest scope (governs this pass)

This pass proves **no anabelian theorem** and makes no claim of progress toward one. Its deliverable
is a *truthful map* of the gap between current Mathlib and the first real target, plus a *clean
compiling floor* with one small axiom-free lemma touching the project's actual subject. The end
target — mono-anabelian reconstruction of a field from its absolute Galois group — is hard, partly
unformalized frontier mathematics; its classical predecessor Neukirch–Uchida is itself plausibly a
multi-year sub-target and is not in Mathlib. Nothing here is near either. See `ROADMAP.md` for the
honest distance and `AXIOM_LEDGER.md` for the (currently empty) debt.

## Pre-search predictions vs. reality (the self-correction the pass demanded)

I recorded predictions before searching, then searched and corrected them. Net: **I underestimated
Mathlib's coverage of the Galois/profinite *upper* layer, and was right that the arithmetic *lower*
layer (CFT, higher ramification) is largely absent.**

| Area | I predicted | Reality | Verdict |
|------|-------------|---------|---------|
| Profinite groups | PRESENT | PRESENT (`ProfiniteGrp`) | ✓ right |
| Infinite Galois fund. thm. | PARTIAL→PRESENT (hedged) | **PRESENT, complete** | ✗ too cautious |
| Absolute Galois group | PARTIAL ("constructible, unnamed") | **PRESENT, packaged** | ✗ too pessimistic |
| Local fields | PARTIAL ("typeclass uncertain") | **typeclass PRESENT**, theory PARTIAL | ✗ partly wrong |
| Ramification: decomp/inertia | PARTIAL | PARTIAL | ✓ right |
| Higher ramification (numbering) | ABSENT | ABSENT | ✓ right |
| Local class field theory | ABSENT | ABSENT (exists externally) | ✓ right |
| Anabelian / reconstruction | ABSENT | ABSENT | ✓ right |

Where I was wrong I was *too pessimistic about the Galois side*: the absolute Galois group is a
named, packaged object and the full infinite Galois correspondence is already a theorem. This is
good news — it is exactly the floor the seed lemma stands on, and it raises the starting altitude of
rung L0→L1.

## The inventory (Step 2) — actual state, with real names

Every PRESENT claim cites a real declaration; every ABSENT claim is a genuine "searched, found
nothing" (search method: directory walks, `rg` over `.lake/packages/mathlib/Mathlib`, and `#check` /
`#synth` in a throwaway `lake env lean` probe — the probe has been deleted).

### 1. Profinite groups and their topology — **PRESENT**
- `ProfiniteGrp` — category of profinite groups, `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean`
  (+ `Limits.lean`, `Completion.lean`).
- `Profinite` — category of profinite spaces, `Mathlib/Topology/Category/Profinite/Basic.lean`
  (with `AsLimit`, cofiltered limits, Nöbeling). Profinite = compact + T2 + totally disconnected via
  the standard topology API; `OpenSubgroup`, `ClosedSubgroup`, `ContinuousMonoidHom` all present.

### 2. Fundamental theorem of infinite Galois theory — **PRESENT (complete)**
- `InfiniteGalois.IntermediateFieldEquivClosedSubgroup [IsGalois k K] :`
  `IntermediateField k K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ` — the order-reversing bijection,
  `Mathlib/FieldTheory/Galois/Infinite.lean`.
- Supporting: `fixedField_fixingSubgroup` (= `fixedField ∘ fixingSubgroup = id`),
  `fixingSubgroup_fixedField`, `fixingSubgroup_isClosed`, `isOpen_iff_finite`
  (open ↔ finite-dim'l), `normal_iff_isGalois`, `mem_bot_iff_fixed`.
- Krull topology on `Gal(K/k)`: `Mathlib/FieldTheory/KrullTopology.lean`.
- Profinite realization: `InfiniteGalois.profiniteGalGrp [IsGalois k K] : ProfiniteGrp` and
  `continuousMulEquivToLimit`, `instance : CompactSpace Gal(K/k)`,
  `Mathlib/FieldTheory/Galois/Profinite.lean`. The Galois group *is* an inverse limit of finite ones.

### 3. Absolute Galois group `Gal(K^sep/K)` — **PRESENT**
- `Field.absoluteGaloisGroup (K) [Field K] : Type := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`,
  `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`; plus `absoluteGaloisGroupAbelianization` (the
  topological abelianization) and `commutator_closure_isNormal`.
- Notation `Gal(L/K) := L ≃ₐ[K] L`, `Mathlib/FieldTheory/Galois/Notation.lean`.
- Caveat (recorded for downstream): it is built on `AlgebraicClosure K`, so it equals
  `Gal(K̄/K)`. This is Galois over `K` iff `K` is **perfect** (for general `K` one wants
  `separableClosure`). The instance `[PerfectField K] → IsGalois K (AlgebraicClosure K)` *does*
  synthesize; but `PerfectField ℚ` is **not** found automatically by instance search (needs to be
  supplied). `separableClosure F E` and `separableClosure.isGalois` are present for the general case.

### 4. Local fields — **definition PRESENT, theory PARTIAL**
- `IsNonarchimedeanLocalField (K) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop`
  (Andrew Yang, 2025), `Mathlib/NumberTheory/LocalField/Basic.lean`. Derives DVR `𝒪[K]`, **finite**
  residue field `𝓀[K]`, completeness, compactness of `𝒪[K]`, adic completeness.
- `Padic`, `PadicInt` and valuation/DVR machinery: `Mathlib/NumberTheory/Padics/*`,
  `Mathlib/RingTheory/Valuation/*`, `Mathlib/RingTheory/DiscreteValuationRing/*`.
- **Missing**: the Galois theory of local fields (structure of `Gal(K̄/K)`, unramified/tame/wild),
  archimedean local fields as part of a unified `LocalField`. → rung L1.

### 5. Ramification theory — **PARTIAL**
- `Ideal.ramificationIdx`, `Ideal.inertiaDeg` (the `e`, `f`): `Mathlib/RingTheory/RamificationInertia/*`,
  `Mathlib/NumberTheory/RamificationInertia/*` (incl. `Galois.lean` with `inertiaDegIn`).
- Decomposition / inertia **subgroups** (Galois-theoretic): `ValuationSubring.decompositionSubgroup`,
  `ValuationSubring.inertiaSubgroup`, and the decomposition→residue-field automorphism map,
  `Mathlib/RingTheory/Valuation/RamificationGroup.lean`.
- **Missing**: higher ramification groups — the filtration `G_i` (lower numbering), Herbrand `ψ/φ`,
  upper numbering `G^v`, Hasse–Arf. Searched (`ramificationGroup`, `lowerNumbering`, `upperNumbering`,
  `herbrand`): **ABSENT**. → rung L2.

### 6. Local class field theory (reciprocity `K^× → Gal^ab`) — **ABSENT**
- No reciprocity / norm-residue / Artin map for local or global fields in Mathlib (searched
  `reciprocity`, `artinmap`, `normresidue`, `class field` — only quadratic reciprocity and unrelated
  "Frobenius reciprocity" of category theory).
- **Exists outside Mathlib**: `github.com/mariainesdff/LocalClassFieldTheory`, referenced from
  `Mathlib/RingTheory/Valuation/Discrete/Basic.lean`. → rung L3 (candidate `FOUNDATIONAL` import).

### 7. Anabelian / reconstruction statements — **ABSENT** (as expected)
- No `anabelian`, `Uchida`, `mono-anabelian`, `section conjecture`. The 15 "Neukirch" hits are all
  bibliography citations to Neukirch's *Algebraic Number Theory* textbook (Dedekind domains,
  ramification, norms) — **not** the Neukirch–Uchida theorem. Confirmed absent.

### Extra (the Neukirch–Uchida prerequisites, rung L4)
- **Chebotarev density theorem**: ABSENT (0 hits).
- **Global Artin reciprocity** / idele-class reciprocity: ABSENT.
- **Arithmetic Frobenius** at unramified primes: PARTIAL (cyclotomic `NumberField/Cyclotomic/Galois.lean`,
  finite-field `GaussSum.lean`; no general API).
- Adele rings: PRESENT (`NumberField.AdeleRing`, `FiniteAdeleRing`, `InfiniteAdeleRing`).
- Hermite–Minkowski discriminant bound: PRESENT (`NumberField.abs_discr_gt_two`).

## The seed lemma (Step 3)

File `Anabelian/Basic.lean`. Two theorems, **standard axioms only** (audited in-file via
`#print axioms`, re-run every build):

- `Anabelian.fixingSubgroup_injective [IsGalois k K] :`
  `Function.Injective (IntermediateField.fixingSubgroup : IntermediateField k K → Subgroup Gal(K/k))`.
- `Anabelian.absoluteGaloisGroup_fixingSubgroup_injective (K) [Field K] [PerfectField K] :` the same
  for `IntermediateField K (AlgebraicClosure K) → Subgroup (Field.absoluteGaloisGroup K)`.

**Genuine content, or smoke test?** *Mild genuine content, honestly characterized.* The statement —
faithfulness of the Galois correspondence: distinct intermediate fields have distinct fixing
subgroups, equivalently a subextension is recoverable as the fixed field of its subgroup — is the
**most primitive precondition of anabelian reconstruction** (if it failed, no group could determine
its field). The proof is a three-line consequence of `InfiniteGalois.fixedField_fixingSubgroup`
(`fixedField` is a left inverse of `fixingSubgroup` ⟹ injective), so it is *light*: it adds a
clean, citable derived form rather than new mathematics. It is more than a pure API smoke test
because the specialization to `Field.absoluteGaloisGroup` of a perfect field places it squarely in
the project's subject and verifies the perfect-field `IsGalois` plumbing the project will lean on.

**What it is NOT.** Not reconstruction. The map uses the *given* action of `Gal(K/k)` on the *given*
`K`; it recovers a *sub*field of a given field, not the field from an abstract group. The hard
converse (an abstract topological-group isomorphism of absolute Galois groups is induced by a field
isomorphism — Neukirch–Uchida, then mono-anabelian) is untouched and is the multi-year target.

**Mathlib API that did the real work**: `InfiniteGalois.fixedField_fixingSubgroup` (hence, under the
hood, the fundamental theorem of infinite Galois theory), `Field.absoluteGaloisGroup`, and the
instance `[PerfectField K] → IsGalois K (AlgebraicClosure K)`.

## Ledger delta

**0 added / 0 discharged.** Zero `DEBT`, zero `FOUNDATIONAL`. Correct pass-0 outcome
(`AXIOM_LEDGER.md`).

## Rule-2 (constructible-bad-model) evidence

**N/A this pass — no new `structure`/`class` was introduced.** The only definitions are two
theorems reusing Mathlib structures (`IntermediateField`, `Subgroup`, `IsGalois`, `PerfectField`).
The first pass that introduces an anabelian `structure`/`class` (expected around rung L1/R1) must
supply: two genuinely different models that come apart on what the structure pins, and a hypothesis
whose removal is a *proved* failure. Flagged here so it is not forgotten.

## Pointer to Pass 1

The honest next concrete step is **rung L1** groundwork: inventory Mathlib's `ValuativeRel` /
local-field API in depth and prove a small axiom-free lemma about `Gal(K̄/K)` for a local or finite
field (e.g. relating the unramified quotient to `Gal(𝔽_q̄/𝔽_q)`), still introducing zero `DEBT`.
Resist the urge to `axiom` local CFT (L3) before its prerequisites — and never `axiom` R1/R2/R3.

---

# Pass 1 — rung L1: finite-field absolute Galois group is commutative (2026-05-30)

## Honest scope (governs this pass)

This pass stays at **rung L1** (Galois theory of local/finite fields) and proves **no reconstruction
(R1–R3)** result. The one lemma takes a finite field `F` and the *given* action of its Galois group
on the *given* algebraic closure `F̄`, and proves a structural property of that group. It recovers
nothing from an abstract topological group, so it does not and cannot approach the reconstruction
targets. Step 0 also hardened the governance files against multi-year reclassification drift
(below). Ledger delta: **0 / 0**.

## Step 0 — ledger / roadmap hardening (bookkeeping, no axioms)

- `AXIOM_LEDGER.md`: added a **Reclassification rule** (no silent `DEBT ⇄ FOUNDATIONAL` moves; each
  needs a dated, justified entry) and an (empty) **Reclassification log**. Rationale: the insidious
  multi-year failure is quietly relabeling a hole-we-owe as a boundary-we-accept.
- `ROADMAP.md`: each target now lists its **permitted `FOUNDATIONAL` inputs** — R1: {L1,L2,L3};
  R2: {L1,L2,L3,L4}, R1 must be proved; R3: {L1,L2,L3,L4}, R1+R2 must be proved. Principle: **only
  L-rungs may ever be `FOUNDATIONAL`; R-rungs (targets) must always be earned.**

## Deepened L1 inventory (verify, don't guess — real names)

### Finite-field Galois API — **PRESENT, and richer than expected**
- `IsCyclic Gal(L/K)` — **instance** for finite `L` (`FieldTheory/Finite/Basic.lean:402`): the
  Galois group of a finite extension of finite fields is cyclic (Frobenius-generated).
- `FiniteField.frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : Gal(L/K)` (Basic.lean:360),
  with `coe = (· ^ q)`; `orderOf_frobeniusAlgEquivOfAlgebraic = Module.finrank K L` (386);
  `bijective_frobeniusAlgEquivOfAlgebraic_pow` (397).
- `FiniteField.exists_forall_apply_eq_pow (l) [Finite l] (g : Gal(l/k)) : ∃ i, ∀ x, g x = x^(#k^i)`
  (`Finite/Extension.lean:143`); `Extension.frob`, `card_algEquiv_extension`, `GaloisField p n`.

### Supporting instances — **PRESENT**
- `PerfectField F` for finite `F` (confirmed by `#synth`), hence `IsGalois F (AlgebraicClosure F)`.
- `[IsAlgClosed K] → Infinite K` — instance (`IsAlgClosed/Basic.lean:387`).
- `FiniteGaloisIntermediateField` (`Galois/GaloisClosure.lean:36`) with `.adjoin` / `subset_adjoin`
  (109/126), and `IsGalois` + `FiniteDimensional` instances — a finite Galois subextension on demand.
- `AlgEquiv.restrictNormalHom` (a `MonoidHom`, `Normal/Defs.lean:195`), `restrictNormalHom_apply`
  (198), `restrictNormal_commutes` (176).
- `Module.finite_of_finite (R) [Finite R] [Module.Finite R M] : Finite M`
  (`RingTheory/Finiteness/Cardinality.lean:73`).
- `IsCyclic.isMulCommutative` (instance, cyclic ⟹ commutative) and `mul_comm'` (the
  `IsMulCommutative` mixin accessor `a * b = b * a`, `Algebra/Group/Defs.lean:224`).
- `normal_of_isMulCommutative` (abelian ⟹ subgroups normal) — for the deferred come-apart witness.

### **ABSENT** (logged as L1 sub-targets in `ROADMAP.md`)
- `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` / procyclic / Frobenius as topological generator. (Mathlib has a general
  profinite-completion functor `ProfiniteGrp/Completion.lean`, but not this identification.)
- The unramified quotient surjection `Gal(K̄/K) ↠ Gal(𝔽_q̄/𝔽_q)` for local `K`; the tame/wild filtration.
- **Any** commutativity / abelian / procyclic statement for finite-field Galois groups — confirming
  this pass's lemma is genuinely new content, not a Mathlib restatement.
- A ready non-abelian Galois example / non-normal extension witness (none found; `X^3-2` not Galois
  is not in Mathlib).

### Pre-search predictions vs. reality (point (iii) of the restatement)

| I predicted | Reality | Verdict |
|-------------|---------|---------|
| finite-field perfectness is an instance | PRESENT | ✓ |
| Frobenius endo + bijectivity present | PRESENT (+ as a generating `AlgEquiv`, with order lemma) | ✓ (under-counted) |
| finite-level `Gal(𝔽_{q^n}/𝔽_q)` cyclic | PRESENT, **as an instance** | ✓ (stronger than expected) |
| `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` assembled | ABSENT | ✓ |
| Frobenius topological generator | ABSENT | ✓ |
| local unramified-quotient surjection | ABSENT | ✓ |

Net: predictions accurate. I slightly *under*-estimated how packaged the finite API is (cyclicity is
a ready instance; Frobenius is a ready `AlgEquiv` with order/bijectivity lemmas). Crucially,
commutativity of the *absolute* group is **not** in Mathlib — so the lemma is new.

## The lemma (Step 2) and self-audit (Step 3)

`Anabelian/FiniteField.lean`, standard axioms only (in-file `#print axioms`):
- `Anabelian.absoluteGaloisGroup_mul_comm (F) [Field F] [Finite F] (σ τ : Gal(AlgebraicClosure F/F))`
  `: σ * τ = τ * σ` — the absolute Galois group of a finite field is commutative.
- `instance finiteField_absoluteGaloisGroup_isMulCommutative : IsMulCommutative (Field.absoluteGaloisGroup F)`
  — the reusable mixin form on the named object (`Gal(AlgebraicClosure F/F) = Field.absoluteGaloisGroup F`
  by definition).

**Genuine L1 content, not a smoke test, not a Pass-0 restatement.** Pass 0 proved a property of
*every* Galois extension via the abstract correspondence — silent on *which* group occurs. This is a
property of a *specific* infinite profinite absolute Galois group, **special to finite fields**: the
absolute Galois group of a general field is highly non-abelian. Not every instance satisfies it
(perfect infinite fields fail), so it is not vacuous. It exercises finite-field-specific API (the
`IsCyclic` instance, `FiniteGaloisIntermediateField.adjoin`, `restrictNormalHom`, `Module.finite_of_finite`)
untouched by Pass 0, and downstream it is the prototype of the abelian unramified-local Galois
structure that L3/R1 use.

**Does NOT reach toward reconstruction.** The map is the *given* action of `Gal(F̄/F)` on the *given*
`F̄`; nothing is recovered from an abstract group. Stated explicitly in the file docstring.

**Load-bearing hypothesis.** `[Finite F]` is essential, used twice in the proof: (i)
`Module.finite_of_finite F` makes each finite-dimensional subextension a *finite field*; (ii) over a
finite field every finite Galois group is *cyclic* hence commutative. The come-apart: `Gal(ℚ̄/ℚ)` is
non-abelian (the non-normal `ℚ(∛2)/ℚ` would, under abelianness ⟹ all subgroups normal ⟹ all
subextensions Galois via `normal_iff_isGalois`, be forced Galois — contradiction). **This witness is
not formalized this pass** — no non-normal-extension API exists in Mathlib and building one is a
separate construction; it is logged as an L1 micro-target in `ROADMAP.md`. No `structure`/`class`
is introduced, so the formal rule-2 obligation does not bind; the load-bearing hypothesis is
documented in lieu, honestly marked as asserted-not-proved.

**Proof shape.** `AlgEquiv.ext`; for each `x`, take the finite Galois subextension
`M = FiniteGaloisIntermediateField.adjoin F {x}` (a finite field), where `Gal(M/F)` is cyclic
(`IsCyclic`) hence commutative (`mul_comm'`); restrict `σ, τ` via the `MonoidHom`
`restrictNormalHom`, so `σ·τ` and `τ·σ` have equal restrictions, then transport back to `x` with
`restrictNormalHom_apply`.

## Ledger delta & rule-2

- **0 added / 0 discharged.** Zero `DEBT`, zero `FOUNDATIONAL`. (Plus Step-0 anti-drift hardening.)
- Rule-2: no new `structure`/`class`. Load-bearing hypothesis documented; formal come-apart deferred.

## Pointer to Pass 2

Natural next L1 steps (still targeting zero `DEBT`): (a) `Gal(𝔽_q̄/𝔽_q)` is *procyclic* / the
Frobenius topologically generates / `≅ Ẑ`; (b) the residue-reduction surjection
`Gal(K̄/K) ↠ Gal(𝔽_q̄/𝔽_q)` for a local field `K`, tying the abstract `inertiaSubgroup` to the
unramified picture; or (c) formalize the deferred non-abelian witness (`Gal(ℚ̄/ℚ)` non-commutative)
to upgrade Pass 1's load-bearing claim from asserted to proved.

---

# Pass 2 — rung L1 continued: finite-field absolute Galois group is procyclic (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The two lemmas concern the action of the
*given* Frobenius on the *given* `𝔽_q̄`; nothing is recovered from an abstract group. Step 0 closed a
discipline gap (rule-2 for theorems). Ledger delta: **0 DEBT / 0 FOUNDATIONAL**; one Owed witness
(**W1**) added and tracked, none discharged.

## Step 0 — closing the rule-2 letter/spirit gap (no axioms)

- `CLAUDE.md`: rule-2 now binds **theorems with a claimed load-bearing hypothesis**, not only
  `structure`/`class`. A pass claiming a hypothesis is load-bearing must either prove the
  failure-when-dropped or register an **Owed witness**; "optional" is banned. This closes exactly the
  erosion the `iutt` project warned of — enforcing the named case while letting the analogous case
  slip.
- `AXIOM_LEDGER.md`: new **Owed witnesses** section (distinct from axioms — these are unproved
  load-bearing claims, a debt of rigor, not a kernel assumption). Pass 1's prose-only `[Finite F]`
  claim is now **W1**, tracked, supporting both the commutativity and procyclicity lemmas.

## Deepened L1 inventory (real names; verify, don't guess)

- `coe_frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : ⇑(frobeniusAlgEquivOfAlgebraic K L) = (· ^ q)`,
  `q = Fintype.card K` (`Finite/Basic.lean`). The Frobenius element exists on `AlgebraicClosure K`
  (def is before `variable [Finite L]`).
- `bijective_frobeniusAlgEquivOfAlgebraic_pow K L` (finite `L`): powers of Frobenius enumerate
  `Gal(L/K)` — the char-free generator fact (no `CharP`/`Fact p.Prime` needed, unlike
  `exists_forall_apply_eq_pow`, which is gated on `(p) [Fact p.Prime] [CharP k p]`).
- `IntermediateField.mem_fixedField_iff`, `IntermediateField.fixingSubgroup_bot`
  (`fixingSubgroup ⊥ = ⊤`, `Galois/Basic.lean:257`), `InfiniteGalois.mem_bot_iff_fixed`,
  `InfiniteGalois.fixingSubgroup_fixedField` (for `ClosedSubgroup`).
- `Subgroup.topologicalClosure`, `Subgroup.le_topologicalClosure`,
  `Subgroup.isClosed_topologicalClosure`; `ClosedSubgroup` (carrier + closedness).
- `Module.finite_of_finite`, `SubmonoidClass.coe_pow`, `mul_comm'`/`FiniteField.pow_card` (Pass 1).
- **Correction to a pre-search guess:** I expected to prove infiniteness via "Frobenius has infinite
  order." **Wrong** — `orderOf_frobeniusAlgEquivOfAlgebraic` is gated on `[Finite L]`, so it does not
  apply to the infinite `AlgebraicClosure`. Pivoted to the fixed-field/correspondence route.
- **ABSENT (still):** `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (no `Ẑ` identification); a non-normal-extension /
  non-abelian-Galois-group API (so W1 cannot be discharged for free).

### Pre-search expectations vs. reality (point (iv))

| I expected | Reality | Verdict |
|------------|---------|---------|
| full `≅ Ẑ` out of reach axiom-free | out of reach (no `Ẑ` iso) | ✓ |
| non-abelian witness (a) likely out of reach | out of reach *for free* (API absent), but viable via AbelRuffini route | ✓ (refined) |
| residue surjection (c) hardest | not attempted; needs absent local machinery | ✓ |
| generation fragment reachable | **reached**: `fixedField (zpowers Frob) = ⊥` and `topologicalClosure = ⊤` | ✓ |
| infinite-order route for infiniteness | **blocked** (`orderOf` gated on `[Finite L]`) | ✗ corrected |

## The lemmas (Step 1) and self-audit (Step 2)

`Anabelian/FiniteField.lean`, standard axioms only (in-file `#print axioms`):
- `frobenius_zpowers_fixedField (K) [Field K] [Fintype K] :`
  `IntermediateField.fixedField (Subgroup.zpowers (frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))) = ⊥`.
- `frobenius_topologicalClosure_eq_top (K) [Field K] [Fintype K] :`
  `(Subgroup.zpowers (frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))).topologicalClosure = ⊤`
  — **Frobenius topologically generates** `Gal(𝔽_q̄/𝔽_q)` (procyclicity).

**Genuine L1 content, not a restatement.** This is *procyclicity*, strictly stronger than Pass 1's
*commutativity* (procyclic ⟹ abelian). It is special to finite fields, not in Mathlib, and uses the
finite-field Frobenius API + the infinite Galois correspondence (the closure↔fixed-field step) that
Pass 1 did not. Not a smoke test: it is false for general fields.

**Recovers nothing from an abstract group.** Both statements are about the given Frobenius acting on
the given `𝔽_q̄`; no reach toward R1–R3. Stated in the file docstring.

**Load-bearing hypothesis — now handled per the extended rule-2.** `[Fintype K]` is load-bearing
(procyclicity fails for infinite fields). The come-apart is the same as Pass 1's and is registered as
**W1** (Owed witnesses), *not* left as prose. Assessed option (a) to discharge W1 this pass:
reachable in principle (AbelRuffini gives a non-solvable, hence non-abelian, `Gal` over `ℚ`;
`restrictNormalHom_surjective` pushes non-commutativity up to `Gal(ℚ̄/ℚ)`), but it needs the splitting
field realized inside `AlgebraicClosure ℚ` — a separate construction, out of scope for one clean
lemma. Left owed with the route recorded.

**Proof shape.** `frobenius_zpowers_fixedField`: `x` fixed by Frobenius ⟹ `x^q = x` ⟹ `x^(q^j)=x`;
then for any `g`, restrict to the finite Galois `M = adjoin K {x}`, where
`bijective_frobeniusAlgEquivOfAlgebraic_pow` writes `g|_M` as a Frobenius power, giving
`g x = x^(q^j) = x`; conclude `x ∈ ⊥` via `mem_bot_iff_fixed`.
`frobenius_topologicalClosure_eq_top`: the closure is a larger subgroup, so its fixed field is `≤`
the (already `⊥`) fixed field of `zpowers Frobenius`; a closed subgroup with fixed field `⊥` is `⊤`
by `fixingSubgroup_fixedField` + `fixingSubgroup_bot`.

## Ledger delta & rule-2

- **0 DEBT / 0 FOUNDATIONAL.** Owed witnesses: **+1 (W1, open)**, 0 discharged.
- Rule-2: no new `structure`/`class`. The load-bearing `[Fintype K]` claim is discharged-or-owed per
  the new rule — here **owed (W1)**, properly tracked.

## Pointer to Pass 3

(a) Discharge **W1** (`Gal(ℚ̄/ℚ)` non-abelian via the AbelRuffini route) — would close the first owed
witness and demonstrate the extended rule-2 biting. (b) Push procyclicity to `≅ Ẑ` (build/identify
`Ẑ`). (c) The local residue surjection `Gal(K̄/K) ↠ Gal(𝔽_q̄/𝔽_q)`. All still target zero `DEBT`.

---

# Pass 3 — rung L1: discharge W1 (ℚ's absolute Galois group is non-commutative) (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The lemma is a property of the Galois
action on the *given* field ℚ and its *given* algebraic closure — it shows `Gal(ℚ̄/ℚ)` is
non-commutative; it recovers nothing from an abstract group. Step 0 hardened the Owed-witnesses
convention against *route-rot*. Ledger delta: **0 DEBT / 0 FOUNDATIONAL**; **W1 discharged**.

## Step 0 — route-rot guard (no axioms)

Route-rot = recording a deferred discharge route whose own steps are unverified-plausible (the same
species of unchecked claim as the owed witness). Pass 2 recorded W1's route as "viable via AbelRuffini
+ `restrictNormalHom_surjective` + splitting-field embedding" without checking it. Step 0 (i) added
the **Route-first-step rule** to `AXIOM_LEDGER.md` (a recorded route must have its first step
probe-verified: names exist, signatures fit), and (ii) probe-verified W1's route — which then went
*all the way* to a full discharge (below), so the route annotation is now moot.

## Route probe results (Step 0): confirmed vs. plausible

All probe-verified to **exist with fitting signatures** (then assembled into a working proof):
- `AlgEquiv.restrictNormalHom_surjective` — and `Polynomial.Gal.restrict_surjective` (its packaging
  for `p.Gal`) **is** the push-up; the feared "splitting-field-into-`AlgebraicClosure ℚ` embedding"
  was **unnecessary**.
- `Polynomial.Gal.galActionHom_bijective_of_prime_degree'` (`Analysis/Complex/Polynomial/Basic.lean`):
  irreducible prime-degree ℚ-poly with `card(rootSet ℝ)+1 ≤ card(rootSet ℂ) ≤ card(rootSet ℝ)+3` has
  full symmetric Galois group. For `X³-2`: `card(rootSet ℂ)=3` (`card_rootSet_eq_natDegree`),
  `card(rootSet ℝ)≤1` (the cube map is injective on ℝ: `Odd.pow_injective`).
- `X_pow_sub_C_irreducible_of_prime` + `isInteger_of_is_root_of_monic` (rational root theorem): `X³-2`
  irreducible because `2` is not a cube in ℚ (`Anabelian.two_not_cube`).
- `CommGroup.isSolvable`, `Equiv.permCongrHom`, `MulEquiv.ofBijective` — and `Equiv.Perm (Fin 3)`
  non-commutative by `decide`.

**The one genuine obstacle** (not anticipated): a **ℚ-algebra diamond**. The synth trace showed
`Algebra ℚ (AlgebraicClosure ℚ)` resolving via `DivisionRing.toRatAlgebra` (every char-0 division ring
is a ℚ-algebra) rather than `AlgebraicClosure.instAlgebra`; the two don't match at instance-resolution
reducibility, so `Normal ℚ (AlgebraicClosure ℚ)` (needed by `restrict_surjective`) failed to
synthesize. **Fix:** `attribute [-instance] DivisionRing.toRatAlgebra in <theorem>` — then every
`Algebra ℚ (AlgebraicClosure ℚ)` uses the algebraic-closure structure (the same one in
`Field.absoluteGaloisGroup ℚ`), and the proof goes through. The ℂ-side (`Algebra ℚ ℂ`) is unaffected.
*(Recorded for future passes touching `AlgebraicClosure ℚ` / number fields — this diamond will recur.)*

**Pre-search expectation vs. reality (point iv):** I expected W1 **not** cleanly dischargeable this
pass (anticipating absent S₃-computation or heavy splitting-field embedding). **Wrong, pleasantly:**
Mathlib's `galActionHom_bijective_of_prime_degree'` + `Gal.restrict_surjective` made `(X³-2).Gal ≅ S₃`
and the push-up clean; the real cost was the ℚ-algebra diamond, not the anticipated plumbing. The
residue surjection (b) and `≅ Ẑ` (c) remain unattempted (still expected heavy).

## The lemma (Step 1) and self-audit (Step 2)

`Anabelian/RationalsNonAbelian.lean`, standard axioms only (in-file `#print axioms`):
- `two_not_cube : ∀ b : ℚ, b ^ 3 ≠ 2` (rational-root-theorem helper).
- `rationals_absoluteGaloisGroup_not_commutative : ¬ ∀ σ τ : Field.absoluteGaloisGroup ℚ, σ*τ = τ*σ`.

**Genuine content — a discharged debt of rigor, not a restatement.** Passes 1–2 *claimed* `[Finite F]`
load-bearing but only registered W1; this *proves* it, closing the first owed witness and completing
a discipline cycle (extend rule-2 in Pass 2 → honor it in Pass 3). Not a smoke test: the conclusion is
the negation of the Pass-1/2 conclusions, true precisely because ℚ is *not* finite.

**Recovers nothing from an abstract group.** The statement is a property of `Gal(ℚ̄/ℚ)` as it acts on
the *given* `AlgebraicClosure ℚ`; it does not reconstruct ℚ from an abstract topological group. No
reach toward R1–R3 (stated in the file docstring).

**Load-bearing hypotheses / owed witnesses.** This lemma *is* the W1 witness; it introduces no new
load-bearing claim and no new `structure`/`class`. No owed witness remains open.

**Proof shape.** `X³-2` irreducible & separable, degree 3 (prime); `card(rootSet ℂ)=3`,
`card(rootSet ℝ)≤1` ⟹ `galActionHom (X³-2) ℂ` bijective ⟹ `(X³-2).Gal ≃* Equiv.Perm (Fin 3)`;
assume `Gal(ℚ̄/ℚ)` commutative ⟹ (via `restrict_surjective`) `(X³-2).Gal` commutative ⟹ (via the iso)
`Equiv.Perm (Fin 3)` commutative, contradicting `decide`.

## Ledger delta & rule-2

- **0 DEBT / 0 FOUNDATIONAL**; Owed witnesses: **W1 discharged**, now **0 open**.
- Rule-2: no new `structure`/`class`; the lemma is itself the come-apart witness for `[Finite F]`.

## Pointer to Pass 4

With W1 closed, the remaining L1 sub-targets (still zero-`DEBT`): (b) the local residue surjection
`Gal(K̄/K) ↠ Gal(𝔽_q̄/𝔽_q)` tying `decompositionSubgroup`/`inertiaSubgroup` to Pass-2's procyclic
residue group; (c) strengthen Pass-2 procyclicity toward `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (needs a `Ẑ`). The
ℚ-algebra-diamond fix recorded above will likely be needed again for number-field work.

---

# Pass 4 — rung L1: residue-reduction faithfulness half (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The lemmas are properties of the Galois
action of a *given* valued field on its *given* residue field; nothing is recovered from an abstract
group. A proved fragment + an honest gap, not a stubbed whole. Ledger delta: **0 DEBT / 0
FOUNDATIONAL**, 0 owed witnesses.

## Step 0 — ℚ-algebra-diamond tracking (no axioms)

Added **D1** to `ROADMAP.md` as a *structural-hygiene debt* (distinct from `DEBT` axioms and Owed
witnesses): resolve the `Algebra ℚ (AlgebraicClosure ℚ)` diamond *once* (e.g.
`Subsingleton (Algebra ℚ (AlgebraicClosure ℚ))`) before sustained number-field work, rather than the
Pass-3 per-theorem band-aid; trigger = its second recurrence. **It did not recur this pass** — the
residue-reduction work is over an abstract valued field `K` (no concrete ℚ-algebra), so D1 stays at
"first appearance, not yet triggered."

## Deepened local-field / ramification inventory (real names)

- **`Mathlib/RingTheory/Valuation/RamificationGroup.lean`** — the *entire* ramification API — is
  **definitions only, zero theorems** (verified by reading the whole file): `ValuationSubring.decompositionSubgroup K A`
  (`:= MulAction.stabilizer (L ≃ₐ[K] L) A`), the `MulSemiringAction` of the decomposition group on
  `A` and on `IsLocalRing.ResidueField A`, the reduction hom
  `MulSemiringAction.toRingAut (decompositionSubgroup) (ResidueField A)`, and
  `ValuationSubring.inertiaSubgroup K A := MonoidHom.ker (that reduction)`. **PRESENT (as definitions).**
- Group-theory glue used: `MonoidHom.mem_ker`, `MonoidHom.normal_ker`, `QuotientGroup.kerLift`,
  `QuotientGroup.kerLift_injective`, `RingEquiv.ext_iff`. **PRESENT.**
- **ABSENT** (confirmed — no theorems in the file, none found elsewhere): surjectivity of the residue
  reduction; the maximal-unramified extension and `Gal(K^ur/K) ≅ Gal(𝔽_q̄/𝔽_q)`; identification of the
  reduction target with a residue Galois group; the unramified/tame/wild filtration.
- `IsNonarchimedeanLocalField` (Pass 0) present as a definition; not needed for the abstract fragment.

### Pre-search expectation vs. reality (point iii)

| I expected | Reality | Verdict |
|------------|---------|---------|
| whole surjection `Gal(K̄/K) ↠ Gal(𝔽_q̄/𝔽_q)` | absent (no max-unram theory) | ✓ |
| surjectivity of reduction | absent (needs Hensel/lifting) | ✓ |
| well-definedness (reduction is a hom) | present but a smoke-test (`MulSemiringAction.toRingAut`) | ✓ |
| inertia = kernel | **definitional** (`rfl`) | ✓ |
| faithful quotient embedding | **reachable** (`kerLift_injective`) — chosen | ✓ |

Net: matched expectation. The API is the patchiest yet (definitions only), so the reachable content
is exactly the *faithfulness half*; surjectivity is genuinely absent, not merely unproven-by-me.

## The lemma/fragment (Step 1) and self-audit (Step 2)

`Anabelian/ResidueReduction.lean`, standard axioms only (in-file `#print axioms`):
- `inertiaSubgroup_eq_reductionKer` — `inertiaSubgroup = ker (reduction)` (`rfl`; documents the def).
- `mem_inertiaSubgroup_iff` — `σ ∈ inertiaSubgroup ↔ ∀ x : ResidueField A, (reduction σ) x = x`
  (inertia = pointwise residue stabilizer).
- `residueReduction_quotient_injective` — `Injective (kerLift reduction)`, i.e.
  `decomposition ⧸ inertia ↪ RingAut (ResidueField A)` (the faithful embedding).

**Genuine but light, exactly which fragment.** Genuine L1 content in *new* (ramification) territory,
not a Pass-0/1/2/3 restatement. But **light**: the ramification API being definitions-only, each is a
short group-theory derivation. The fragment proved is the **faithfulness (injective) half** of the
residue reduction; the **surjectivity half** (onto the residue Galois group — the R1-relevant
structure) is **absent from Mathlib** and is logged as an L1 sub-target, *not* stubbed. (Honest: a
proved fragment + named gap, per the pass mandate.)

**Recovers nothing from an abstract group.** Maps between / properties of *given* Galois groups of
*given* fields. No reach toward R1–R3 (stated in the file docstring).

**Load-bearing hypotheses / owed witnesses.** None: the results hold for *any* valuation subring `A`
of any `L/K`. No new `structure`/`class`, so no rule-2 obligation.

**Diamond status.** Did not reappear (abstract setting). D1 untriggered.

## Ledger delta & rule-2

- **0 DEBT / 0 FOUNDATIONAL**; 0 owed witnesses added; **0 open**.
- Rule-2: no new `structure`/`class`; no load-bearing hypothesis to witness.

## Scope: honest read on L1 completeness, and pointer to Pass 5

The *easy/finite* L1 fruit is now harvested (finite-field commutativity/procyclicity P1–P2,
non-abelian witness P3, definitional ramification faithfulness P4). **What remains in L1 is not more
light lemmas** — residue *surjectivity*, the maximal-unramified extension, the tame/wild filtration,
and `≅ Ẑ` all need local-field *structure theory* absent from Mathlib. So L1 is **not** "done enough"
to leave for L2/L3 by harvesting more fragments. **Pass 5 should make a decision, per sub-target:**
(a) formalize the genuine local-field structure (likely several passes of real work), or (b)
consciously take a specific piece as a `FOUNDATIONAL` boundary (logged + classified) — rather than
hunt for another light fragment. This is the natural inflection point the pass mandate anticipated.

---

# Pass 5 — rung L1 inflection: the unramified quotient (first non-empty ledger) (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The residue surjection is a map between
the Galois groups of *given* fields (`K` and its residue field `𝓀[K]`) — nothing is recovered from
an abstract group. This is the **inflection pass**: the zero-entry streak ends, and that is the
honest sign the project reached its real work. Ledger delta: **`FOUNDATIONAL` +1, `DEBT` +0**.

## The decision (Step 1): (B), with reasoning

A **third light fragment was disallowed**, and would have looked like: proving another zero-debt
group-theory triviality about the Pass-4 maps (inertia normal, decomposition closed, …) — keeping the
clean-build streak alive without confronting the residue *surjectivity*, the structure load-bearing
for R1. That is the anabelian-scale `iutt`-photographs trap.

**Chose (B): import the residue surjection as a `FOUNDATIONAL` boundary, build on it.** Tractability
assessment that drove it: the maximal-unramified Galois edifice (`K^ur`, the unramified↔residue
correspondence, the surjection) is **entirely absent** from Mathlib; only ingredients are present.
The surjection's *content is* that correspondence, so option (A) has **no clean strictly-lower `DEBT`
to stub** — a `DEBT` axiom below the surjection is either already-present (Hensel) or *is* the
surjection (cardinal sin). (A) is a genuine multi-pass construction with nothing clean committable
this pass. So (B) — a classical theorem (Serre I–II / Neukirch II), consciously taken as an external
input strictly below R1 — is the honest call, and it buys real downstream content.

## Deepened maximal-unramified inventory (real names; verify, don't guess)

- **PRESENT (ingredients):** `HenselianLocalRing` (+ `Field.henselian`, `IsAdicComplete.henselianRing`)
  in `RingTheory/Henselian.lean`; `IsLocalRing.ResidueField.map` (+ `map_id`/`map_comp`/`mapEquiv`)
  — residue-field functoriality, in `RingTheory/LocalRing/ResidueField/Basic.lean`; `Algebra.IsUnramified`
  / `Algebra.IsUnramifiedAt` (étale-style), with `[IsUnramifiedAt R q] → IsSeparable/Module.Finite`
  on residue fields, in `RingTheory/Unramified/`. Residue field of a local field: `𝓀[K] :=`
  `IsLocalRing.ResidueField ↥𝒪[K]` (scoped notation, `Valued/ValuativeRel.lean`), with **`Finite 𝓀[K]`**
  and `Field 𝓀[K]` instances for `IsNonarchimedeanLocalField K`.
- **ABSENT (the Galois edifice):** the maximal unramified extension `K^ur` as an object; the iso
  `Gal(K^ur/K) ≅ Gal(𝓀̄/𝓀)`; the residue reduction `Gal(K̄/K) → Gal(𝓀̄/𝓀)` and its surjectivity; a
  Frobenius lift. Zero hits across Mathlib for all of these. (`RamificationGroup.lean` remains, as
  Pass 4 found, definitions only.)
- Glue used: `QuotientGroup.quotientKerEquivOfSurjective`, `Fintype.ofFinite`, and Pass 2's
  `Anabelian.frobenius_topologicalClosure_eq_top` (procyclicity of finite-field absolute Galois groups).

### Pre-search expectation vs. reality (points iii/iv)

| I expected | Reality | Verdict |
|------------|---------|---------|
| maximal-unramified Galois edifice absent | absent (zero hits) | ✓ |
| (A) has no clean strictly-lower `DEBT` to stub | confirmed (surjection's content *is* the correspondence) | ✓ |
| (B) the honest call | chosen | ✓ |
| residue surjection becomes a *proved* theorem this pass | **no** — it is the *posited* `FOUNDATIONAL` axiom; proving it is several passes out (needs the whole construction) | ✓ |

## What was proved vs. what was imported (Step 2)

`Anabelian/UnramifiedQuotient.lean`:
- **Imported (`FOUNDATIONAL`):** `residueReduction_surjective` — `∃ φ : G_K →* G_{𝓀[K]}, Surjective φ`
  for a nonarchimedean local field. Classified in `AXIOM_LEDGER.md`: below R1, permitted `FOUNDATIONAL`
  for R1, Serre/Neukirch. Posits *existence* of the surjection (weaker than the full classical map).
- **Proved on it (`theorem`, rests on the boundary):** `unramifiedQuotient_iso` —
  `G_K ⧸ N ≃* Gal(𝓀̄/𝓀)` (first iso theorem); `unramifiedQuotient_procyclic` — that quotient is
  procyclic (combine boundary + Pass 2). And `residue_procyclic` — the residue Galois group is
  procyclic (Pass 2, standard axioms only).
- **Genuine, not a fragment:** the pass changed the ledger from empty and confronted the load-bearing
  structure theory (by importing it as a classified boundary) and built the unramified-quotient
  structure on it. In-file `#print axioms` confirm exactly which results rest on the boundary.
- **Recovers nothing from an abstract group** (stated in the file docstring); no reach toward R1–R3.
- **No owed witness, no new `structure`/`class`.** **D1 did not recur** (local field + *finite*
  residue field; no `Algebra ℚ (AlgebraicClosure ℚ)`).

## Ledger delta

- **`FOUNDATIONAL` +1** (`Anabelian.residueReduction_surjective`), **`DEBT` +0**. First non-empty
  ledger. Owed witnesses: 0 open.

## Scope: toward R1, what remains on L1, pointer to Pass 6

Advanced toward R1: the unramified quotient `G_K ⧸ N ≅ Gal(𝓀̄/𝓀)` is procyclic — exactly the
residue-Galois structure R1 reconstruction exploits, now available (modulo one explicit boundary).
Remaining L1, all genuine structure theory (not light fragments): (i) **discharge**
`residueReduction_surjective` by formalizing the maximal-unramified construction (reclassify
`FOUNDATIONAL → DEBT`, then prove — multi-pass); (ii) **tie `N` to Pass 4's `inertiaSubgroup`** (needs
the valuation on `K̄`, absent); (iii) tame/wild filtration; (iv) `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`. **Pass 6**
should take one of these with the same (A)/(B) discipline — e.g. begin option (A) on
`residueReduction_surjective` now that its boundary role is explicit, scaffolding the construction
over several passes.

---

# Pass 6 — rung L1 discipline-inversion: `Ẑ ↠ Gal(𝔽_q̄/𝔽_q)`, no new boundary (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The result is the structure of a *given*
finite field's absolute Galois group; nothing is recovered from an abstract group. The pass's defining
constraint: **no second `FOUNDATIONAL`** — the `FOUNDATIONAL`-stacking trap (a tower of accepted
boundaries, a slow IUT-Stage-1 replay). Ledger delta: **0 / 0** (no `DEBT`, no new `FOUNDATIONAL`).

## The decision (A vs Z) and the tractability call

**Chose (Z): the `≅ Ẑ` residue-side identification, axiom-free, no boundary.** Reasoning:

- **(A) (discharge `residueReduction_surjective`) is blocked this pass.** The surjection's content *is*
  the unramified↔residue correspondence, and its heart is the **lifting** step (every residue
  automorphism lifts). A `DEBT` axiom asserting lifting *is* the surjection in disguise (cardinal sin).
  The legitimate strictly-lower infrastructure (`K^ur` existence, residue `= 𝓀̄`, reduction
  well-definedness) needs the **valuation on `K̄`**, which is **absent** (only `SpectralNorm` exists, in
  Analysis, not assembled into `𝒪[K̄]`/residue/reduction). So (A) has no clean strictly-lower `DEBT`
  and its infrastructure is not axiom-free this pass → blocked. (Per the mandate, when lifting is
  irreducibly absent, do not fake a cardinal-sin `DEBT`.)
- **(Z) is genuinely achievable axiom-free**, using Mathlib's profinite-completion functor + Pass 2.

## Deepened inventory (real names; verify, don't guess)

- **(A) side — confirmed ABSENT:** maximal unramified extension / `K^ur` / residue Galois iso /
  Frobenius lift (zero hits). `RingTheory/Henselian.lean` has `HenselianLocalRing` + the
  `HenselianLocalRing.TFAE` and `IsAdicComplete.henselianRing` (so Hensel is *available* as a
  characterization), but the unramified-correspondence assembly is absent. Valuation on `K̄`: only
  `Analysis/Normed/Unbundled/SpectralNorm.lean` (`spectralNorm`, extends the norm to algebraic exts,
  automorphisms are isometries) — not assembled into a `ValuativeRel`/residue-field/reduction-map.
- **(Z) side — PRESENT:** `ProfiniteGrp.ProfiniteCompletion.{completion, etaFn, eta, denseRange, lift,
  lift_eta, homEquiv, adjunction}` and the functor `ProfiniteGrp.profiniteCompletion`
  (`Topology/Algebra/Category/ProfiniteGrp/Completion.lean`); `InfiniteGalois.profiniteGalGrp =`
  `ProfiniteGrp.of Gal(K/k)`; `zpowersHom (α) : α ≃ (Multiplicative ℤ →* α)`; `GrpCat.ofHom`;
  `Subgroup.topologicalClosure_coe`, `dense_iff_closure_eq`, `isCompact_range`. **ABSENT:** a named
  `Ẑ`/`ZHat` (constructed here as `completion (GrpCat.of (Multiplicative ℤ))`); the iso `≅ Ẑ` itself.

### Pre-search expectation vs. reality (points iii/iv)

| I expected | Reality | Verdict |
|------------|---------|---------|
| (A) lifting irreducibly absent (not reducible to Hensel API) | confirmed (no `K^ur`; valuation on `K̄` absent) | ✓ |
| (Z) profinite-completion functor present, no named `Ẑ` | confirmed | ✓ |
| full `≅ Ẑ` not finished this pass; surjective half reachable | confirmed — surjective half proved, injective half remains | ✓ |
| ledger stays `1 FOUNDATIONAL / 0 DEBT` | confirmed | ✓ |

## What was proved (Step 2 self-audit)

`Anabelian/FiniteFieldZHat.lean`, standard axioms only (in-file `#print axioms`):
- `ZHat := completion (GrpCat.of (Multiplicative ℤ))` (Ẑ).
- `zhatToGalois` — the canonical `Ẑ → Gal(K̄/K)` (finite `K`), via the profinite-completion universal
  property `lift` applied to `n ↦ Frobⁿ`. `zhatToGalois_etaFn` characterizes it on the image of `ℤ`.
- `zhatToGalois_surjective` — **surjective** (range closed [compact image] ⊇ dense Frobenius powers
  [Pass 2]). The **surjective half** of `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`.

**Genuine, not a fragment, not avoidance:** it is the actual map of the classical iso, built via the
profinite-completion universal property — genuinely beyond Pass 2's procyclic generation. It is **not**
a Pass-2 restatement (which was `topologicalClosure (zpowers φ) = ⊤`); it constructs the map from the
completion object `Ẑ` and proves surjectivity of *that*. The proof took real categorical work (the
GrpCat/ProfiniteGrp coercions, the pointwise `lift_eta` via `DFunLike.congr_fun`), the kind the
easy-fruit era did not require.

**Recovers nothing from an abstract group** (file docstring). **No load-bearing hypothesis / owed
witness** (holds for any finite `K`). No new `structure`/`class`. **D1 did not recur** (finite fields).

## Ledger delta

- **0 `DEBT` / 0 new `FOUNDATIONAL`.** Active axioms unchanged: 1 `FOUNDATIONAL`
  (`residueReduction_surjective`, Pass 5, unused here), 0 `DEBT`. 0 open owed witnesses.

## Scope: toward R1, what remains on L1, pointer to Pass 7

Advanced toward R1: `Gal(𝔽_q̄/𝔽_q)` is now known to be a *continuous quotient of `Ẑ`* (surjective half),
the residue-side structure R1 exploits. Remaining L1 (both genuinely multi-pass, no light fragments):
(i) the **injective half** of `≅ Ẑ` — the canonical map is injective, equivalently the finite quotients
`Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n` match `Ẑ`'s inverse system; (ii) **discharge** `residueReduction_surjective`
by building the maximal-unramified construction (`FOUNDATIONAL → DEBT`, then prove — needs the
valuation on `K̄` first). **Pass 7**: continue *without stacking boundaries* — begin (i) (finite
quotients `≅ ℤ/n`) or begin (ii)'s construction, both axiom-free-or-committed-`DEBT`, never a second
posit.

---

# Pass 7 — rung L1: the finite levels of `≅ Ẑ` (`Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n`) (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The result is the structure of the Galois
group of *given* finite fields; nothing recovered from an abstract group. The pass's organizing risk:
**half-accumulation** — six passes hold several *halves* but no L1 whole of depth, the project-level
relocate-and-never-close pattern. Preferred move: **close a whole**. Ledger delta: **0 / 0**.

## The decision (i vs ii) and the tractability call

**Chose route (i)'s fallback.** (i) = CLOSE `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` (finish Pass 6's surjective half with
injectivity). Inventory found **(i)-full not closable axiom-free this pass**: injectivity of
`zhatToGalois` needs `Ẑ`'s presentation as `lim ℤ/n`, but Mathlib's `Ẑ = ProfiniteGrp.completion`
`(Multiplicative ℤ)` is indexed by `FiniteIndexNormalSubgroup`, *not* `ℤ/n`, and no off-the-shelf
cofinal matching exists — genuinely multi-pass. Per the route-(i) fallback ("real axiom-free progress
on the injective half"), proved its **per-level ingredient** `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n`, a *complete*
theorem, **without positing the iso** (closing-by-positing = the stacking trap). Did not switch to
(ii) (begin valuation-on-`K̄`) — it adds `DEBT` and opens new multi-pass work; the (i)-fallback keeps
the ledger clean and is the more on-target progress toward `≅ Ẑ`.

## Deepened inventory (real names; verify, don't guess)

- **PRESENT (used):** `IsGalois.card_aut_eq_finrank (F E) [FiniteDimensional] [IsGalois] :`
  `Nat.card Gal(E/F) = Module.finrank F E`; the finite-field `IsCyclic Gal(L/K)` instance (`[Finite L]`,
  Pass 1); `zmodCyclicMulEquiv (h : IsCyclic G) : Multiplicative (ZMod (Nat.card G)) ≃* G`. **`IsGalois K L`
  is automatic for finite fields** — but its instance lives in `Mathlib.FieldTheory.Finite.GaloisField`,
  which had to be imported (the Pass-3 specific-imports lesson recurred).
- **PRESENT (iso-packaging, for the eventual close):** `Continuous.homeoOfEquivCompactToT2`
  (compact→T2 continuous bijection ⟹ homeomorphism), `MulEquiv.ofBijective`, `ContinuousMulEquiv`,
  `etaFn_injective_iff_residuallyFinite`. So once injectivity lands, the iso is clean to package.
- **ABSENT (the genuine multi-pass remainder):** `Ẑ` as `lim ℤ/n` (no named `Ẑ`/`ZHat`; the only
  presentation is `completion (Multiplicative ℤ)` over `FiniteIndexNormalSubgroup`); the cofinal
  matching of that with `Gal`'s `FiniteGaloisIntermediateField` inverse system; hence injectivity of
  `zhatToGalois`. (For route (ii): `SpectralNorm` present, but the valuation-on-`K̄` assembly absent.)

### Pre-search expectation vs. reality (points iii/iv)

| I expected | Reality | Verdict |
|------------|---------|---------|
| "continuous bijection compact→T2 ⟹ homeo" present | present (`Continuous.homeoOfEquivCompactToT2`) | ✓ |
| injectivity of `zhatToGalois` heavy/absent | confirmed — needs absent `Ẑ = lim ℤ/n` + cofinal matching | ✓ |
| `≅ Ẑ` may not fully close; finite-level iso lands | confirmed — only the per-level ingredient closed | ✓ |
| ledger stays `1 FOUNDATIONAL / 0 DEBT` | confirmed | ✓ |

## What was proved (Step 2 self-audit)

`Anabelian/FiniteGaloisCyclic.lean`, standard axioms only (in-file `#print axioms`):
- `galoisFiniteField_mulEquivZMod` — `Gal(L/K) ≃* Multiplicative (ZMod (Module.finrank K L))` for a
  finite extension `L/K` of finite fields. The per-level datum `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n` of `≅ Ẑ`'s
  injective half.

**Did `≅ Ẑ` fully close? NO** — only the injective-half *per-level ingredient* landed; the full iso
remains open (gap: `Ẑ = lim ℤ/n` + cofinal matching, absent). **The iso was NOT posited as
`FOUNDATIONAL`** (explicitly: closing-by-positing is the stacking trap). **Honest on depth:** this is a
*complete* theorem but **modest** (short proof assembling existing API), matching the Pass-1/4 "genuine
but light" bar — it is a closed whole at the finite level, not another half, but it is **not** the deep
L1 whole the pass aimed to close.

**Recovers nothing from an abstract group** (file docstring). No load-bearing hypothesis / owed
witness; no new `structure`/`class`. **D1 did not recur** (finite fields).

## Ledger delta

- **0 `DEBT` / 0 new `FOUNDATIONAL`.** Active axioms unchanged: 1 `FOUNDATIONAL`
  (`residueReduction_surjective`, Pass 5, unused here), 0 `DEBT`. 0 open owed witnesses.

## Scope: toward R1, what remains on L1, pointer to Pass 8

Toward R1: `≅ Ẑ` now has both its surjective half (Pass 6) and the injective half's per-level data
(Pass 7) — the residue-side structure R1 exploits, *nearly* whole. **Honest caveat: no deep L1 whole is
closed yet.** Pass 8 should aim to **close one whole** (not accumulate another half): either (a) build
`Ẑ = lim ℤ/n` and the cofinal inverse-system matching to **close `≅ Ẑ`** (the satisfying whole, via the
iso-packaging API confirmed present), or (b) begin route (ii) — assemble the valuation on `K̄` (from
`SpectralNorm`) toward discharging `residueReduction_surjective` (`FOUNDATIONAL → DEBT`). Both
multi-pass; neither a fresh boundary.

---

# Pass 8 — rung L1: the `Ẑ`-side inverse-system presentation of `≅ Ẑ` (2026-05-30)

## Honest scope (governs this pass)

Stays at **rung L1**, proves **no reconstruction (R1–R3)**. The result is structure of the completion
object `Ẑ` (and `Multiplicative ℤ`); nothing recovered from an abstract group. The pass's designated
job: **close `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`** as a complete axiom-free theorem — break the half-accumulation, not
add a fourth half/pivot/posit. Ledger delta: **0 / 0**.

## The decision (close vs. the permitted not-closed outcome) and why

**Outcome: not closed this pass — the permitted fallback, with both required components delivered.**
The iso = bijectivity of Pass 6's `zhatToGalois`. Surjective is in hand; **injectivity** needs the
commuting square `Ẑ → ℤ/n ≅ Gal(𝔽_{q^n}/𝔽_q) ← Gal(K̄/K)` at every level. Inventory found the **Galois-
side level projection** `Gal(K̄/K) → Gal(𝔽_{q^n}/𝔽_q)` blocked: Mathlib has no `𝔽_{q^n}` as a
`FiniteGaloisIntermediateField` of `AlgebraicClosure K`. So closure is genuinely multi-pass. Per the
mandate, I did NOT posit anything; instead delivered (1) the named missing-API + a **numbered Pass 9–11
sub-plan** (`ROADMAP.md`), and (2) **real axiom-free progress on the actual injective-half machinery** —
the `Ẑ`-side inverse-system presentation (procyclicity + cyclic finite quotients). I did NOT pivot to
the residue-surjection boundary discharge (it opens long `DEBT` and closes nothing soon).

## Deepened inventory (real names; verify, don't guess) — with Pass-7 corrections

- **CORRECTION to Pass 7 ("`Ẑ = lim ℤ/n` presentation + cofinal machinery absent off the shelf").**
  The general profinite-as-inverse-limit machinery is **PRESENT**:
  `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits` — `toLimit (P) : P ⟶ limit (diagram P)`,
  `toLimit_injective`/`toLimit_surjective` (separation via `exist_openNormalSubgroup_sub_open_nhds_of_one`
  in `ClopenNhdofOne.lean`), `proj`, `isLimitCone`, `isoLimittoFiniteQuotientFunctor`,
  `continuousMulEquivLimittoFiniteQuotientFunctor : P ≃ₜ* limit (diagram P)`. And `completion G =`
  `limit (ProfiniteCompletion.diagram G)` over `FiniteIndexNormalSubgroup G` — `Ẑ` **is** a genuine
  categorical inverse limit already.
- **CORRECTION re `etaFn_injective_iff_residuallyFinite`** (Pass 7 listed it as iso-packaging help): it
  states `Injective (etaFn G) ↔ Group.ResiduallyFinite G` — about the **unit** `η : G → completion G`,
  **not** about `zhatToGalois`. `ℤ` residually finite ⟹ `η` injective, but that is a fact about `Ẑ`
  containing a copy of `ℤ`, not injectivity of `zhatToGalois`. So this hint does **not** close the
  injective half; recorded so a future pass doesn't chase it.
- **PRESENT (used Pass 8):** `ProfiniteCompletion.{etaFn, eta, denseRange}`; `Multiplicative.ofAdd`,
  `ofAdd_zsmul`; `map_zpow`; `isCyclic_of_surjective`; `IsCyclic (Multiplicative ℤ)`;
  `QuotientGroup.mk'`, `mk'_surjective`, `continuous_quotient_mk'`; `Subgroup.topologicalClosure_coe`,
  `dense_iff_closure_eq`, `isClosed_discrete`, `DenseRange.{comp, closure_range, mono}`;
  `OpenNormalSubgroup` with `Finite`/`DiscreteTopology` instances on `Ẑ ⧸ U`.
- **PRESENT (for the close, Pass 9–11):** `AlgEquiv.restrictNormalHom` + `restrictNormalHom_surjective`
  (`FieldTheory/Normal/`); `FiniteGaloisIntermediateField.{proj, finGaloisGroupFunctor}`,
  `mulEquivToLimit`, `asProfiniteGaloisGroupFunctor` (`FieldTheory/Galois/Profinite.lean`);
  `Continuous.homeoOfEquivCompactToT2`, `MulEquiv.ofBijective`, `ContinuousMulEquiv.toProfiniteGrpIso`.
- **ABSENT (the genuine blocker):** `𝔽_{q^n}` as a `FiniteGaloisIntermediateField K (AlgebraicClosure K)`
  for finite `K` (`FieldTheory/Finite/GaloisField.lean` has only standalone `GaloisField p n`, not
  embedded in `K̄` with a restriction map). Hence the Galois-side level projection
  `Gal(K̄/K) → Gal(𝔽_{q^n}/K)` is absent — the Pass-9 construction target.

### Pre-search expectation vs. reality (points iii/iv)

| I expected (pre-search) | Reality | Verdict |
|-------------------------|---------|---------|
| `≅ Ẑ` close is a stretch; likely needs a sub-plan | confirmed — not closable this pass | ✓ |
| Pass 7's "`lim` machinery absent" might be stale | **corrected** — `ProfiniteGrp.Limits` is PRESENT | ✗→fixed |
| `etaFn_injective_iff_residuallyFinite` might give injectivity | **corrected** — it's about the unit `η`, not `zhatToGalois` | ✗→fixed |
| the blocker would be `Ẑ`-side | **corrected** — blocker is **Galois-side** (`𝔽_{q^n}` absent) | ✗→fixed |
| ledger stays `1 FOUNDATIONAL / 0 DEBT` | confirmed | ✓ |

## What was proved (Step 2 self-audit)

`Anabelian/ZHatProcyclic.lean`, standard axioms only (in-file `#print axioms`):
- `zhat_topologicalClosure_eq_top` — **`Ẑ` is procyclic**: `topologicalClosure (zpowers zhatGen) = ⊤`
  for `zhatGen = η(ofAdd 1)`. (`η`'s image ⊆ `zpowers zhatGen`, dense in compact `Ẑ`.) The `Ẑ`-side
  analogue of Pass 2's `frobenius_topologicalClosure_eq_top`.
- `zhat_quotient_isCyclic` — **every finite quotient `Ẑ ⧸ U` is cyclic** (image of the cyclic
  `Multiplicative ℤ` under `mk' ∘ η`, dense range into discrete ⟹ surjective ⟹ cyclic). With
  `toLimit_injective Ẑ` (point-separating projections), `Ẑ` = inverse limit of finite **cyclic** groups.

**Did `≅ Ẑ` close? NO.** Only the `Ẑ`-side inverse-system presentation landed; the iso is **open** and
was **NOT posited** (a second `FOUNDATIONAL` is barred; closing-by-positing is the stacking trap).
**On-path, not adjacent:** these are the `Ẑ`-side of the injectivity square (matching `Gal`'s cyclic
`ℤ/n` system, Pass 7), about `Ẑ` itself — not a finite-field corollary. **Genuine but partial.**

**Recovers nothing from an abstract group** (file docstring). No load-bearing hypothesis / owed witness
(both hold for `Ẑ` unconditionally). No new `structure`/`class`. **D1 did not recur** (`Ẑ` /
`Multiplicative ℤ`, no `Algebra ℚ (AlgebraicClosure ℚ)`).

## Mathlib API that did the real work

`ProfiniteCompletion.denseRange` + `eta` (the unit, as a `MonoidHom` via `.hom`); `ofAdd_zsmul` +
`map_zpow` (the `ofAdd 1` generates `Multiplicative ℤ` step — note the `(1 : ℤ)`-vs-group-`One` literal
ambiguity had to be pinned explicitly); `isCyclic_of_surjective`; `isClosed_discrete` +
`DenseRange.closure_range` (dense-into-discrete ⟹ surjective); `Subgroup.topologicalClosure_coe` +
`dense_iff_closure_eq` (the procyclic-closure idiom).

## Ledger delta

- **0 `DEBT` / 0 new `FOUNDATIONAL`.** Active axioms unchanged: 1 `FOUNDATIONAL`
  (`residueReduction_surjective`, Pass 5, unused here), 0 `DEBT`. 0 open owed witnesses.

## Scope: what remains on L1, honest pointer to Pass 9

`≅ Ẑ` now has all three component halves (surjective P6, per-level P7, `Ẑ`-side inverse-system P8) but
the **iso itself is still open** — the half-accumulation pattern is **not yet broken**; this pass
converted the vague remainder into the concrete **Pass 9–11 sub-plan** (`ROADMAP.md`): **Pass 9** build
`𝔽_{q^n} ⊆ K̄` as a `FiniteGaloisIntermediateField` + the level projection `r_n`; **Pass 10** the
commuting square (on the dense `η`-image, via Pass 8 procyclicity + Pass 6 `zhatToGalois_etaFn`) ⟹
`ker zhatToGalois = ⊥`; **Pass 11** package the `ContinuousMulEquiv` — **closing `≅ Ẑ`**, the first L1
whole of depth. All axiom-free, no fresh boundary. Honest next step: **execute Pass 9**.

---

# Pass 9 — rung L1: the Galois-side level subfields `𝔽_{q^n}` of `≅ Ẑ` (2026-05-30)

## Honest scope + grading (governs this pass)

Rung **L1**, **no reconstruction (R1–R3)**. Executed **Pass 9** of the resolved `≅ Ẑ` sub-plan: built
the one absent Galois-side ingredient. **Graded as infrastructure, not a closed whole** — a
`FiniteGaloisIntermediateField` term + a `restrictNormalHom` + the Frobenius-alignment equation are the
*means* to Pass 10's injectivity, not the iso. `≅ Ẑ` is **NOT** closed and **NOT** posited. The
half-accumulation pressure is satisfied only by the *eventual* `≅ Ẑ`. Ledger delta: **0 / 0**.

## The decision: execute the sub-plan rung; no pivot, no posit, no padding

Pass 8 had reduced `≅ Ẑ` to a single named blocker. This pass executes that rung. A pivot (to the
`K̄`-valuation/residue boundary), a posit (of `𝔽_{q^n}` or `r_n` as `FOUNDATIONAL` — barred), or
padding with adjacent finite-field lemmas would all be the disallowed money-pit move. Everything built
is a Pass-9 component or directly on the closure path. Closure did **not** fall out — injectivity is
the separate Pass-10 cofinality/diagram chase (see setup) — so this is graded infrastructure.

## Construction route + deepened inventory (real names; verify, don't guess)

**Route chosen for `𝔽_{q^n}`: `fixedField (zpowers (Frob^n))`** (not `adjoin (rootSet)`), because the
membership `x ∈ levelField K n ↔ x^(q^n) = x` is then clean, and the carrier coincides with the
rootSet of `X^(q^n)−X` for the degree count.

- **PRESENT (used):** `IntermediateField.fixedField` + `mem_fixedField_iff`;
  `FiniteField.frobeniusAlgEquivOfAlgebraic` + `coe_frobeniusAlgEquivOfAlgebraic_iterate` +
  `AlgEquiv.coe_pow` (giving `(Frob^n) x = x^(q^n)`); `FiniteField.X_pow_card_pow_sub_X_natDegree_eq` /
  `_ne_zero`; `card_rootSet_eq_natDegree` (`Mathlib.FieldTheory.Separable`) + `IsAlgClosed.splits` +
  the inline separability of `X^(q^n)−X` (derivative `= −1`); `Module.card_eq_pow_finrank` +
  `Nat.pow_right_injective` (degree from card); `IsGalois K (AlgebraicClosure K)` instance;
  `FiniteGaloisIntermediateField` (`Mathlib.FieldTheory.Galois.GaloisClosure`);
  `AlgEquiv.restrictNormalHom` + `restrictNormalHom_apply` + `restrictNormalHom_surjective`
  (`Mathlib.FieldTheory.Normal`); `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic`.
- **The `IsGalois K L` instance for finite `L` lives in `Mathlib.FieldTheory.Finite.GaloisField`** —
  had to be imported (the Pass-3/7 specific-imports lesson recurred, exactly as the instruction warned).
- **ABSENT (so built from scratch, confirming Pass 8):** `𝔽_{q^n}` as a `FiniteGaloisIntermediateField`
  of `AlgebraicClosure K`; no fixed-points-of-Frobenius subfield API; no "irreducible of degree `n`
  over a finite field" existence lemma. The degree count is bespoke (carrier = rootSet, card `q^n`).

### Pre-search expectation vs. reality (points ii–iv)

| I expected | Reality | Verdict |
|------------|---------|---------|
| `fixedField (Frob^n)` clean for membership | yes — membership iff `x^(q^n)=x` is short | ✓ |
| degree `n` would be the linchpin/hard part | yes — bespoke card-of-rootSet argument, several steps | ✓ |
| Frobenius alignment (the trap) tractable | **easier than feared** — `restrictNormalHom_apply` + both maps `·^q` ⟹ `simp only` closes it | ✓ (better) |
| closure would NOT fall out (injectivity separate) | confirmed — this is the infrastructure rung | ✓ |
| ledger stays `1 FOUNDATIONAL / 0 DEBT` | confirmed | ✓ |

## The Frobenius-alignment check (the trap, explicitly confirmed)

The level iso is pinned to **Frobenius**, not an arbitrary generator: `levelRestrict_frobenius` proves
`r_n (Frob) = frobeniusAlgEquivOfAlgebraic K (levelField K n)` (both are `x ↦ x^q`; via
`restrictNormalHom_apply` + `coe_frobeniusAlgEquivOfAlgebraic` + `IntermediateField.coe_pow`), and
`orderOf_levelRestrict_frobenius` proves `orderOf (r_n Frob) = n` (= `finrank`, via
`orderOf_frobeniusAlgEquivOfAlgebraic`). Since `Frob = zhatToGalois (η (ofAdd 1))` (Pass 6), the
generator Pass 10 needs — `r_n (zhatToGalois (η (ofAdd 1)))` = the Frobenius of `𝔽_{q^n}`, generating
`Gal(𝔽_{q^n}/K)` — is exactly what landed. **No unaligned-iso landmine for Pass 10.** (Note: Pass 7's
`galoisFiniteField_mulEquivZMod` via `zmodCyclicMulEquiv` was *deliberately not used* here, since it
picks an arbitrary generator; Pass 10 should use this Frobenius-aligned generator instead.)

## What was proved (Step 2 self-audit)

`Anabelian/FiniteFieldLevel.lean`, standard axioms only (in-file `#print axioms`):
`levelField`, `mem_levelField`, `separable_X_pow_card_pow_sub_X`, `levelField_coe_eq_rootSet`,
`levelField_finite` (instance, `[NeZero n]`), `levelField_finrank` (= `n`), `levelFGIF`,
`levelRestrict`, `levelRestrict_surjective`, `levelRestrict_frobenius`,
`orderOf_levelRestrict_frobenius`.

**Did `≅ Ẑ` close? NO** — infrastructure rung; injectivity is Pass 10. **Nothing posited.** **Recovers
nothing from an abstract group** (structure of *given* finite fields' subextensions). Load-bearing
hypothesis `NeZero n` is genuine (`n = 0` ⟹ level field = all of `K̄`, infinite) but is not a rule-2
come-apart claim (no `structure`/`class`); no owed witness. **D1 did not recur** (no
`Algebra ℚ (AlgebraicClosure ℚ)`).

## Ledger delta

- **0 `DEBT` / 0 new `FOUNDATIONAL`.** Active axioms unchanged: 1 `FOUNDATIONAL`
  (`residueReduction_surjective`, Pass 5, unused here), 0 `DEBT`. 0 open owed witnesses.

## Scope: progress toward `≅ Ẑ`, remaining sub-plan, pointer to Pass 10

`≅ Ẑ` now has all four ingredients (surjective P6, per-level P7, `Ẑ`-side inverse-system P8,
Galois-side level subfields P9). **Remaining:** Pass 10 — injectivity of `zhatToGalois`. Precise setup:
with `χ_n := levelRestrict K n ∘ zhatToGalois : Ẑ → Gal(𝔽_{q^n}/K)`, `χ_n` is surjective and
`χ_n (η (ofAdd 1)) = r_n (Frob)` generates (order `n`); show `⋂_n ker χ_n = ⊥` ⟹ `ker zhatToGalois = ⊥`.
The argument needs new group-theory on `Ẑ`: **"procyclic ⟹ unique subgroup of each finite index" +
cofinality of those subgroups** (on Pass 8's `zhat_quotient_isCyclic` + `toLimit_injective` separation).
Then Pass 11 packages the `ContinuousMulEquiv` (`homeoOfEquivCompactToT2` + `MulEquiv.ofBijective`,
both PRESENT) — closing `≅ Ẑ`, the first L1 whole of depth. Honest next step: **execute Pass 10**
(likely substantial — the cofinality/diagram chase may itself fill a pass).

---

# Pass 10 — rung L1: **`Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` CLOSED** — first L1 whole of depth (2026-05-30)

## Honest scope + grading

Rung **L1**, **no reconstruction (R1–R3)**. This pass **closes** `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` as a complete
axiom-free `ContinuousMulEquiv` — the project's **first closed L1 whole of real depth**, the capstone
of the Pass 6–10 chain. Graded as the **genuine whole** it is (not a half, not infrastructure):
nothing posited anywhere in the chain; the iso is earned. Ledger delta: **0 / 0**.

## The decision: prove injectivity, close the iso; no posit/pivot/pad

The setup was fully resolved by Pass 9. This pass proved the one substantive remaining rung
(injectivity) and the packaging fell out the same pass, so the iso closed. A posit (of injectivity /
the iso), a pivot (to the residue boundary), or padding would each have been the disallowed outcome.
Every lemma is on the injectivity/closure path.

## The injectivity argument (and the crux that dissolved)

`ker zhatToGalois = ⊥` via:
- `χ_m := r_m ∘ zhatToGalois` (`levelComp`); `χ_m zhatGen = r_m (Frob)` of **order `m`** (Pass 9
  `orderOf_levelRestrict_frobenius` + Pass 6 `zhatToGalois_etaFn`, the latter giving
  `zhatToGalois zhatGen = Frob`).
- **`ker_levelComp_le` (the cofinality core):** for closed `S ∋ zhatGen^m`, `ker χ_m ≤ S`. `ker χ_m`
  is **open** (`χ_m` continuous to the discrete `Gal(𝔽_{q^m}/K)`), the dense `⟨zhatGen⟩` (Pass 8)
  meets it in exactly `⟨zhatGen^m⟩` (`χ_m (zhatGen^k) = 1 ↔ m ∣ k`), so by `IsOpen.inter_closure`
  `ker χ_m = closure⟨zhatGen^m⟩ ⊆ S`.
- Then: `zhatToGalois x = 1`, `x ≠ 1` ⟹ separation gives open normal `H ∌ x`; `m := |Ẑ ⧸ H|`;
  Lagrange (`pow_card_eq_one'`) puts `zhatGen^m ∈ H`; so `x ∈ ker χ_m ≤ H` — contradiction.

**The Pass-9-flagged "procyclic ⟹ unique open subgroup of each finite index" lemma was NOT needed.**
The realization `ker χ_m = closure⟨zhatGen^m⟩` (an *equation*, from openness + density) replaced the
uniqueness/cofinality lemma entirely — a cleaner route than the one set up. This is the inventory
correction this pass: the crux dissolved into `IsOpen.inter_closure` + Pass 8 density, no new
group-theory.

## Deepened inventory (real names; verify, don't guess)

- **PRESENT (the decisive ones):** `krullTopology_discreteTopology_of_finiteDimensional`
  (`DiscreteTopology Gal(𝔽_{q^m}/K)`, makes `ker χ_m` open — the linchpin);
  `InfiniteGalois.restrictNormalHom_continuous` (`r_m` continuous);
  `exist_openNormalSubgroup_sub_open_nhds_of_one` (separation; the engine of Pass 8
  `toLimit_injective`); `IsOpen.inter_closure` (`s ∩ closure t ⊆ closure (s ∩ t)`);
  `orderOf_dvd_iff_zpow_eq_one`, `pow_card_eq_one'`, `QuotientGroup.eq_one_iff`,
  `injective_iff_map_eq_one`; `Continuous.homeoOfEquivCompactToT2`, `Equiv.ofBijective`,
  `ContinuousMulEquiv` (the packaging, as Pass 8 inventory predicted).
- **My-side reused:** `zhatToGalois`/`_surjective`/`_etaFn` (P6), `zhatGen`/
  `zhat_topologicalClosure_eq_top` (P8), `levelRestrict`/`orderOf_levelRestrict_frobenius`/
  `levelField`+`FiniteDimensional` (P9).
- **ABSENT / not needed:** no "unique index-`n` subgroup of `Ẑ`" lemma (dissolved, see above); the
  `≅ Ẑ` iso itself was the gap, now filled.

### Pre-search expectation vs. reality

| I expected (pre-search) | Reality | Verdict |
|-------------------------|---------|---------|
| injectivity is the one substantive rung | yes | ✓ |
| needs "procyclic ⟹ unique index-`n` subgroup" (maybe a pass) | **not needed** — `ker χ_m = closure⟨zhatGen^m⟩` replaces it | ✗→better |
| `DiscreteTopology Gal(𝔽_{q^m}/K)` present (for ker open) | confirmed (`krullTopology_discreteTopology_of_finiteDimensional`) | ✓ |
| packaging falls out if injectivity lands | confirmed — iso closed same pass | ✓ |
| ledger stays `1 FOUNDATIONAL / 0 DEBT`, nothing posited | confirmed | ✓ |

## What was proved (Step 2 self-audit)

`Anabelian/FiniteFieldZHatIso.lean`, standard axioms only (in-file `#print axioms`):
`zhatToGalois_zhatGen`, `levelComp`, `levelComp_zhatGen`, `ker_levelComp_le`,
**`zhatToGalois_injective`**, **`galoisContinuousMulEquivZHat : galoisProfinite K ≃ₜ* ZHat`** (the
classical `Gal(𝔽_q̄/𝔽_q) ≃ₜ* Ẑ`).

**Did `≅ Ẑ` CLOSE? YES** — the full topological-group iso, standard-axioms-only, nothing posited.
**Recovers nothing from an abstract group** (structure of a *given* finite field's `Gal`). No new
`structure`/`class` (no rule-2 obligation); no load-bearing hypothesis beyond `K` finite; no owed
witness. **D1 did not recur** (finite fields).

## Ledger delta

- **0 `DEBT` / 0 new `FOUNDATIONAL`.** Active axioms unchanged: 1 `FOUNDATIONAL`
  (`residueReduction_surjective`, Pass 5, unused here), 0 `DEBT`. 0 open owed witnesses.
  **`≅ Ẑ` sub-target: DONE.**

## Scope: what closing `≅ Ẑ` means for L1, pointer to Pass 11

The project now has its **first deep L1 whole** — a genuine anabelian-flavored complete theorem, the
calibration target. **Remaining open L1 item:** the residue-surjection boundary discharge
(`residueReduction_surjective`, Pass 5 `FOUNDATIONAL`), still blocked on the absent valuation on `K̄`
(no `K^ur`/`𝒪[K̄]` assembled from `SpectralNorm`). **Pass 11 options (honest):** (a) begin the
valuation-on-`K̄` construction toward discharging the one `FOUNDATIONAL` (`FOUNDATIONAL → DEBT`,
multi-pass, the only way to drive `FOUNDATIONAL` down); or (b) open a fresh L1 sub-target (e.g. the
unramified/tame/wild ramification filtration, L2-adjacent). With `≅ Ẑ` closed, the bar (a deep whole)
is met once; the climb up the ladder continues.

---

# Pass 11 — rung L1 inflection: route (a), begin discharging the one boundary (2026-05-30)

## The inflection decision (the primary deliverable, documented before code)

Rung **L1**, **no reconstruction (R1–R3)**. Pass 10 banked `≅ Ẑ`; the danger this introduces is
**breadth-without-depth** — opening clean axiom-free fragments while the one boundary
`residueReduction_surjective` (Pass 5) sits undischarged forever, the IUT-Stage-1 replay at project
scale. So this pass's primary deliverable is a **reasoned fork decision**, not a default target.

**The fork:** (a) begin discharging the boundary, vs (b) open an independent deep sub-target (e.g. the
ramification filtration). **Decision: (a)**, driven by two findings:

1. **Common-prerequisite finding** (the question that collapses the fork): the **valuation on `K̄` is
   the common gate** for both. (a) needs it for the residue field `𝓀[K̄]` and the reduction map; (b)'s
   lower-numbering ramification groups `G_i` are defined *via* the valuation, and the
   unramified/tame/wild filtration sits *on* the residue reduction (the L1 boundary). And the
   filtration machinery itself (`G_i`, Herbrand `ψ/φ`) is **ABSENT** (re-confirmed). So (b) is **not**
   an independent escape from (a) — it needs the same absent valuation. Beginning the valuation on `K̄`
   is the **highest-leverage** move (unblocks the most).
2. **Tractability correction to Pass 6.** Pass 6 called the valuation on `K̄` "irreducibly absent."
   **Wrong.** `spectralNorm.normedField` + `NormedField.toValued` give `Valued K̄ ℝ≥0` (cf.
   `NumberTheory/Padics/Complex.lean`, which builds exactly this for `ℂ_p`), whence `𝒪[K̄]`/`𝓀[K̄]`;
   `Krasner.lean`'s `IsKrasner` is the lifting machinery. Only the final maximal-unramified lifting
   assembly is genuinely absent.

(b) declined as breadth-drift-relative-to-(a): it cannot escape the valuation gate, and pure
finite-field fragments would be exactly the clean-build padding the inflection warns against.

## Deepened inventory (real names; PRESENT/ABSENT)

- **PRESENT (used / for the route):** `spectralNorm` (`Analysis/Normed/Unbundled/SpectralNorm.lean`):
  `spectralNorm_mul` (submult, `≤`), `isNonarchimedean_spectralNorm`, `spectralNorm_one/zero/neg`,
  `spectralNorm_nonneg`, **`spectralNorm_eq_of_equiv`** (Galois ⟹ isometry — the invariance),
  `spectralNorm.normedField`/`spectralNorm.normedAlgebra` (the `NormedField K̄`);
  `NormedField.toValued` + `Valued.toNormedField` (`Topology/Algebra/Valued/NormedValued.lean`, the
  rank-one bridges); `𝒪[K]`/`𝓂[K]`/`𝓀[K]` notation (`Topology/Algebra/Valued/ValuativeRel.lean`);
  **`IsKrasner`** (`Analysis/Normed/Field/Krasner.lean`, `of_completeSpace`/`of_completeSpace_of_normal`
  — the lifting). `NumberTheory/Padics/Complex.lean` is the worked precedent (`Valued (PadicAlgCl p)`).
- **ABSENT (the genuine remainder):** `spectralNorm → Valuation/ValuativeRel` as a *named* bridge (one
  goes via `NormedField.toValued`); the ramification filtration `G_i`/Herbrand (L2); the
  maximal-unramified / lifting assembly that proves surjectivity (the `DEBT`'s heart).
- **Typeclass gap:** `IsNonarchimedeanLocalField K` (the boundary's setting) is `ValuativeRel`-based
  and does **not** directly give `NormedField K`; the bridge is
  `ValuativeRel → Valued → RankOne → Valued.toNormedField` (route step 2). So Pass 11's brick is built
  over the natural complete-nonarch-normed setting and connected to the exact statement later.

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| valuation-on-`K̄` is the common gate for (a) & (b) | confirmed (filtration sits on residue reduction + needs the valuation) | ✓ |
| Pass 6's "valuation absent" still holds | **corrected** — `spectralNorm.normedField`/`toValued`/`IsKrasner` PRESENT | ✗→fixed |
| (a) is highest-leverage; (b) not independent | confirmed | ✓ |
| can build the valuation-ring brick axiom-free this pass | confirmed (`spectralIntegers`) | ✓ |

## What was built (Step 2 self-audit)

`Anabelian/SpectralValuation.lean`, standard axioms only (in-file `#print axioms`):
- `spectralIntegers K : Subring (AlgebraicClosure K)` — the spectral valuation ring
  `𝒪[K̄] = {x | spectralNorm K K̄ x ≤ 1}` (subring via nonarch + submult). `mem_spectralIntegers`.
- `spectralIntegers_mem_iff_galois` — `Gal(K̄/K)` preserves `𝒪[K̄]` (isometry, `spectralNorm_eq_of_equiv`).

**Strictly-lower, axiom-free, on the discharge path** (the valuation on `K̄` is route step 1 and the
common gate — not adjacent). **Nothing posited:** the lifting/surjectivity (the irreducible heart) is
untouched — positing it would be the cardinal sin. Honest grade: the **first brick**, not the discharge.

## Ledger move (the first pass to legitimately *raise* `DEBT`)

**Reclassified `residueReduction_surjective` `FOUNDATIONAL → DEBT`** (Reclassification log, first entry)
— a **genuine** commitment backed by begun construction (step 1) + a corrected, probe-verified route,
**not paper**. Count: **`1 FOUNDATIONAL / 0 DEBT` → `0 FOUNDATIONAL / 1 DEBT`.** This is the *good*
direction for route (a): you cannot discharge what you never commit to, and the metric is net `DEBT`
reduction over time (the boundary is now a committed-and-under-construction debt, not a static posit).
**No second `FOUNDATIONAL`; nothing cardinal-sin posited.** Pass 11 file itself adds **0 axioms**.

D1 (ℚ-diamond) did **not** recur (abstract nonarch normed field + its algebraic closure; no
`Algebra ℚ (AlgebraicClosure ℚ)`). No new `structure`/`class` (no rule-2 obligation). No owed witness.
Recovers nothing from an abstract group.

## Scope: pointer to Pass 12

Route (a) continues: **Pass 12** should advance the bridge `IsNonarchimedeanLocalField → NormedField`
(step 2) and/or the residue field `𝓀[K̄]` + reduction map (step 3), toward the lifting (step 4, the
`DEBT`'s heart, via `IsKrasner` + maximal-unramified). The same valuation-on-`K̄` infrastructure also
unblocks L2 (ramification filtration) — so route (a) is the project's current spine. The one `DEBT` is
now committed and under construction; driving it to a theorem (net `DEBT` → 0) is the standing
objective, and it is no longer deferrable.

---

# Pass 12 — rung L1, route (a): the lifting is NOT a wall (keystone present) (2026-05-30)

## The primary deliverable: the lifting-tractability verdict

Rung **L1**, **no reconstruction (R1–R3)**. Pass 11 began route (a) and flagged the **lifting** — "every
residue automorphism lifts to `Gal(K̄/K)`", the heart of `residueReduction_surjective`, which Pass 6
called "irreducibly absent" — as the unverified hard step, with the failure mode being: build passes of
bottom-up infrastructure and only then hit a wall. This pass **front-loaded that uncertainty**.

**Verdict: the lifting is NOT a wall. The keystone is PRESENT.** Mathlib proves the residue-reduction
surjectivity directly in the profinite setting:
**`Ideal.Quotient.stabilizerHom_surjective_of_profinite`** (`RingTheory/Invariant/Profinite.lean`) —
for a profinite group `G` acting continuously on a discrete commutative ring `B` over `A`, with
`Algebra.IsInvariant A B G` and `Q` prime over `P`, the decomposition group `stabilizer G Q` **surjects
onto** `Aut((B/Q)/(A/P))` (the residue-field automorphisms). It is assembled from the finite-level
arithmetic Frobenius (`exists_of_isInvariant` / `stabilizerHom_surjective`,
`RingTheory/Invariant/Basic.lean` + `Frobenius.lean`) via the **same profinite-limit machinery used to
close `≅ Ẑ`** (`ProfiniteGrp.isoLimittoFiniteQuotientFunctor`,
`exist_openNormalSubgroup_sub_open_nhds_of_one`, `nonempty_sections_of_finite_cofiltered_system`).

Applied with `G = Gal(K̄/K)`, `B = 𝒪[K̄]`, `A = 𝒪[K]`, `Q = 𝔪[K̄]`, `P = 𝔪[K]` (where `stabilizer = ⊤`,
the maximal ideal being the unique prime over `𝔪[K]`), this **is** the surjection `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)`.
So **no maximal-unramified / `K^ur` construction is needed** — correcting both Pass 6 and Pass 11.

## Deepened inventory (real names; PRESENT/ABSENT)

- **PRESENT — the keystone and its engine:** `Ideal.Quotient.stabilizerHom_surjective_of_profinite`
  (profinite, the absolute surjectivity); `Ideal.Quotient.stabilizerHom_surjective` /
  `IsFractionRing.stabilizerHom_surjective` (`RingTheory/Invariant/Basic.lean`, finite-level
  decomposition→residue surjectivity); `AlgHom.IsArithFrobAt` + `exists_of_isInvariant`
  (`RingTheory/Frobenius.lean`, the finite-level Frobenius lift); `Algebra.IsInvariant`,
  `IsInvariantSubring` + `IsInvariantSubring.toMulSemiringAction` (`Algebra/Ring/Action/Invariant.lean`);
  `MulSemiringAction (K̄ ≃ₐ[K] K̄) K̄`.
- **ABSENT — and NOT needed (route-pruning finding):** `K^ur` / maximal-unramified extension / the
  unramified Galois correspondence (zero hits — Pass 6's feared edifice). `IsKrasner`
  (`Krasner.lean`) is **field-generation** (Krasner's lemma: close roots ⟹ subfield containment),
  **not** Galois-automorphism lifting — so Pass 11's "IsKrasner supplies the lifting" was wrong; it is
  irrelevant to the discharge. The keystone bypasses all of this.
- **ABSENT — the remaining bounded setup (steps 2–3):** `𝒪[K̄]` as an `Algebra.IsInvariant 𝒪[K] · Gal`
  discrete-continuous algebra (the keystone's hypotheses); `B/Q ≅ 𝓀̄` (residue of `K̄` = alg closure of
  `𝓀[K]`); `stabilizer = ⊤`.

### Pre-search expectation vs. reality

| I expected (pre-search) | Reality | Verdict |
|-------------------------|---------|---------|
| lifting likely a wall / long maximal-unramified construction | **NOT a wall** — `stabilizerHom_surjective_of_profinite` supplies it directly | ✗→far better |
| `IsKrasner` + Hensel supply the lifting | `IsKrasner` is field-generation, not lifting — irrelevant; the real engine is `RingTheory/Invariant` | ✗→corrected |
| discharge = long bounded sub-plan | bounded sub-plan, but the **hardest step is PRESENT** (only setup remains) | ✓ (better) |
| ledger stays `0 FOUNDATIONAL / 1 DEBT`, `DEBT` open | confirmed | ✓ |

## What was built (Step 2 self-audit)

`Anabelian/ResidueReductionRoute.lean`, standard axioms only (in-file `#print axioms`):
- `spectralIntegers_isInvariant` — `IsInvariantSubring (Gal(K̄/K)) (spectralIntegers K)` (from Pass 11's
  `spectralIntegers_mem_iff_galois`). Via `IsInvariantSubring.toMulSemiringAction` this yields the
  `MulSemiringAction (Gal(K̄/K)) 𝒪[K̄]` the keystone consumes — **route step 1b**, strictly-lower,
  axiom-free, genuinely on-route (not the lifting in disguise).

**Nothing cardinal-sin posited:** the surjection is **not** stubbed — it is a present Mathlib theorem to
be *applied* (step 4), never posited. No new axiom. **`DEBT` status: OPEN** (the
`axiom residueReduction_surjective` is still present; discharge ⟺ its deletion). **Recovers nothing from
an abstract group.** No new `structure`/`class` (no rule-2 obligation). **D1 did not recur** (abstract
nonarch normed field).

## `DEBT` status and ledger delta

- **`DEBT` open. Single `DEBT` (`residueReduction_surjective`); no new axiom; no reclassification.**
  Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**. **Route-steps remaining: [Step 2
  `Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal` framing (discrete + `ContinuousSMul`); Step 3 residue
  identification `𝓀̄/𝓀` + `stabilizer = ⊤`; Step 4 apply `stabilizerHom_surjective_of_profinite`].**
- Steps 1 (Pass 11) and 1b (Pass 12) done axiom-free. The unit of progress this phase is strictly-lower
  bricks; the ledger sits at `0 FOUNDATIONAL / 1 DEBT` honestly while they accumulate toward the keystone.

## Scope: pointer to Pass 13

Pass 13: **step 2** — construct `B = integralClosure 𝒪[K] (AlgebraicClosure K)` (= `𝒪[K̄]`) as an
`Algebra.IsInvariant 𝒪[K] B (Gal(K̄/K))` discrete-topology continuous-action algebra (the keystone's
exact hypotheses), connecting `IsNonarchimedeanLocalField K`'s `𝒪[K]`/`ValuativeRel` to this framing.
Then Pass 14: step 3 (residue identification + `stabilizer = ⊤`), Pass 15: step 4 (apply the keystone,
**delete the axiom** — discharge). The discharge is now a concrete, bounded, keystone-anchored
sub-plan; net `DEBT` → 0 is genuinely in sight, no longer a static boundary.

---

# Pass 13 — rung L1, route (a): keystone fit-verdict + route pivot to `integralClosure` (2026-05-30)

## Primary deliverable: the keystone's exact-hypothesis fit-verdict

Rung **L1**, **no reconstruction (R1–R3)**. The discharge of `residueReduction_surjective` applies
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` (Pass 12). Per the route-first-step discipline,
I probed its **exact hypotheses**: `A B : CommRing`, `Algebra A B`, `[MulSemiringAction G B]
[SMulCommClass G A B]`, `G` profinite (`CompactSpace` + `TotallyDisconnectedSpace` + `IsTopologicalGroup`),
`B` with `[TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]`, `(P) (Q) [Q.IsPrime]
[Q.LiesOver P] [Algebra.IsInvariant A B G]`; conclusion `stabilizer G Q ↠ Aut((B/Q)/(A/P))`.

**Two findings (the verdict):**
1. **`B` must be `DiscreteTopology`** — the keystone's `B`-topology is the *algebraic/Krull* (discrete)
   one, `ContinuousSMul G B` meaning open stabilizers, **not** the valuation topology on `𝒪[K̄]`. So `B`
   is given the discrete topology (free on the ring); the Pass-11/12 spectral/valuation topology is not
   what the keystone consumes. Reframing, not a wall.
2. **`G = Gal(K̄/K)` profinite needs `IsGalois K (AlgebraicClosure K)`** — probe-verified ABSENT for a
   general field (`CompactSpace Gal(K̄/K)` and `IsGalois K (AlgebraicClosure K)` both fail to synthesize
   without perfectness). Holds for perfect `K` (char-0 / mixed-char local fields); fails for imperfect
   equal-char (`𝔽_q((t))`, `K̄/K` inseparable). A **genuine route prerequisite**, now tracked: the
   keystone discharge needs `Gal(K̄/K)` profinite (via `[IsGalois K K̄]`), the imperfect case via the
   separable-closure framing (`Aut(K̄/K) ≅ Gal(K^sep/K)`) — deferred.

## Route pivot (correcting Pass 11's spectralNorm route): use `integralClosure 𝒪[K] K̄`

The keystone wants `B` a `CommRing` with `Algebra A B` + `Algebra.IsInvariant A B G` + the action — i.e.
`B = integralClosure 𝒪[K] K̄` over `A = 𝒪[K]`, **native to `IsNonarchimedeanLocalField`'s `ValuativeRel`**.
This pivots off the `spectralNorm` route and **avoids the `IsNonarchimedeanLocalField → NormedField`
bridge entirely — so the watched bridge-diamond (D2) is NOT incurred** (`ROADMAP.md` D2). `spectralNorm`
(`𝒪[K̄] = spectralIntegers K`, P11–12) is a valid identification of the same ring but off the critical
path.

## Deepened inventory (real names; PRESENT/ABSENT)

- **PRESENT (used):** `IsNonarchimedeanLocalField` + `𝒪[K]` (`ValuativeRel`; the `CommRing ↥𝒪[K]`,
  `Algebra ↥𝒪[K] (AlgebraicClosure K)`, `IsScalarTower ↥𝒪[K] K (AlgebraicClosure K)` instances all
  synthesize); `integralClosure` + `.toSubring`; `IsIntegral.map` + `AlgHom.restrictScalars`
  (integrality preservation under a `K`-linear, hence `𝒪[K]`-linear, σ); `IsInvariantSubring` +
  `IsInvariantSubring.toMulSemiringAction`; `MulSemiringAction (K̄ ≃ₐ[K] K̄) K̄`;
  `AlgEquiv.mapIntegralClosure` / `integralClosure_map_algEquiv`.
- **ABSENT / remaining (steps 2–3):** `Algebra.IsInvariant 𝒪[K] (integralClosure 𝒪[K] K̄) Gal` (the
  fixed-points-= base theorem); `DiscreteTopology`/`ContinuousSMul` setup; `IsGalois K K̄` profinite
  prerequisite; `𝒪[K̄]/𝔪 ≅ AlgebraicClosure 𝓀[K]` (residue of `K̄` = alg closure of `𝓀`) + the `Aut`
  identification; `stabilizer = ⊤` (unique prime over `𝔪[K]`, Henselian).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| `𝒪[K̄]`/`Gal` may not literally fit; bridge/reframing needed | confirmed — `B` discrete + `Gal` profinite-needs-`IsGalois` | ✓ |
| not reach axiom-removal (discharge) this pass | confirmed — steps 2–3 substantial; partway with tracker | ✓ |
| identification lemmas substantial | confirmed; but the **action** brick landed cleanly over the exact setting | ✓ (+pivot) |
| watch the `NormedField`-bridge diamond | **avoided** by pivoting to `integralClosure` — no D2 | ✓ (better) |

## What was built (Step 2 self-audit)

`Anabelian/ResidueReductionIntegral.lean`, standard axioms only (in-file `#print axioms`):
- `galoisIntegers K` — the keystone's ring `B = 𝒪[K̄] = integralClosure 𝒪[K] K̄` (`Subring`).
- `isIntegral_map_galois` — `σ ∈ Gal(K̄/K)` preserves integrality over `𝒪[K]`.
- `galoisIntegers_isInvariant` — `IsInvariantSubring (Gal(K̄/K)) 𝒪[K̄]` ⟹ (via
  `IsInvariantSubring.toMulSemiringAction`) the `MulSemiringAction G B` the keystone consumes
  (**route step 1b, over the keystone's actual `B`, in the exact `IsNonarchimedeanLocalField` setting**).

**Headline status: the axiom was NOT removed — `DEBT` remains the single open entry.** Strictly-lower,
axiom-free, genuinely below the surjection (the action on `B`, not the lifting). **Nothing cardinal-sin
posited** (the surjection is a present theorem to be *applied*, never stubbed; no new `DEBT`/`FOUNDATIONAL`).
**Recovers nothing from an abstract group.** No new `structure`/`class` (no rule-2 obligation). **D1
N/A** (local field); **D2 not incurred** (route avoids the `NormedField` bridge).

## `DEBT` status and ledger delta

- **`DEBT` OPEN. Route-steps remaining: [Step 2 `Algebra.IsInvariant 𝒪[K] 𝒪[K̄] Gal` + discrete +
  `ContinuousSMul` + `IsGalois K K̄` prerequisite; Step 3 residue `𝒪[K̄]/𝔪 ≅ AlgebraicClosure 𝓀[K]` +
  `Aut` + `stabilizer = ⊤`; Step 4 apply keystone, delete axiom].** Steps 1, 1b done (Pass 13) over the
  keystone's actual `B`.
- **Ledger unchanged: `0 FOUNDATIONAL / 1 DEBT`.** No new axiom; no reclassification.

## Scope: pointer to Pass 14

Pass 14: **step 2** — establish `Algebra.IsInvariant 𝒪[K] (integralClosure 𝒪[K] K̄) (Gal(K̄/K))` (the
fixed points `𝒪[K̄]^Gal = 𝒪[K]`), give `galoisIntegers K` the discrete topology with `ContinuousSMul`
(open stabilizers of the Galois action), and address the `IsGalois K (AlgebraicClosure K)` profinite
prerequisite (start with the perfect / char-0 local-field case where it holds). Then Pass 15: step 3
(residue identification + `stabilizer = ⊤`), Pass 16: step 4 (apply the keystone, **delete the axiom** —
net `DEBT` → 0). The discharge is a concrete, keystone-anchored, bounded sub-plan with one tracked
prerequisite (perfectness); not a static boundary.

---

# Pass 14 — rung L1, route (a): fixed-ring `𝒪[K̄]^Gal = 𝒪[K]` + the generality decision (2026-05-30)

## Job B — the generality decision (primary, not optional)

Rung **L1**, **no reconstruction**. The keystone `stabilizerHom_surjective_of_profinite` needs
`Gal(K̄/K)` **profinite** = `IsGalois K (AlgebraicClosure K)` ⟺ **`K` perfect** (`PerfectField K ⟹
IsGalois K K̄`, confirmed). Mixed-char / char-0 local fields are perfect; imperfect equal-char (`𝔽_q((t))`)
are not.

**Investigation — is `residueReduction_surjective` true *as stated* for imperfect `K`? YES.**
`Field.absoluteGaloisGroup K = Aut(K̄/K)`; for imperfect `K`, `K̄/K^sep` is purely inseparable, so each
`K`-automorphism of `K̄` is determined by its rigid restriction to `K^sep`, giving `Aut(K̄/K) ≅
Gal(K^sep/K)` (profinite). The residue field `𝓀[K]` is **finite, hence perfect**, so the residue
reduction `Gal(K^sep/K) ↠ Gal(𝓀̄/𝓀)` holds by standard unramified theory. So the statement is true for
all local fields — the obstruction is only that the keystone *as applied* needs `Gal(K̄/K)` *literally*
profinite (`IsGalois K K̄`), which Mathlib gates on perfectness.

**Decision: option (a) — narrow to the perfect case, track the imperfect case.** The discharging
`theorem` (a later pass) will carry `[PerfectField K]`, the narrowing documented in its docstring +
ledger, and the **imperfect equal-char case is a named tracked remainder** (`ROADMAP.md`), to be proven
via the `Aut(K̄/K) ≅ Gal(K^sep/K)` framing — never silently dropped. Not enacted this pass (axiom not
removed); decided + recorded.

## Job A — the fixed-ring identification (step-2 core, perfect case)

`Anabelian/ResidueReductionInvariant.lean`, standard axioms only (in-file `#print axioms`):
- `galoisIntegers_algebraIsInvariant` — **`Algebra.IsInvariant 𝒪[K] (integralClosure 𝒪[K] K̄) Gal`**
  (`𝒪[K̄]^Gal = 𝒪[K]`) for perfect `K`, one of the keystone's hypotheses. Proof: a `Gal`-fixed `b` has
  `(b : K̄) ∈ fixedField ⊤ = (⊥ : IntermediateField K K̄) = K` (`InfiniteGalois.fixedField_fixingSubgroup`
  + `fixingSubgroup_bot` + `mem_fixedField_iff`); `b` integral over `𝒪[K]`; integrality descends through
  the injective `K → K̄` (`isIntegral_algebraMap_iff`); `𝒪[K]` integrally closed in `K = Frac 𝒪[K]`
  (`IsIntegrallyClosed.isIntegral_iff`) ⟹ `b ∈ 𝒪[K]`.

## Deepened inventory (real names; PRESENT/ABSENT)

- **PRESENT (used):** `PerfectField K → IsGalois K (AlgebraicClosure K)`;
  `InfiniteGalois.fixedField_fixingSubgroup` (the infinite Galois correspondence, `K̄^Gal = K`);
  `IntermediateField.fixingSubgroup_bot`, `mem_fixedField_iff`, `IntermediateField.mem_bot`;
  `isIntegral_algebraMap_iff` (integrality descent, injective algebraMap);
  `IsIntegrallyClosed.isIntegral_iff` + `IsFractionRing ↥𝒪[K] K`; `FaithfulSMul.algebraMap_injective`.
- **ABSENT (the confirmed discharge blocker, step 3):** `𝒪[K̄]/𝔪[K̄] ≅ AlgebraicClosure 𝓀[K]` — the
  residue field of `K̄` is the algebraic closure of `𝓀` — no `ResidueField`-of-algebraic-closure API
  (and no integral-closure-residue API). A substantial sub-construction (residue alg-closed + algebraic
  over `𝓀` ⟹ `≅ AlgebraicClosure`).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| statement true for imperfect `K` | confirmed (`Aut(K̄/K) ≅ Gal(K^sep/K)`, residue finite/perfect) | ✓ |
| fixed-ring `𝒪[K̄]^Gal = 𝒪[K]` reachable (moderate) | landed cleanly (the InfiniteGalois fixed-field + integrally-closed chain) | ✓ |
| residue iso the hard blocker | confirmed ABSENT, substantial — the next obstacle | ✓ |
| not reach axiom-removal this pass | confirmed (blocked on residue iso) | ✓ |

## What was built (Step 2 self-audit) + HEADLINE status

Built `galoisIntegers_algebraIsInvariant` (step-2 core, perfect case), axiom-free, strictly-lower.
**HEADLINE: the axiom was NOT removed — `residueReduction_surjective` remains the single open `DEBT`.**
**Route-steps remaining: [Step 2b `DiscreteTopology` + `ContinuousSMul`; Step 3 residue iso (the ABSENT
blocker) + `stabilizer = ⊤`; Step 4 apply keystone + delete axiom, perfect-case narrowing].** Steps 1,
1b, 2a done. **Nothing cardinal-sin posited** (no sub-step stubbed with a new `DEBT`; the surjection is
a present theorem to be applied). **Recovers nothing from an abstract group.** No new `structure`/`class`
(no rule-2). **D1** N/A; **D2 not incurred** (integral-closure route, no `NormedField` bridge).

## Ledger delta

- **0 / 0.** No new axiom; no reclassification. Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`** (open).
  The unit of progress this phase is strictly-lower axiom-free bricks toward the keystone application.

## Scope: pointer to Pass 15

Pass 15: **step 3 — the residue identification** `𝒪[K̄]/𝔪[K̄] ≅ AlgebraicClosure 𝓀[K]` (the ABSENT
blocker: residue field of `K̄` is alg-closed + algebraic over `𝓀`), the `Aut = Gal(𝓀̄/𝓀)` identification,
and `stabilizer 𝔪[K̄] = ⊤` (unique prime over `𝔪[K]`, Henselian). Plus step 2b (`DiscreteTopology` +
`ContinuousSMul`). Then step 4: apply `stabilizerHom_surjective_of_profinite`, **delete the axiom**
(perfect-case, documented narrowing), and track the imperfect case — net `DEBT` → 0 for the perfect
case. The residue iso is the one remaining hard lemma; the rest of the route is assembled.

---

# Pass 15 — rung L1, route (a): Step 2b (`ContinuousSMul`) + the residue-iso verdict (2026-05-30)

## Primary deliverable: the residue-identification tractability verdict

Rung **L1**, **no reconstruction**. The discharge (perfect case) applies
`stabilizerHom_surjective_of_profinite` to `B = 𝒪[K̄] = integralClosure 𝒪[K] K̄`; the one remaining hard
step was the **residue iso** `𝒪[K̄]/𝔪[K̄] ≅ AlgebraicClosure 𝓀[K]` (Pass 14's pinpointed blocker).
Front-loaded its tractability. **Verdict: a BOUNDED multi-pass sub-plan, not a wall.** Decomposition:
- **3a. `𝒪[K̄]` local + `Q = 𝔪[K̄]`** — `𝒪[K̄]` is the valuation ring of the (unique, `𝒪[K]` complete)
  extension to `K̄`. **ABSENT** as a direct lemma; reachable via the valuation-integral-closure API
  (`RingTheory/Valuation/AlgebraInstances.lean`), **NOT** `spectralNorm` (that re-introduces the
  `NormedField` bridge / **D2** — avoid). Substantial.
- **3b. residue algebraic over `𝓀[K]`** — residue classes lift to integral (hence algebraic) elements.
  Moderate.
- **3c. residue `𝓀̄` algebraically closed** — **ABSENT** (no `IsAlgClosed`-of-residue API). From-scratch:
  monic poly over `𝓀̄` lifts to monic over `𝒪[K̄] ⊆ K̄` (alg closed), root is integral ⟹ in `𝒪[K̄]` ⟹
  reduces to a root in `𝓀̄`. Uses `K̄` alg-closed + integral-closure, **not** Hensel (`K̄` not complete ⟹
  `𝒪[K̄]` not Henselian — the naive Hensel route fails). Substantial.
- **3d. `𝓀̄ ≅ AlgebraicClosure 𝓀[K]`** — `isAlgClosure_iff` (`IsAlgClosed ∧ Algebra.IsAlgebraic ↔
  IsAlgClosure`) + `IsAlgClosure.equiv`. **Supported.**
- **3e. `Aut(𝓀̄/𝓀[K]) ≅ Field.absoluteGaloisGroup 𝓀[K]`** — transport along 3d. Supported.

So the residue iso is reachable (~2–3 passes; 3a/3c the substantial from-scratch pieces, 3d/3e supported)
— **not a wall**.

## Built — Step 2b (`ContinuousSMul`, a keystone hypothesis)

`Anabelian/ResidueReductionContinuity.lean`, standard axioms only (in-file `#print axioms`):
- `galoisStabilizer_isOpen` — every stabilizer of the Galois action on `𝒪[K̄] = integralClosure 𝒪[K] K̄`
  is **open** in `Gal(K̄/K)`: it equals the stabilizer of the underlying `(b : K̄)`, open by
  `stabilizer_isOpen_of_isIntegral` (`K̄/K` integral; the coe-of-action bridge `↑(σ•b) = σ↑b` is `rfl`).
- `continuousSMul_galoisIntegers` — hence with the **discrete** topology on `𝒪[K̄]` (the keystone's
  choice), `ContinuousSMul Gal(K̄/K) 𝒪[K̄]` (`continuousSMul_iff_stabilizer_isOpen`). **Step 2b** —
  `DiscreteTopology B` + `ContinuousSMul G B` — discharged, strictly-lower, axiom-free.

## Deepened inventory (real names; PRESENT/ABSENT)

- **PRESENT (used):** `stabilizer_isOpen_of_isIntegral` (`KrullTopology.lean`, integral ext ⟹ open
  krull stabilizers); `continuousSMul_iff_stabilizer_isOpen` + `MulAction.stabilizer` API
  (`Topology/Algebra/MulAction.lean`). For 3d/3e: `isAlgClosure_iff`, `IsAlgClosure.equiv`
  (`FieldTheory/IsAlgClosed/Basic.lean`).
- **ABSENT (the residue-iso remainder):** `IsLocalRing (integralClosure …)` / valuation-extension
  uniqueness to `K̄` (3a); `IsAlgClosed`-of-residue-field (3c). Both from-scratch but bounded.

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| residue iso a bounded sub-plan, not a wall | confirmed — 3a/3c substantial, 3d/3e supported | ✓ |
| Step 2b cheap and reachable | confirmed (`stabilizer_isOpen_of_isIntegral` + `continuousSMul_iff…`) | ✓ |
| `spectralNorm` re-entry for 3a risks D2 | confirmed — flagged; use the `ValuativeRel` route instead | ✓ |
| not reach axiom-removal this pass | confirmed (3a/3c remain) | ✓ |

## What was built + HEADLINE status

`galoisStabilizer_isOpen`, `continuousSMul_galoisIntegers` (Step 2b), axiom-free, strictly-lower.
**HEADLINE: the axiom was NOT removed — `residueReduction_surjective` remains the single open `DEBT`.**
**Route-steps remaining: [Step 3a–3c (residue iso, the substantial remainder); 3d/3e (supported); Step
4 apply keystone + delete axiom (perfect-case)].** Done: 1, 1b, 2a, 2b. **Nothing cardinal-sin posited**
(no sub-step stubbed; residue iso to be built, surjection to be applied). **Recovers nothing from an
abstract group.** No new `structure`/`class` (no rule-2). **D1** N/A; **D2 not incurred** (and the
`spectralNorm` 3a-re-entry is flagged as a D2 risk to avoid).

## Ledger delta

- **0 / 0.** No new axiom; no reclassification. Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`** (open).

## Scope: pointer to Pass 16

Pass 16: **steps 3a + 3c** — the two substantial from-scratch lemmas: `𝒪[K̄] = integralClosure 𝒪[K] K̄`
is **local** with maximal ideal `𝔪[K̄]` (the valuation ring of `K̄`, via the valuation-integral-closure
API — avoiding the `spectralNorm`/D2 bridge), and its **residue field is algebraically closed** (the
monic-lift argument; not Hensel). Then 3b (residue algebraic), 3d/3e (`IsAlgClosure` repackaging), and
step 4 (apply `stabilizerHom_surjective_of_profinite`, **delete the axiom** — perfect-case, documented
narrowing; the imperfect equal-char case stays tracked). Net `DEBT` → 0 for the perfect case is ~2–3
passes out; the two named hard lemmas (3a, 3c) are the gate.

---

# Pass 16 — rung L1, route (a): brick 3c (residue field alg-closed) + the D2-fork decision (2026-05-30)

## Restatement (i)–(iv), pre-search

(i) **Target:** the two from-scratch residue-iso bricks — 3a (`𝒪[K̄] = integralClosure 𝒪[K] K̄` local,
`𝔪[K̄]` its maximal ideal) and 3c (residue field algebraically closed). (ii) **3c depends on 3a** (the
residue field is only a field once `𝒪[K̄]` is local). (iii) **PRIMARY DISCIPLINE:** route-first-step on
3a — probe the valuation-extension-to-`K̄` / `IsLocalRing (integralClosure …)` API *before* building,
and make the **D2 fork an explicit logged decision** (native `ValuativeRel` route = no D2 vs.
`spectralNorm` route = tracked D2). 3c via the **monic-lift** argument, NOT Hensel. (iv) **Will not:**
stub any residue-iso brick; claim discharge while the axiom exists; silently incur or route around D2;
add a second sub-target.

## 3a route-first-step probe — the finding (deepened beyond Pass 15)

Probed `RingTheory/Valuation/AlgebraInstances.lean`, the `ValuativeRel`/`Valued` extension theory, and
the `spectralNorm` route:

- **`AlgebraInstances.lean`** has the integral-closure-of-valuationSubring algebra API
  (`algebraMap_injective`, `isIntegral_of_mem_ringOfIntegers`, the `algebra`/`IsScalarTower` instances)
  but **NOT** local-ness — no `IsLocalRing (integralClosure …)`, no valuation-extension-to-algebraic, no
  Henselian-unique-extension. **ABSENT.**
- **Key reduction found:** `ValuationRing.isLocalRing : IsLocalRing A` is a **free** (priority-100)
  instance (`RingTheory/Valuation/ValuationRing.lean:266`). So 3a's local-ness **reduces to**
  "`integralClosure 𝒪[K] K̄` is a `ValuationRing`" — and `IsLocalRing` then comes for free. But that
  `ValuationRing` fact is the unique extension of a complete DVR's valuation to `K̄` (Serre II) —
  **ABSENT** from Mathlib.
- **`NormedField K` is NOT a global instance** for `IsNonarchimedeanLocalField K` (only a scoped
  `Valued.toNormedField`, used locally in `LocalField/Basic.lean:163`). And the `spectralNorm` route's
  bridge `spectralNorm x ≤ 1 ↔ IsIntegral 𝒪[K] x` is **ABSENT** (`Analysis/Normed/.../SpectralNorm.lean`
  has no such lemma).

## The D2 fork — DECIDED explicitly (the pass's primary discipline)

**Decision: native `ValuativeRel` route; D2 NOT incurred.** Reasoning: both routes need substantial
absent theory, but the `spectralNorm` route offers **no shortcut** for 3a — its `norm ≤ 1 ↔ integral`
link is equally absent, so connecting `spectralIntegers` to `integralClosure` is itself a missing lemma,
*and* it re-introduces the `NormedField`-on-`K` diamond. Taking on D2 would buy nothing. So the committed
3a target is the native **"`integralClosure 𝒪[K] K̄` is a `ValuationRing`"** (⟹ `IsLocalRing` free). This
deepens Pass 15's "3a substantial": 3a is a genuine from-scratch valuation-extension construction (the
single substantial remaining gate), not avoidable via `spectralNorm`.

## Built — brick 3c (route-independent, does NOT need 3a)

The insight that let 3c land **this** pass despite its stated dependence on 3a: 3c's *substance* is a
**general** fact, provable abstractly and applied to `𝒪[K̄]` with the maximal ideal left as a hypothesis
(supplied later by 3a). `Anabelian/ResidueAlgClosed.lean`, standard axioms only (in-file `#print axioms`):

- `residueField_isAlgClosed_of_integrallyClosed` — **the general 3c lemma.** `R` a subring of an
  alg-closed field `L` (`algebraMap R L` injective), integrally closed in `L` ⟹ `R ⧸ m` alg-closed for
  **any** maximal `m`. Proof chain: `p` monic over `R⧸m` → `lifts_and_natDegree_eq_and_monic` gives a
  monic `P` over `R` of the same degree → `P.map (algebraMap R L)` monic, degree ≥ 1 (`Monic.natDegree_map`
  + `Irreducible.natDegree_pos`) → `IsAlgClosed.exists_root` gives `r ∈ L` → `r` integral over `R` (root
  of monic `P`) → `r ∈ R` (integral-closedness `hcl`) → `Ideal.Quotient.mk m r` (= via `s`, `algebraMap s
  = r`) is a root of `p` (`eval_map` + `eval₂_at_apply`, injectivity to pull `eval s P = 0` from
  `algebraMap (eval s P) = aeval r P = 0`). `IsAlgClosed.of_exists_root` closes it.
- `galoisIntegers_integrallyClosed` — **`𝒪[K̄]` integrally closed in `K̄`** (the general lemma's `hcl`):
  `x` integral over `integralClosure 𝒪[K] K̄` ⟹ integral over `𝒪[K]` (`isIntegral_trans`, using the
  `integralClosure.AlgebraIsIntegral` instance) ⟹ in the integral closure (`IsIntegralClosure.isIntegral_iff`).
- `galoisResidueField_isAlgClosed` — **brick 3c for `𝒪[K̄]`**: the general lemma applied to `R = 𝒪[K̄]`,
  `L = K̄`, injectivity = `Subtype.coe_injective`. So for **any** maximal ideal `m` of `𝒪[K̄]`, the residue
  field `𝒪[K̄] ⧸ m` is algebraically closed. **3c done modulo 3a** (3a supplies that `𝔪[K̄]` is maximal).

## Deepened inventory (real names; PRESENT/ABSENT)

- **PRESENT (used in 3c):** `IsAlgClosed.of_exists_root`, `IsAlgClosed.exists_root`
  (`FieldTheory/IsAlgClosed/Basic.lean`); `lifts_and_natDegree_eq_and_monic`, `Polynomial.lifts_iff_coeff_lifts`
  (`Algebra/Polynomial/Lifts.lean`); `Polynomial.Monic.natDegree_map`, `eval_map`, `eval₂_at_apply`,
  `aeval_def`; `isIntegral_trans` + `integralClosure.AlgebraIsIntegral`, `IsIntegralClosure.isIntegral_iff`
  (`RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`); `Ideal.Quotient.field`, `Ideal.Quotient.mk_surjective`.
- **PRESENT (key 3a reduction):** `ValuationRing.isLocalRing` (free `IsLocalRing` from `ValuationRing`),
  `ValuationSubring.isLocalRing` (`RingTheory/Valuation/`).
- **ABSENT (the 3a gate):** "`integralClosure 𝒪[K] K̄` is a `ValuationRing`" / valuation-extension-to-`K̄`
  / Henselian-unique-extension; `spectralNorm x ≤ 1 ↔ IsIntegral`; `NormedField K` as a global instance.

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| 3a `IsLocalRing (integralClosure …)` reachable via the valuation API | ABSENT; reduces to "is a `ValuationRing`", itself absent (unique-extension) | deepened — 3a more substantial than Pass 15 said |
| `spectralNorm` route a viable D2-tradeoff for 3a | no shortcut — `norm ≤ 1 ↔ integral` also absent; D2 buys nothing | **decided: stay native, no D2** |
| 3c depends on 3a (need 𝓀̄ a field) → can't land this pass | 3c's *substance* is a general lemma (m left as hypothesis) → **landed route-independently** | ✓ better than expected |
| land 3a + 3c | landed **3c** (general + `𝒪[K̄]` discharges); 3a deepened to a verdict, not built | partial — 3c done, 3a is the gate |

## What was built + HEADLINE status

`residueField_isAlgClosed_of_integrallyClosed`, `galoisIntegers_integrallyClosed`,
`galoisResidueField_isAlgClosed` (brick 3c), axiom-free, strictly-lower, **route-independent (no D2)**.
**HEADLINE: the axiom was NOT removed — `residueReduction_surjective` remains the single open `DEBT`.**
**Route-steps remaining: [Step 3a `𝒪[K̄]` local = "`integralClosure` is a `ValuationRing`" (the one
substantial gate, native route, no D2); 3b residue algebraic; 3d/3e (supported); Step 4 apply keystone +
delete axiom (perfect-case)].** Done: 1, 1b, 2a, 2b (P13–15), **3c (P16)**. With 3c proved, the residue
iso reduces to **3a + supported repackaging**. **Nothing cardinal-sin posited** (3c is *proved*, not
stubbed; the surjection is to be *applied* from a present theorem). **Recovers nothing from an abstract
group.** No new `structure`/`class` (no rule-2). **D1** N/A; **D2 NOT incurred** (fork decided — native
route, `spectralNorm` rejected for offering no shortcut).

## Ledger delta

- **0 / 0.** No new axiom; no reclassification. Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`** (open).
  Progress = a strictly-lower brick proved (3c) + the D2-fork resolved + 3a deepened to a precise target.

## Scope: pointer to Pass 17

Pass 17: **step 3a — the one substantial remaining gate.** Build "`integralClosure 𝒪[K] K̄` is a
`ValuationRing`" (⟹ `IsLocalRing` for free via `ValuationRing.isLocalRing`, ⟹ `𝔪[K̄]` is *the* maximal
ideal, ⟹ `galoisResidueField_isAlgClosed` applies to give `𝓀̄` alg-closed). This is the native
`ValuativeRel` valuation-extension-to-`K̄` construction (complete-DVR valuation extends uniquely to the
algebraic closure; the integral closure is its valuation ring) — ABSENT, from-scratch, possibly itself
multi-pass. If it proves too large for one pass, decompose it honestly (e.g. uniqueness of the extension
via Henselianness of `𝒪[K]`) and land the reachable sub-brick. With 3a done: 3b (residue algebraic),
3d/3e (`IsAlgClosure` repackaging), then step 4 (apply `stabilizerHom_surjective_of_profinite`, **delete
the axiom** — perfect case, documented narrowing; imperfect equal-char tracked). The metric is net `DEBT`
reduction: 3c proved this pass, one named hard lemma (3a) plus supported repackaging stand between here
and net `DEBT` → 0 for the perfect case.

---

# Pass 17 — rung L1, route (a): the 3a three-route comparison + the bridge's algebraic half (2026-05-30)

## Restatement (i)–(iv), pre-search

(i) Pre-search pass-count guess: **(iii) Henselian-local-direct shortest** (if Mathlib has
"integral-closure of a Henselian local ring is local"); **(ii) spectralNorm** next (~1–2 passes + D2);
**(i) native ValuationRing** longest (~3). (ii) Probe: valuation-extension-to-`K̄` (route i);
`spectralNorm ≤ 1 ↔ integral` + `Valued.integer` local (route ii); Henselian-local ⟹ integral-closure
local + colimit (route iii). (iii) Bricks: land 3a if a route's key lemma is present, else strictly-lower
bricks + the named sub-plan; assess whether 3a/discharge are ≤2 passes out. (iv) Decide by **magnitude +
the D2 cost principle**, not reflex; never stub 3a/a residue-iso brick with a `DEBT`; claim discharge
only at axiom-removal.

## The three-route probe (real names) — reality vs. expectation

- **(iii) Henselian-local-direct.** `HenselianLocalRing` exists (`Henselian.lean:108`), `Field.henselian`
  + `IsAdicComplete.henselianRing` exist. But **`grep Henselian` hits only `Henselian.lean`** — its
  `TFAE` (`:119`) is root-lifting only, **no** integral-closure-local clause; and `HenselianLocalRing
  𝒪[K]` does **not** synthesize. So the key lemma is absent, must be built from TFAE, plus a colimit to
  `K̄`. **~2–3 passes, no D2.** (My pre-search hope that Mathlib had it was wrong.)
- **(i) native `ValuationRing`/`ValuativeRel`.** `ValuativeExtension` (`ValuativeRel/Basic.lean:1292`) is
  **compatibility-only** (assumes `[ValuativeRel B]`, does not construct the `ValuativeRel` on `K̄`); no
  canonical `ValuativeRel (AlgebraicClosure K)`. So local-ness via "`integralClosure` is a `ValuationRing`"
  needs the full from-scratch unique-extension theory. **~3 passes, no D2.**
- **(ii) `spectralNorm` (+ tracked D2).** Two decisive finds Pass 16 missed: (a) `Valued.integer K̄` is a
  `ValuationRing` ⟹ `IsLocalRing` **for free** (`ValuationSubring`→`ValuationRing`→`IsLocalRing`;
  `Padics/Complex.lean` is the exact template — `spectralNorm.normedField`, `NormedField.toValued`,
  `Valued … ℝ≥0` on the *non-complete* `AlgebraicClosure`); (b) the bridge `spectralNorm x ≤ 1 ↔
  IsIntegral 𝒪[K] x` is **reachable** — `spectralNorm = spectralValue ∘ minpoly` (`SpectralNorm.lean:379`)
  + **`spectralValue_le_one_iff`** (`:202`, monic ⟹ `≤1 ↔ all coeffs norm ≤1`) + the algebraic half
  (coeffs ∈ `𝒪[K]` ↔ integral). So only the bridge is real work; local-ness is free. **~2 passes + a
  tracked D2.**

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| (iii) Henselian shortest (Mathlib has integral-closure-local) | absent (TFAE root-lifting only); + colimit absent | (iii) is ~2–3, not shortest |
| (ii) bridge `spectralNorm ≤ 1 ↔ integral` maybe absent (P16) | **reachable** via `spectralValue_le_one_iff` (P16 missed it) | (ii) shrank to ~2 |
| (ii) local-ness needs work | **free** — `Valued.integer` is a `ValuationRing` | (ii) shortest |
| (i) native ~3 | confirmed (`ValuativeExtension` constructs nothing) | (i) longest |

## The decision — route (ii), incur the tracked D2 (REVERSES Pass 16)

**Route (ii) is materially shortest** (~2 passes vs ~3 / ~2–3): local-ness free + bridge reachable. By
the **cost principle** — a tracked **D2** instance diamond is a *bounded, documented, fix-once* hygiene
debt (logged like D1), **cheaper than 2–3 passes of from-scratch valuation/Henselian theory** — incurring
D2 is the right trade. **This reverses Pass 16's "stay native, D2 not incurred"**, legitimately and on
**new evidence**: Pass 16 grepped only `spectralNorm.*le_one` (missing `spectralValue_le_one_iff`) and
had not found the free `Valued.integer` local-ness, so its magnitude estimate for (ii) was wrong. This is
a **magnitude** decision, the opposite of a D2-reflex (it *chooses* D2 because (ii) is genuinely shorter).
Note: local-ness genuinely cannot be finished without the spectral structure — an integral `x` is a unit
iff `minpoly`'s constant coeff is a unit, but "non-units form an ideal" (additive closure) needs the
multiplicative ultrametric `spectralNorm`; so the D2 is unavoidable, not gratuitous.

## Built — the bridge's algebraic half (D2-free, strictly-lower)

`Anabelian/GaloisIntegersLocal.lean`, standard axioms only (in-file `#print axioms`):
- `isIntegral_iff_minpoly_coeff_mem` — `IsIntegral 𝒪[K] x ↔ ∀ i, (minpoly K x).coeff i ∈ 𝒪[K]`, for
  `x : K̄`. Forward: `minpoly.isIntegrallyClosed_eq_field_fractions` (`𝒪[K]` integrally closed, `K = Frac
  𝒪[K]`, so `minpoly K x = (minpoly 𝒪[K] x).map`). Reverse: lift `minpoly K x` to a monic poly over `𝒪[K]`
  via `Polynomial.toSubring` (+ `monic_toSubring`, `aeval_map_algebraMap`, `map_toSubring`; the
  `algebraMap ↥𝒪[K] K = subtype` step is `rfl`). The **algebraic core** of route (ii)'s bridge
  `integralClosure 𝒪[K] K̄ = {x | spectralNorm x ≤ 1}`; the remaining (D2-incurring) half is `coeff ∈
  𝒪[K] ↔ ‖coeff‖ ≤ 1` chained through `spectralValue_le_one_iff`. **Norm-free ⟹ D2-free** — D2 is deferred
  to exactly the spectral step that needs the norm.

Inventory correction needed: `IsIntegrallyClosed ↥𝒪[K]` is **not** transitively imported by
`ResidueReductionIntegral` + minpoly/polynomial modules; it comes from
`Mathlib.RingTheory.Valuation.LocalSubring` (the `ValuationSubring → IsIntegrallyClosed` instance), which
this file imports. (Under `import Mathlib` the probe hid this.)

## What was built + HEADLINE status

`isIntegral_iff_minpoly_coeff_mem` (bridge algebraic half), axiom-free, strictly-lower, D2-free.
**HEADLINE: the axiom was NOT removed — `residueReduction_surjective` remains the single open `DEBT`.**
**Route-steps remaining: [3a via route (ii): (a) D2 setup ⟹ `IsLocalRing (Valued.integer K̄)`; (b) the
bridge `integralClosure = Valued.integer K̄` (algebraic half ✅ this pass); (c) transport ⟹ 3a; 3b residue
algebraic; 3d/3e supported; Step 4 apply keystone + delete axiom (perfect-case)].** Done: 1, 1b, 2a, 2b,
3c-modulo-3a, bridge algebraic half. **Nothing cardinal-sin posited** (3a being *built*; no `DEBT` posits
`𝒪[K̄]` local / a `ValuationRing` / the residue iso). **Recovers nothing from an abstract group.** No new
`structure`/`class` (no rule-2). **D1** N/A; **D2 decided to be incurred via route (ii)** (the reversal),
not yet incurred in code, logged.

## Ledger delta

- **0 / 0.** No new axiom; no reclassification. Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`** (open).
  Progress = the magnitude-based three-route decision (route ii, D2 to be incurred) + the bridge's
  D2-free algebraic-half brick.

## Scope: pointer to Pass 18

Pass 18: **3a's spectral steps (a)/(b) — the D2 incurral.** (a) Set up `NormedField K`/`RankOne` on the
local field (the `Padics/Complex` + `LocalField.Basic` `RankOne` pattern) ⟹ `spectralNorm.normedField K
K̄` ⟹ `Valued K̄ ℝ≥0` ⟹ `IsLocalRing (Valued.integer K̄)` (free). Track the D2 diamond: prove the spectral
`Valued`/`NormedField` on `K` agrees with the intrinsic `ValuativeRel` valuation (same valuation — the
agreement lemma is the fix-once hygiene step). (b) The norm half of the bridge: `‖y‖ ≤ 1 ↔ y ∈ 𝒪[K]`
(norm↔valuation) + `spectralValue_le_one_iff` chained to this pass's `isIntegral_iff_minpoly_coeff_mem`,
giving `integralClosure 𝒪[K] K̄ = Valued.integer K̄`. (c) Transport ⟹ `IsLocalRing (integralClosure 𝒪[K]
K̄)` = **3a**. With 3a: 3b (residue algebraic), 3d/3e (`IsAlgClosure` repackaging), then step 4 (apply
`stabilizerHom_surjective_of_profinite`, **delete the axiom** — perfect case; imperfect equal-char
tracked). Honest pointer: 3a is ~2 passes out (the D2 setup + bridge are the real work, both
de-risked by the `Padics/Complex` template + the reachable `spectralValue_le_one_iff`), the discharge ~3.

---

# Pass 18 — rung L1, route (a): brick 3a (`𝒪[K̄]` local) DONE + the D2 incursion (2026-05-30)

## Restatement (i)–(iv), pre-search

(i) D2 setup localized like D1: introduce `NormedField K`/`RankOne` via `letI` **inside the proof**, so
`spectralNorm` is reachable but `𝒪[K]`/`integralClosure 𝒪[K] K̄` keep elaborating via `ValuativeRel`
elsewhere (3a's statement is pure `ValuativeRel`, no leak). (ii) The bridge `spectralNorm x ≤ 1 ↔
IsIntegral 𝒪[K] x` over the **same** `ValuativeRel` `𝒪[K]`, via `spectralValue_le_one_iff` + Pass-17's
algebraic half + the norm↔valuation agreement. (iii) Expected 3a to land or be ≤2 passes out — it
**landed**. (iv) D2 localized-and-logged, no stub, discharge only at axiom-removal, re-confirm 2a/2b/3c.

## Route-first-step probes (real names) — the D2 setup

- **`Valued K` needs `[UniformSpace K] [IsUniformAddGroup K]`** (`LocalField/Basic.lean:104`), absent in
  my `[TopologicalSpace K]` context — but `Basic.lean:138-145` shows the localized fix: `letI :=
  IsTopologicalAddGroup.rightUniformSpace K; haveI := isUniformAddGroup_of_addCommGroup; letI :
  RankOne := {hom' := IsRankLeOne.nonempty.some.emb.comp …, strictMono' := …}`. Verified it elaborates.
- **`NormedField K`** via `Valued.toNontriviallyNormedField K (ValueGroupWithZero K)` (NormedValued.lean);
  `IsUltrametricDist K` then `inferInstance`. **`NormedField K̄`** via `spectralNorm.normedField K K̄`
  (the `Padics/Complex.lean` template — `PadicAlgCl = AlgebraicClosure ℚ_[p]` mirrors our `K̄`);
  `IsUltrametricDist K̄` via `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  (isNonarchimedean_spectralNorm …)`; **`Valued K̄ ℝ≥0`** via `NormedField.toValued`. Then **`IsLocalRing
  ↥(Valued.integer K̄)` is `inferInstance` — free** (`ValuationSubring → ValuationRing → IsLocalRing`).
- **The agreement** `‖a‖ ≤ 1 ↔ a ∈ 𝒪[K]`: `Valued.toNormedField.norm_le_one_iff` (`‖x‖ ≤ 1 ↔ Valued.v x
  ≤ 1`, NormedValued.lean:245) + `Valuation.mem_integer_iff` (`r ∈ v.integer ↔ v r ≤ 1`, `rfl`) + `Valued.v
  = ValuativeRel.valuation K` (`rfl`, ValuativeRel.lean:66). So `coeff ∈ 𝒪[K] ↔ Valued.v coeff ≤ 1` is
  **`Iff.rfl`** — the spectral norm's unit ball on `K` IS the `ValuativeRel` `𝒪[K]`, definitionally.

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| D2 setup via `Padics/Complex` template | works, but needs the `rightUniformSpace`+`RankOne` `letI` prefix (`[TopologicalSpace K]`, not `[UniformSpace K]`) | ✓ (localized as `letI`) |
| agreement `‖a‖ ≤ 1 ↔ a ∈ 𝒪[K]` a real lemma | **`Iff.rfl`** (`Valued.v = valuation K` + `mem_integer_iff` both `rfl`) | better — diamond reconcilable |
| `IsLocalRing (Valued.integer K̄)` free | free, but the instance search is **expensive** under `import Mathlib` + Anabelian instances (needs `maxHeartbeats` bump) | ✓ + a heartbeats note |
| 3a lands this pass | **landed** (`isLocalRing_galoisIntegers`, standard-axioms-only) | ✓ |

## Built — brick 3a (route (ii)), D2 localized

`Anabelian/GaloisIntegersLocal.lean`, standard axioms only (in-file `#print axioms`):
- `isLocalRing_galoisIntegers : IsLocalRing ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))`. Proof: the
  `letI` chain (above) sets up `Valued K̄`; `Valued.integer K̄` local for free; the **bridge** `hmem : x ∈
  integralClosure 𝒪[K] K̄ ↔ x ∈ Valued.integer K̄` (`change` to `IsIntegral`, then
  `isIntegral_iff_minpoly_coeff_mem` ↔ `∀ i, coeff ∈ 𝒪[K]`; the RHS `x ∈ Valued.integer K̄ ↔ Valued.v x
  ≤ 1 ↔ spectralNorm x ≤ 1 ↔ spectralValue (minpoly K x) ≤ 1 ↔ ∀ n, ‖coeff n‖ ≤ 1`, glued by the
  `Iff.rfl` agreement per coeff); then a hand-built `RingEquiv` (identity on values, all axioms `rfl`)
  and `RingEquiv.isLocalRing` transports local-ness back. With 3a, `𝔪[K̄]` is THE maximal ideal, so 3c
  (`galoisResidueField_isAlgClosed`) gives `𝓀̄` algebraically closed.

## D2 incursion — localized + logged (PRIMARY discipline)

First incursion of D2 (watched P13–17). Contained like D1:
- **Mechanism:** the spectral/normed/Valued setup is a `letI`/`haveI` chain **inside the proof**; the
  statement is pure `ValuativeRel`. So nothing leaks to other declarations.
- **Agreement band-aid:** `Iff.rfl` (no genuine clash — same valuation).
- **No global instance; `synthInstance.maxHeartbeats 400000` (commented)** for the one expensive search.
- **Re-typecheck confirmation (the discipline):** `lake build` clean (8493 jobs); 2a
  `galoisIntegers_algebraIsInvariant`, 2b `continuousSMul_galoisIntegers`, 3c
  `galoisResidueField_isAlgClosed` **all still `#print axioms` standard-only** — the D2 setup changed
  nothing in them. 3a too is standard-only.
- This file uses **`import Mathlib`** (sanctioned fallback, noted): 3a spans many spectral/valued/normed
  modules with uncertain paths/transitive instances. (Pass-17's `isIntegral_iff_minpoly_coeff_mem`
  compiles unchanged under it.)

## What was built + HEADLINE status

`isLocalRing_galoisIntegers` (brick 3a), axiom-free (standard only), D2 localized.
**HEADLINE: the axiom was NOT removed — `residueReduction_surjective` remains the single open `DEBT`.**
**Route-steps remaining: [3b residue algebraic; 3d/3e `≅ AlgebraicClosure 𝓀[K]` + `Aut` (supported);
Step 4 apply keystone + delete axiom (perfect-case)].** Done: 1, 1b, 2a, 2b, 3c, **3a (this pass)**.
**Nothing cardinal-sin posited** (3a proved, not stubbed). **Recovers nothing from an abstract group.**
No new `structure`/`class` (no rule-2). **D1** N/A; **D2 incurred, localized, logged** (hygiene, not a
logical axiom). Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`**.

## Ledger delta

- **0 / 0.** No new axiom; no reclassification. Progress = brick 3a (the last substantial gate) proved
  axiom-free + the D2 incursion contained.

## Scope: pointer to Pass 19

Pass 19: **steps 3b + 3d/3e (and possibly Step 4).** (3b) `𝓀̄ := 𝒪[K̄]/𝔪[K̄]` is algebraic over `𝓀[K]`
— each residue class lifts to an element integral over `𝒪[K]`, hence algebraic (moderate). (3d) with 3c
(`𝓀̄` alg-closed) + 3b (`𝓀̄/𝓀[K]` algebraic), `isAlgClosure_iff` gives `IsAlgClosure 𝓀[K] 𝓀̄`, and
`IsAlgClosure.equiv` gives `𝓀̄ ≅ AlgebraicClosure 𝓀[K]` (supported). (3e) transport `Aut(𝓀̄/𝓀[K]) ≅
Field.absoluteGaloisGroup 𝓀[K]`. Then **Step 4**: assemble the keystone hypotheses (all now in hand —
`MulSemiringAction`, `Algebra.IsInvariant`, `DiscreteTopology`/`ContinuousSMul`, `Q = 𝔪[K̄]` prime over
`𝔪[K]` with `stabilizer = ⊤` via local-ness, residue `B/Q ≅ 𝓀̄ ≅ AlgebraicClosure 𝓀[K]`), apply
`stabilizerHom_surjective_of_profinite`, reinterpret as `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)`, **delete the `axiom`**
for a `[PerfectField K]` `theorem`, and propagate `[PerfectField K]` to the downstream
`UnramifiedQuotient.lean` results (the narrowing) + record the imperfect equal-char remainder. 3a was the
last substantial gate; the discharge is now ~1–2 passes out.

---

# Pass 19 — rung L1, route (a): the residue identification (3b/3c/3d/3e), clean partial (2026-05-30)

## Restatement (i)–(iv), pre-search

(i) Bricks: 3b (`Algebra.IsAlgebraic 𝓀[K] 𝓀̄`), 3d (`𝓀̄ ≅ AlgebraicClosure 𝓀[K]`), 3e (`Aut ≅ Gal 𝓀[K]`),
connective (Q prime/LiesOver, `stabilizer = ⊤`, `A/P ≅ 𝓀[K]`). (ii) Aim for Step 4 (discharge) but stop
clean if it's too much. (iii) Discharge-moment checklist. (iv) Claim discharge only at axiom-removal.

## Inventory (real names) — what made the bricks work

- `𝓀[K] = IsLocalRing.ResidueField ↥𝒪[K]` (`Valued/ValuativeRel.lean:91`) = `𝒪[K] ⧸ 𝔪[K]` — matches the
  keystone's `A/P` exactly.
- **The connective keystone:** given `[IsLocalHom (algebraMap R S)]`, `ResidueField/Basic.lean:178-184`
  gives `(maximalIdeal S).LiesOver (maximalIdeal R)` **and** `Algebra (ResidueField R) (ResidueField S)`
  as **free instances**. So all connective tissue + the residue algebra reduce to proving `IsLocalHom
  (algebraMap 𝒪[K] 𝒪[K̄])`.
- `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` (`Ideal/GoingUp.lean:204`) + `eq_maximalIdeal`
  (local) ⟹ `(𝔪[K̄]).comap = 𝔪[K]` = `local_hom_TFAE` clause 4 ⟹ clause 0 = `IsLocalHom`.
- `IsAlgClosure.equiv` (`IsAlgClosed/Basic.lean:414`) needs `IsTorsionFree` (free over a field, but the
  search is slow — bumped `synthInstance.maxHeartbeats`). `IsAlgClosure 𝓀[K] 𝓀̄ := ⟨h3c, h3b⟩` directly
  (avoiding `isAlgClosure_iff`'s awkward arg binding).
- **3b can NOT use `Algebra.IsAlgebraic.tower_top`** — that needs a *field* base, but `𝒪[K]` is a DVR. So
  3b is element-wise: `mk b` with `b` integral (monic `q` over `𝒪[K]`); `q.map (algebraMap 𝒪[K] 𝓀[K])`
  is monic (≠0) and kills `mk b` (`aeval_map_algebraMap 𝓀[K]` + `aeval_algHom_apply` + `aeval_def` +
  the integrality witness).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| LiesOver/residue-algebra need separate work | **free** given `IsLocalHom` | ✓ (reduce to IsLocalHom) |
| 3b via `tower_top` | `tower_top` needs field base; `𝒪[K]` is a DVR → element-wise | corrected, built directly |
| Step 4 a big separate assembly | keystone **typechecks** on `G/B/A/P/Q`; only `ContinuousSMul` (Pass 2b) missing | discharge ~1 pass out |
| might reach the discharge | residue iso done; Step 4 = keystone + `stabilizer=⊤` + reinterpret | clean partial, stop |

## Built — the residue identification (`Anabelian/ResidueIso.lean`, standard axioms only)

- `galoisIntegers_isLocalHom` (instance) — `IsLocalHom (algebraMap 𝒪[K] 𝒪[K̄])` (the comap-maximal +
  TFAE chain). Unlocks `LiesOver` + `Algebra 𝓀[K] 𝓀̄`.
- `galoisResidueEquiv` (3b + 3d) — `ResidueField 𝒪[K̄] ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K]`.
- `galoisResidueAut` (3e) — `Aut(𝓀̄/𝓀[K]) ≃* Field.absoluteGaloisGroup 𝓀[K]` (`AlgEquiv.autCongr`).
All need **no `PerfectField`**; `isLocalRing_galoisIntegers` (3a) registered as `local instance` so the
statements elaborate.

## Step-4 distance (probed, for the honest pointer)

`stabilizerHom_surjective_of_profinite (𝔪[K]) (𝔪[K̄])` **typechecks** applied to `G = Gal(K̄/K)`,
`B = 𝒪[K̄]`, `A = 𝒪[K]` (with discrete `B`) — the *only* instance it can't auto-synth is `ContinuousSMul
G 𝒪[K̄]`, which **is** Pass-2b's `continuousSMul_galoisIntegers` (supply via `haveI`). So Step 4 is:
supply `ContinuousSMul` → keystone gives `stabilizer G 𝔪[K̄] ↠ (𝒪[K̄]/𝔪[K̄] ≃ₐ[𝒪[K]/𝔪[K]] 𝒪[K̄]/𝔪[K̄])`;
prove `stabilizer G 𝔪[K̄] = ⊤` (pointwise-ideal-maximality + local uniqueness); reinterpret the codomain
(`B/Q = 𝓀̄`, `A/P = 𝓀[K]`, defeq) via `galoisResidueAut` ⟹ `Gal K →* Gal 𝓀[K]` surjective; **delete the
axiom**. ~1 pass.

## What was built + HEADLINE status

The residue identification (3b/3c/3d/3e) + connective `IsLocalHom`/`LiesOver`, all standard-axioms-only.
**HEADLINE: the axiom was NOT removed — `residueReduction_surjective` remains the single open `DEBT`.**
This is a **clean partial**: Step 4 (keystone application + `stabilizer = ⊤` + reinterpretation + axiom
deletion) was **deliberately NOT half-assembled** — a half-built Step 4 is worse than a clean partial.
**Nothing cardinal-sin posited** (all bricks proved; surjection to be applied from the present keystone).
**Recovers nothing from an abstract group.** No new `structure`/`class` (no rule-2). **D1** N/A; **D2**
unchanged (3a's localized incursion); no further D2 this pass.

## Ledger delta

- **0 / 0.** No new axiom; no reclassification. Ledger unchanged at **`0 FOUNDATIONAL / 1 DEBT`** (open,
  now ~1 pass from discharge). Progress = the residue identification (the last substantial body of work).

## Scope: pointer to Pass 20

Pass 20: **the discharge.** Assemble Step 4 in `UnramifiedQuotient.lean` (or a new file feeding it):
(1) `letI : TopologicalSpace 𝒪[K̄] := ⊥`, `haveI : DiscreteTopology`, `haveI := continuousSMul_galoisIntegers
K`; (2) prove `MulAction.stabilizer (Gal K) 𝔪[K̄] = ⊤` (every `σ` maps the unique maximal ideal to a
maximal ideal = itself — `Ideal.pointwise_smul` + maximality-under-equiv + `eq_maximalIdeal`); (3)
`have := stabilizerHom_surjective_of_profinite 𝔪[K] 𝔪[K̄]` (typechecks); (4) compose `G ≃* ↥(stabilizer)`
(`stabilizer = ⊤` ⟹ `Subgroup.topEquiv`), the surjective `stabilizerHom`, and `galoisResidueAut`
(matching `B/Q = 𝓀̄`, `A/P = 𝓀[K]`) into `φ : Gal K →* Gal 𝓀[K]` surjective; (5) **delete `axiom
residueReduction_surjective`, replace with the `[PerfectField K]` theorem of the SAME statement**;
(6) **discharge-moment checklist**: `#print axioms` standard-only on the theorem AND
`unramifiedQuotient_iso`/`_procyclic` (propagate `[PerfectField K]` to them + their docstrings),
anti-circularity (keystone genuinely applied), ledger **1 DEBT → 0** with the tracked imperfect remainder.
The residue identification is done; this is the keystone application + bookkeeping.

---

# Pass 20 — rung L1: THE DISCHARGE. `residueReduction_surjective`: `DEBT → theorem` (2026-05-30)

## Restatement (i)–(iv), pre-search

(i) Step-4 pieces: `ContinuousSMul` plumbing (Pass 2b), `stabilizer = ⊤`, keystone application,
codomain via `galoisResidueAut` (+ transport if not defeq), domain via `stabilizer = ⊤`. (ii) Aim to
reach the deletion; stop clean if `stabilizer = ⊤` or the codomain transport balloons. (iii)
Discharge-moment checklist. (iv) Claim discharge only at axiom-removal; re-audit downstream.

## Route-first-step (keystone conclusion shape) + the identifications

- `#check @Ideal.Quotient.stabilizerHom`: `... ↥(MulAction.stabilizer G P) →* (B ⧸ P) ≃ₐ[A ⧸ p] B ⧸ P`
  (its `P` = our `Q = 𝔪[K̄]`, its `p` = our `P = 𝔪[K]`).
- **Codomain identification is DEFEQ, no transport needed:** `B ⧸ 𝔪[K̄] = IsLocalRing.ResidueField 𝒪[K̄]
  = 𝓀̄` and `A ⧸ 𝔪[K] = ResidueField 𝒪[K] = 𝓀[K]` (both `= R ⧸ maximalIdeal`, the `ResidueField` def);
  and **both algebra instances are `Ideal.Quotient.algebraOfLiesOver`** (the keystone's from `LiesOver`,
  `galoisResidueAut`'s from `IsLocalHom` ⟹ `LiesOver` ⟹ the `ResidueField.algebra` instance). So the
  keystone's codomain *is* `galoisResidueAut`'s domain `𝓀̄ ≃ₐ[𝓀[K]] 𝓀̄` — `.comp` works directly.
- `Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G`; `Ideal.pointwise_smul_eq_comap : a • S = S.comap
  (toRingAut _ _ a).symm`; **`comap_isMaximal_of_equiv` is an INSTANCE** (so `σ • 𝔪[K̄]` is maximal
  automatically); `IsLocalRing.eq_maximalIdeal`.

## The discharge assembly (`Anabelian/UnramifiedQuotient.lean`)

- `stabilizer G 𝔪[K̄] = ⊤`: `Subgroup.eq_top_iff'`; `intro σ`; `MulAction.mem_stabilizer_iff,
  Ideal.pointwise_smul_eq_comap`; `exact eq_maximalIdeal inferInstance` (the comap is maximal by the
  instance; `= 𝔪[K̄]` by local uniqueness).
- `hsurj := stabilizerHom_surjective_of_profinite (maximalIdeal 𝒪[K]) (maximalIdeal 𝒪[K̄])` — all
  hypotheses synthesize (`MulSemiringAction`, `Algebra.IsInvariant`, `DiscreteTopology` via `⊥` +
  `⟨rfl⟩`, `ContinuousSMul` via `continuousSMul_galoisIntegers K`, `G` profinite via `[PerfectField K]`,
  `Q.IsPrime`/`Q.LiesOver P` via `IsLocalHom`).
- `ι : Gal K →* ↥(stabilizer)`, `σ ↦ ⟨σ, by rw [hstab]; exact Subgroup.mem_top σ⟩`, surjective.
- `φ = (galoisResidueAut K).toMonoidHom.comp (stabilizerHom.comp ι)`; surjective via
  `(galoisResidueAut K).surjective.comp (hsurj.comp hι)` (after `simp only [MonoidHom.coe_comp,
  MulEquiv.coe_toMonoidHom]`).
- **`axiom` DELETED; `theorem residueReduction_surjective [PerfectField K] : <same statement> := by …`**.

Verified standalone (`discharge_test` probe): `depends on axioms: [propext, Classical.choice,
Quot.sound]` — no `residueReduction_surjective`, no `sorryAx`, no hidden axiom (anti-circularity).

## Discharge-moment checklist (all five run)

1. **Statement preserved:** `∃ φ : Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup 𝓀[K],
   Function.Surjective φ` + `[PerfectField K]` — identical existence claim.
2. **`#print axioms` standard-only, theorem + downstream:** `residueReduction_surjective`,
   `unramifiedQuotient_iso`, `residue_procyclic`, `unramifiedQuotient_procyclic` all `[propext,
   Classical.choice, Quot.sound]`. `grep ^axiom` project-wide: **ZERO**. No new axiom replaced it.
3. **Anti-circularity:** the proof *applies* the keystone to the axiom-free bricks (standalone audit
   standard-only) — not a re-posit, not circular, no hidden `sorry`/axiom.
4. **Narrowing propagation:** `[PerfectField K]` added to `unramifiedQuotient_iso`/`_procyclic`;
   `residue_procyclic` left independent (not over-constrained); docstrings updated; imperfect case
   tracked in `ROADMAP.md`.
5. **Ledger `1 DEBT → 0`:** `0 FOUNDATIONAL / 0 DEBT`.

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| codomain `B/Q ≃ₐ[A/P]` may need an `AlgEquiv` transport to `𝓀̄ ≃ₐ[𝓀[K]] 𝓀̄` | **defeq** (`ResidueField` def + `algebraOfLiesOver` both ways) — `.comp` direct | ✓ no transport |
| `stabilizer = ⊤` fiddly (pointwise-ideal maximality) | `comap_isMaximal_of_equiv` is an instance ⟹ 4-line proof | ✓ easy |
| keystone instances need work | all synthesize once `ContinuousSMul` (2b) is supplied | ✓ |
| might stop clean before Step 4 | **reached the deletion** — full discharge | ✓ DISCHARGED |

## Build + headline

`lake build`: **8494 jobs, clean** (no errors, no warnings, no `sorry`). **HEADLINE: the project's first
`DEBT` is DISCHARGED into a proved `theorem`. Ledger `0 FOUNDATIONAL / 0 DEBT`; zero `axiom`
declarations project-wide.** Imports: `UnramifiedQuotient` now imports the residue chain
(`ResidueIso`/`ResidueReductionInvariant`/`ResidueReductionContinuity`); no cycle (none of those import
`UnramifiedQuotient`). D1 N/A; **D2** unchanged (3a's localized incursion only; Step 4 adds none). No
new `structure`/`class` (no rule-2). **Recovers nothing from an abstract group** — a map between the
Galois groups of *given* fields `K`, `𝓀[K]`; R1–R3 untouched.

## Ledger delta

- **`DEBT` −1 (discharged into a theorem); `FOUNDATIONAL` 0.** `0 FOUNDATIONAL / 1 DEBT` →
  **`0 FOUNDATIONAL / 0 DEBT`**.

## Scope: pointer to Pass 21

The residue surjection is discharged; L1's `DEBT` is gone. Pass 21 — the post-discharge L1 work, two
natural options: (a) **tie `N` (the residue-reduction kernel) to Pass 4's `inertiaSubgroup`** — Pass 5
logged this as blocked on the absent `K̄`-valuation, which is now in hand (`𝒪[K̄]` local, the spectral
valuation), so the identification `N = inertiaSubgroup` is reachable; or (b) **open L2** — the
unramified ⟶ tame ⟶ wild ramification filtration `G_i` of `Gal(K̄/K)`, defined via the now-available
`K̄`-valuation (the Pass-11 common-prerequisite finding: the same `𝒪[K̄]`/valuation infrastructure
gates L2). Also outstanding (not blocking): the **imperfect equal-char generality** of the residue
surjection (the tracked remainder, via `Aut(K̄/K) ≅ Gal(K^sep/K)`). The honest frame stays: R1–R3
remain distant; L1 is essentially complete (its one boundary earned, not posited).

---

# Pass 21 — rung L1, post-discharge: the named residue reduction + `ker = inertia` (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) The Pass-20 pointer's two options: (a) tie `N` to the inertia subgroup; (b) open L2. (ii) Choose
(a): the Pass-20 discharge is an *existential* (`∃ φ, Surjective φ`) with the concrete map buried in
the proof — until it is a named `def` with an identified kernel, L2's filtration has no anchor
(`G_0` *is* inertia), so (a) gates (b). (iii) Deliverables: the named map, its surjectivity, the
kernel characterization as the pointwise residue stabilizer; stop clean if the kernel identification
balloons. (iv) Claim only what is proved; `[PerfectField K]` only where surjectivity is consumed.

## Environment note (this pass ran on a fresh machine)

No Lean toolchain was present: installed `elan` (4.2.3), toolchain `v4.30.0` auto-pinned from
`lean-toolchain`, `lake exe cache get` (8459 files), baseline `lake build` clean (8494 jobs,
all Pass-20 audits standard-only) before any work.

## Route-first-step (probe) + the inventory find of the pass

- **`Ideal.inertia` is PRESENT** (`Mathlib/RingTheory/Ideal/Defs.lean`):
  `Ideal.inertia G I : Subgroup G = {σ | ∀ x, σ • x - x ∈ I}` (via `AddSubgroup.inertia`, with
  `AddSubgroup.mem_inertia : … ↔ ∀ x, σ • x - x ∈ I` a simp `.rfl`) — Mathlib's general inertia
  subgroup for a group acting on a ring, exactly the classical pointwise condition.
- **`Ideal.Quotient.ker_stabilizerHom` is PRESENT** (`Mathlib/RingTheory/Ideal/Over.lean`):
  `(stabilizerHom P p G).ker = (P.inertia G).subgroupOf (stabilizer G P)` — the kernel lemma we
  would otherwise have proved by hand. (Also `map_ker_stabilizer_subtype`, `inertia_le_stabilizer`,
  `stabilizerHom_apply` simp.) So the pass *applies* Mathlib's kernel identification; nothing reproved.
- Full draft probed via `lake env lean` (throwaway): all declarations compiled standard-axioms-only
  after three fixes (below).

## What was built (`Anabelian/GaloisInertia.lean`, all standard-axioms-only)

- `galoisIntegers_stabilizer_eq_top` — decomposition = ⊤ (extracted from the Pass-20 proof as a
  named lemma; no `PerfectField`).
- `galoisToStabilizer` (+ `_surjective`) — `Gal K →* ↥(stabilizer 𝔪[K̄])`, the bundled inclusion.
- `residueReductionHom : Gal K →* Gal 𝓀[K]` — **THE residue reduction, named** =
  `galoisResidueAut ∘ stabilizerHom ∘ galoisToStabilizer`. **No `PerfectField`** (the map exists
  unconditionally; only surjectivity needs profiniteness).
- `residueReductionHom_surjective [PerfectField K]` — the Pass-20 keystone assembly, restated for
  the named map. `residueReduction_surjective` (`UnramifiedQuotient.lean`) refactored to the
  one-line corollary `⟨residueReductionHom K, residueReductionHom_surjective K⟩` (statement
  verbatim; heavy proof + its heartbeat options removed from that file).
- `galoisInertia : Subgroup (Field.absoluteGaloisGroup K)` — the inertia subgroup, named:
  `(𝔪[K̄]).inertia Gal(K̄/K)` (+ `mem_galoisInertia_iff`, the unfolded pointwise form — the concrete
  realization of Pass 4's abstract `mem_inertiaSubgroup_iff`).
- **`ker_residueReductionHom : (residueReductionHom K).ker = galoisInertia K`** — the headline.
  `galoisResidueAut` injective + `ker_stabilizerHom` + `stabilizer = ⊤` collapsing `subgroupOf`.
  **Unconditional.**
- `galoisInertia_normal` — inertia normal in the full group (it is a kernel). Unconditional.
- `unramifiedQuotientEquiv [PerfectField K] : Gal K ⧸ galoisInertia K ≃* Gal 𝓀[K]` — the classical
  unramified-quotient theorem in standard form (upgrades the existential `unramifiedQuotient_iso`).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| kernel characterization proved by hand (mk-surjectivity + quotient eq) | **`Ideal.Quotient.ker_stabilizerHom` is in Mathlib** — applied, not reproved | ✓ cheaper |
| inertia stated ad-hoc as a set-with-condition | **`Ideal.inertia` is in Mathlib** — the canonical form | ✓ better |
| the equiv `G⧸I ≃* Gal 𝓀` routine | **instance-path trap**: `AlgEquiv.aut` vs the `deriving Group` instance on `absoluteGaloisGroup` are defeq but not syntactically equal — `Subgroup.Normal` synthesis fails across the mismatch (motive-not-type-correct under `rw`) | fixed by **typing `galoisInertia` as `Subgroup (Field.absoluteGaloisGroup K)`** so every statement lives over one instance path |
| `mem`-lemma for `σ : absoluteGaloisGroup K` | `HSMul` synthesis won't unfold the `absoluteGaloisGroup` def (instances are reducible-only) | stated for `σ` in the `AlgEquiv` form (defeq) |

## Build + headline

`lake build`: **8495 jobs, clean** (no errors, warnings, or `sorry`); all 14 rebuilt-file audits
standard-only; project-wide `axiom`-declaration grep: **zero**. **HEADLINE: the Pass-5 sub-target
"tie `N` to the inertia subgroup" is CLOSED — `ker(residueReductionHom) = galoisInertia`,
unconditionally, and the unramified quotient now reads `Gal(K̄/K) ⧸ I ≃* Gal(𝓀̄/𝓀)` with `I` the
named inertia subgroup.** Honesty: connective packaging of Passes 11–20's hard content + Mathlib's
kernel lemma — not a new hard theorem; its value is that downstream work can now *refer* to the
reduction and to inertia. The literal `ValuationSubring.inertiaSubgroup` translation deliberately
not pursued (statement-level D2); continuity of the reduction logged as remaining refinement.
D1 N/A; **D2 unchanged** (no valuation on `K̄` in any statement). No new `structure`/`class`
(no rule-2); no new owed witness (`[PerfectField K]` = the tracked owed generality, not a
load-bearing claim). Recovers nothing from an abstract group; R1–R3 untouched.

## Ledger delta

- **0 / 0.** No axiom touched; ledger stays **`0 FOUNDATIONAL / 0 DEBT`**. Progress = the named
  map + the unconditional kernel identification (the Pass-5 remaining-work item, closed).

## Scope: pointer to Pass 22

With `galoisInertia` named, **L2 is unblocked at its anchor**: the ramification filtration in lower
numbering — `G_0 = galoisInertia K`, `G_i = {σ | ∀ b ∈ 𝒪[K̄], σ b − b ∈ 𝔪[K̄]^(i+1)}` (i.e.
`Ideal.inertia` applied to `𝔪[K̄]^(i+1)` — the SAME Mathlib device, so the definition costs little;
the *theorems* — `G_i` normal in `G_0`, the quotients' structure, eventually Herbrand/upper
numbering — are the real L2 body). Alternatives: the imperfect equal-char generality (the tracked
remainder, via `Aut(K̄/K) ≅ Gal(K^sep/K)`), or continuity of `residueReductionHom`. Honest frame
unchanged: R1–R3 distant; L1 essentially complete with its boundary earned, its map named, and its
kernel identified.

---

# Pass 22 — L2 opening verdict: naive lower numbering is DEGENERATE (proved) + the `Ẑ` payoff (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) The approved plan: open L2 by defining `G_i := (𝔪[K̄]^(i+1)).inertia Gal(K̄/K)` and proving
`G_0 = galoisInertia`, antitonicity, normality. (ii) Red flag raised before writing a line: `K̄` is
algebraically closed, so its value group is divisible — `𝔪[K̄]` should be **idempotent**, making the
filtration collapse. Verify FIRST; if confirmed, the refutation IS the pass (a vacuous definition
whose "theorems" all hold trivially is the exact iutt failure mode, and rule-2's come-apart test
would fail for every pair `i ≠ j`). (iii) If degenerate: prove it axiom-free, record the corrected
architecture, and bank the available real payoff (`≃ Ẑ`). (iv) Do NOT define the degenerate `G_i`.

## The verdict (confirmed): the planned opening was mathematically vacuous

`𝔪[K̄]² = 𝔪[K̄]`: for `x ∈ 𝔪[K̄]`, `K̄` gives `y` with `y² = x` (`IsAlgClosed.exists_pow_nat_eq`);
`y` is integral over `𝒪[K̄]` (monic `T² − x`, `Polynomial.monic_X_pow_sub_C`) hence over `𝒪[K]`
(`isIntegral_trans` + `integralClosure.AlgebraIsIntegral`) hence in `𝒪[K̄]`; `y` is a non-unit
(else `x = y²` is a unit, contra `x ∈ 𝔪` = nonunits, local), so `y ∈ 𝔪[K̄]` and `x = y·y ∈ 𝔪²`.
Then `𝔪^n = 𝔪` (`n ≠ 0`, induction) and `(𝔪^(i+1)).inertia G = galoisInertia K` for EVERY `i`
(`inertia_maximalIdeal_pow_collapse`) — the would-be `G_i` never come apart.

**This corrects the Pass-21 scope-pointer (and the pre-pass plan presented to the user), which had
recommended exactly this definition.** The discipline's value is that the refutation was *proved
before the definition was committed* — preemptive rule-2, a constructed failure as deliverable, in
the tradition of the Pass-13 fit-verdict and Pass-16/17 route reversals.

## What was built (all standard-axioms-only)

- `Anabelian/RamificationDegeneracy.lean`: `maximalIdeal_galoisIntegers_sq` (`𝔪[K̄]² = 𝔪[K̄]`),
  `maximalIdeal_galoisIntegers_pow_eq` (`𝔪^n = 𝔪`, `n ≠ 0`),
  `inertia_maximalIdeal_pow_collapse` (the collapse `G_i = G_0` ∀ `i`). Side consequences noted:
  `𝒪[K̄]` non-Noetherian, no uniformizer — DVR-style arguments must stay at finite level.
- `Anabelian/UnramifiedQuotient.lean` (+import `FiniteFieldZHatIso`): **`unramifiedQuotientZHat
  [PerfectField K] : Gal(K̄/K) ⧸ galoisInertia K ≃* Ẑ`** — the quantitative unramified-quotient
  theorem, assembling Pass 21's `unramifiedQuotientEquiv` with Pass 10's
  `galoisContinuousMulEquivZHat` at the finite residue field `𝓀[K]` (`Fintype` via
  `Fintype.ofFinite`). Two project wholes, one theorem. Universe note: `K : Type` (the Pass 6–10
  `Ẑ` development is `ProfiniteGrp`-packaged at universe 0 — an artifact, documented); group form
  only (topological form awaits the continuity refinement).
- **Corrected L2 architecture** (`ROADMAP.md`, L2 now IN-PROGRESS/architecture-fixed): (1)
  finite-level `G_i(L/K)` over a DVR + basic theory (tame `G_0/G_1 ↪ 𝓀_L^×`, wild `G_1` pro-`p`);
  (2) Herbrand `φ`/`ψ` + upper numbering; (3) the limit `G^v ≤ Gal(K̄/K)` (upper numbering is what
  survives limits — the degeneracy is lower numbering's failure to); (4) Hasse–Arf. Gaps re-verified:
  `RamificationGroup.lean` still definition-only; Herbrand ABSENT; finite-extension
  `IsNonarchimedeanLocalField` instances ABSENT (`NumberTheory/LocalField/Basic.lean` is the only
  file there).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| define `G_i` on `Gal(K̄/K)`, prove antitone/normal | **degenerate** — `𝔪[K̄]` idempotent, all `G_i = G_0`; proved, not asserted | ✗ plan refuted — refutation banked instead |
| degeneracy proof might need value-group machinery | pure ring theory: square roots + integrality + locality (~25 lines) | ✓ cheaper |
| `≃ Ẑ` payoff a one-liner | needed `Fintype 𝓀[K]` (`ofFinite`) + a universe restriction to `Type` (`ProfiniteGrp` packaging) | ✓ minor friction |

## Build + headline

`lake build`: **8496 jobs, clean**; all audits standard-only; zero `axiom` declarations project-wide.
**HEADLINE: the naive absolute-group lower-numbering filtration is PROVED degenerate (the L2
architecture is now fixed on the classical finite-level/upper-numbering ladder), and the unramified
quotient is now quantitatively `Ẑ`** (`Gal(K̄/K) ⧸ I ≃* Ẑ`, Passes 10+21 assembled). D1 N/A; **D2
unchanged**. No new `structure`/`class`; no new owed witness. Recovers nothing from an abstract
group; R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. Progress = a proved refutation that re-routed L2 before any vacuous
  definition landed, + one real assembled theorem (`≃ Ẑ`).

## Scope: pointer to Pass 23

**Open L2 at the finite level.** First job is the prerequisite inventory + bricks: (a) does Mathlib
make a finite extension `L/K` of a nonarch local field a nonarch local field (instances ABSENT in
`LocalField/Basic.lean` — check wider: `Valued`/`DiscreteValuationRing` routes)? (b) the
`Gal(L/K)`-action bricks on `𝒪_L = integralClosure 𝒪[K] L` (finite-level analogues of P11–14:
invariance, fixed ring, local-ness — much should specialize from the existing machinery); (c) then
`G_i(L/K) := (𝔪_L^(i+1)).inertia Gal(L/K)` with the REAL (non-vacuous, DVR) basic theory: `G_0` =
inertia, strictly-eventually-trivial (`G_i = 1` for `i` large — the DVR separation that `K̄` lacks),
antitone, normal in the decomposition group. Alternates: continuity of `residueReductionHom`
(upgrades `unramifiedQuotientZHat` to `≃ₜ*`), or the imperfect equal-char generality. Honest frame:
R1–R3 distant; L1 done in substance; L2 now starts on a sound foundation.

---

# Pass 23 — rung L2 OPENED: lower-numbering ramification filtration + basic theory (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Open L2 per the corrected architecture: the filtration where `𝔪`-powers separate. (ii) Choice of
setting: Mathlib's own `ValuationSubring` ramification setting (Pass 4's) — it has the
decomposition-group `MulSemiringAction` on `A` ready-made, and its file carries the literal
`TODO: Define higher ramification groups in lower numbering`; the abstract form subsumes the
finite-level `𝒪_L` case (Noetherian ⟹ Krull) without waiting on the absent finite-extension
local-field instances. (iii) Deliverables: `G_i` + mem-iff + antitone + `G_0 = inertiaSubgroup` +
normality + separation (hypothesis-explicit) + Noetherian discharge; cut eventual-triviality-for-
finite if fiddly. (iv) State the Krull hypothesis explicitly (Pass-22 lesson); make no
irremovability claim (no rule-2 obligation incurred).

## Inventory finds (route-first-step probe)

- `RamificationGroup.lean` (54 lines): `decompositionSubgroup` = stabilizer of `A` in `L ≃ₐ[K] L`;
  **`decompositionSubgroupMulSemiringAction : MulSemiringAction (decompositionSubgroup K A) A`**
  (instance, ready-made); `inertiaSubgroup` = ker of the residue action. The TODO is verbatim.
- `IsLocalRing.ResidueField.residue_smul : residue R (g • r) = g • residue R r` — `@[simp]`, `rfl`;
  the bridge lemma for `G_0 = inertiaSubgroup`.
- **`Ideal.iInf_pow_eq_bot_of_isLocalRing`** (`RingTheory/Filtration.lean`) — Krull intersection for
  Noetherian local rings: discharges the separation hypothesis in the Noetherian case.
- `Ideal.map_isMaximal_of_equiv` (instance) + `IsLocalRing.eq_maximalIdeal` + `Ideal.map_pow` — the
  crux `smul_mem_maximalIdeal_pow` assembles from these.
- `IsNonarchimedeanLocalField`: still exactly one Mathlib file, no finite-extension instances
  (re-verified) — the local-field instantiation `A = 𝒪_L` stays blocked, logged.

## What was built (`Anabelian/RamificationFiltration.lean`, all standard-axioms-only)

`ramificationGroup K A i := (𝔪_A^(i+1)).inertia (decompositionSubgroup K A)` (ℕ-indexed, `G_0` =
inertia, Serre's `G_{−1}` = ambient decomposition group), with: `mem_ramificationGroup_iff`;
`smul_mem_maximalIdeal_pow` (crux: the action preserves `𝔪_A^n`); `ramificationGroup_antitone`;
**`ramificationGroup_zero : G_0 = A.inertiaSubgroup K`** (ties to Pass 4's `mem_inertiaSubgroup_iff`
via `residue_smul`; the residue/`Quotient.mk` defeq handled by a term-mode bridge `hres`, since `rw`
needs syntactic match); **`ramificationGroup_normal`** (Serre IV §1 Prop. 1 — conjugation transports
the inertia condition along the crux); **`iInf_ramificationGroup_eq_bot`** (separation under explicit
`⨅ 𝔪_A^n = ⊥`; fixing `A` pointwise ⟹ fixing `L` via `mem_or_inv_mem` + `map_inv₀`);
`iInf_ramificationGroup_eq_bot_of_isNoetherianRing` (Krull discharge — field-or-DVR = the finite
level); `exists_notMem_ramificationGroup` (per-element escape).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| need to build the decomposition action on `A` | Mathlib instance `decompositionSubgroupMulSemiringAction` ready-made | ✓ free |
| `G_0 = inertiaSubgroup` may need a new residue-action apply lemma | `residue_smul` present, `@[simp]`/`rfl`; only friction was `residue` vs `Quotient.mk` syntactic mismatch (term-mode bridge) | ✓ |
| Krull intersection might be absent for valuation rings | `Ideal.iInf_pow_eq_bot_of_isLocalRing` present (Noetherian local) — exactly the needed discharge | ✓ |
| eventual triviality `∃ i, G_i = ⊥` for finite groups this pass | cut (antitone-chain-in-finite-group epsilon); per-element escape proved instead; logged | – honest cut |

## Build + headline

`lake build`: **8497 jobs, clean**; all audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: L2 is OPEN — the lower-numbering ramification filtration is defined (the
Mathlib-TODO object) with its basic theory proved: `G_0` = inertia, antitone, normal in the
decomposition group, and separating exactly where it should (Krull/DVR regime), in proved contrast
to the Pass-22 collapse.** No claim of hypothesis-irremovability (none needed; none dodged). D1 N/A;
**D2 N/A** (`ValuationSubring`-native). No new `structure`/`class`; no new owed witness. Recovers
nothing from an abstract group; R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. L2's first real content: the filtration + five basic theorems.

## Scope: pointer to Pass 24

L2 continuation, three candidate jobs in rough leverage order: (a) **the tame-quotient embedding**
`G_0/G_1 ↪ 𝓀^×` (`σ ↦ σ(π)/π mod 𝔪` for a uniformizer `π` — needs the DVR uniformizer API, present
in Mathlib for DVRs; the first structurally-rich L2 theorem, gateway to `G_0/G_1` cyclic + wild
`G_1` pro-`p`); (b) **the concrete properly-decreasing chain** — `G_0 ≠ G_1` for an explicitly
ramified extension (the come-apart exhibit; needs a concrete `ValuationSubring` with computable
Galois action — possibly `ℤ_p[√p]`-style or a Laurent-series toy); (c) **eventual triviality** for
finite decomposition groups (antitone chain in a finite group stabilizes at `⨅ = ⊥`). The
local-field instantiation (`A = 𝒪_L`, finite `L/K`) stays blocked on the absent
`IsNonarchimedeanLocalField`-finite-extension instances (gap logged; building them is itself a
candidate pass). Honest frame: R1–R3 distant; L1 done in substance; L2 now has its first rung built.

---

# Pass 24 — rung L2: the tame character `θ₀ : G₀ →* 𝓀ˣ` (hom + kernel half) + eventual triviality (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Per the Pass-23 pointer and the user-approved plan: the tame character, scoped UP FRONT to the
homomorphism + kernel half (`θ₀ : G_0 →* 𝓀ˣ`, `G_1 ≤ ker`, induced `G_0/G_1 →* 𝓀ˣ`), with the
eventual-triviality warm-up bundled. (ii) Injectivity (the full Serre IV §2 Prop. 7 embedding) is
declared OUT of scope before starting: it needs `σ ∈ G_i` detectable on `π` alone, i.e. the
monogenicity of the totally-ramified subextension (Serre IV §1 Prop. 5, from
completeness/Eisenstein) — absent at the bare-`ValuationSubring` level. The Pass-22 lesson applied
prospectively: under-promise. (iii) Setting: a uniformizer hypothesis `𝔪_A = (π)`, `π ≠ 0`
(weaker than DVR; DVR is the entry point). (iv) Stretch: uniformizer-independence (θ canonical).

## What was built (all standard-axioms-only)

`Anabelian/TameCharacter.lean`:
- `smulUnit` — decomposition elements act on units (the generic `MulDistribMulAction` units
  instance does NOT synthesize for this action — constructed directly, 4 lines).
- `exists_smul_uniformizer_eq`/`tameUnit`/`_spec`/`_unique` — `σπ = π·u_σ`, `u_σ` a unique unit:
  `σ` preserves `(π)` both ways (Pass-23's `smul_mem_maximalIdeal_pow`) ⟹ `π ∣ σπ ∣ π` ⟹
  `associated_of_dvd_dvd`; uniqueness by `mul_left_cancel₀`.
- `residue_smul_eq_of_mem_ramificationGroup_zero` — inertia fixes residues (the `G_0` condition
  mod `𝔪`).
- **`tameCharacter : ↥(G_0) →* (ResidueField ↥A)ˣ`** — multiplicativity is the pass's heart: the
  cocycle `(στ)π = π·u_σ·σ(u_τ)` is only a crossed homomorphism in general and straightens
  BECAUSE `σ ∈ G_0` fixes residues. (This is the mathematical content of "θ₀ lives on inertia".)
- **`tameCharacter_eq_one`** — `G_1 ≤ ker`: `σπ − π = π(u_σ − 1) ∈ (π²)`, cancel `π`,
  `u_σ ≡ 1 mod 𝔪`.
- **`tameQuotientHom : G_0 ⧸ (G_1.subgroupOf G_0) →* 𝓀ˣ`** — `QuotientGroup.lift` (normality:
  Pass 23's instance + `Subgroup.normal_subgroupOf`).
- **`tameCharacter_eq_of_span_eq`** — uniformizer-independence: `π' = πw` ⟹ `u'_σ =
  w⁻¹·u_σ·σ(w)`, and inertia fixes `res w` ⟹ same character. **θ₀ is canonical.**
- `tameCharacterOfIrreducible` — the DVR entry point (`irreducible_iff_uniformizer`).

`RamificationFiltration.lean` (appended): **`exists_ramificationGroup_eq_bot`** — finite
decomposition group + separation ⟹ `∃ i, G_i = ⊥` (closes the Pass-23 epsilon).

### Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| units-action instance available for `σ • u` | `MulDistribMulAction (decomposition) (↥A)ˣ` does NOT synthesize | constructed `smulUnit` by hand (4 lines) |
| eventual triviality a 15-line `Finset.sup` argument | `Fintype`/`Finset.univ.sup` route hit a `whnf` TIMEOUT (800k heartbeats); root cause isolated by bisection: an un-annotated anonymous constructor in a one-liner `exact` | restructured via `Set.finite_range.bddAbove` + type-annotated constructor — compiles at default heartbeats |
| independence a stretch goal, might drop | went through (the same inertia-fixes-residues lemma does the work) | ✓ included — θ₀ canonical |
| `residue` vs `Quotient.mk` syntactic friction (Pass-23 déjà vu) | hit again in two proofs | same term-mode-bridge fix |

## Build + headline

`lake build`: **8498 jobs, clean**; all audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: the tame character exists as an honest, canonical homomorphism
`θ₀ : G_0 →* 𝓀ˣ` killing `G_1` — the first map OUT of the ramification filtration — and finite
decomposition groups have eventually-trivial filtration.** Injectivity (⟹ `G_0/G_1`
abelian/cyclic) deliberately not claimed: it is the named next rung, needing the monogenicity
input. No new `structure`/`class`; no new owed witness; D1 N/A; **D2 N/A**. Recovers nothing from
an abstract group; R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. L2 gains its first quotient-structure map + the eventual-triviality
  closure.

## Scope: pointer to Pass 25

Three L2 candidates, leverage order: (a) **the concrete properly-decreasing chain** — `G_0 ≠ G_1`
for an explicitly ramified extension (the come-apart exhibit; spelunking-heavy: needs an explicit
`ValuationSubring` of a quadratic extension with computable action — `Zsqrtd`/`GaussianInt`
adjacent); (b) **injectivity of the tame map** — needs the monogenicity bridge (`v(σπ − π) ≥ i+1
⟹ σ ∈ G_i` when `𝒪_L = 𝒪_{L_0}[π]`) — could be stated WITH a monogenicity hypothesis at the
abstract level (honest, hypothesis-parametrized, like Pass 23's Krull) and discharged later at
the local-field level; (c) **the finite-extension local-field instances** (the known ~3-pass
infrastructure subproject; unlocks genuine `𝒪_L` instantiation of everything above). Also still
open: continuity of `residueReductionHom` (L1 polish); the imperfect-case generality. Honest
frame: R1–R3 distant; L2 advancing rung by rung on sound foundations.

---

# Incident note (2026-06-10, pre-Pass 25) — orphaned uncommitted session discovered and discarded

A pre-Pass-25 repo review found **12 untracked Lean files (~1,710 lines), mtimes 2026-05-31
13:02–18:44**, from a session that was never committed and never entered the governance files:
`RamificationInjection/Monogenic/Tame`, `HerbrandFunction/Monotone/Inverse/Averaging/Kernel`,
`UpperNumbering`, `RamificationTower/Function/Index`. Internally they numbered themselves "passes
24–35" and covered: the additive injection `G_i/G_{i+1} ↪ 𝓀⁺` (`i ≥ 1`), the monogenicity
reduction (Serre IV §1 Prop 5, hypothesis-parametrized), the tame injection `G_0/G_1 ↪ 𝓀ˣ`
(including the injectivity the committed Pass 24 deliberately deferred), Herbrand `φ`/`ψ` as an
`OrderIso` on `[0,∞)`, upper numbering with `G^{φ(u)} = G_u`, the tower/restriction maps, the
ramification function `i_G`, and a from-scratch relative ramification index.

**Why they were unusable as-is:** all 12 were written against a lost 2026-05-31 version of
`RamificationFiltration.lean` whose API (`lowerRamificationGroup`, `_iff`, `_antitone`, `_normal`)
exists nowhere in the surviving tree — the reflog shows this machine sat at `pass 20`, then a
`reset --hard` + fast-forward `pull` to `pass 24` (2026-06-10) destroyed the May-31 session's
tracked-file changes (its filtration file and its NOTES/ledger updates), leaving only the 12
non-colliding orphans. They do not elaborate against HEAD; their in-file "standard axioms only"
audit blocks are therefore unverifiable claims, not evidence. They also reference an owed witness
"W2" that the committed ledger has never contained, and the committed Passes 23–24 (run on a fresh
machine, unaware of them) re-derived part of the same territory under different names with
narrower, honestly-scoped claims.

**Decision (user, 2026-06-10): discard, proceed clean.** The 12 files were deleted (they exist in
no commit; genuinely gone). Cost accepted: the tame-injectivity route and the Herbrand `OrderIso`
bookkeeping are feasibility-proven but must be re-derived against the committed
`ramificationGroup` API. Nothing from the orphans is cited as evidence anywhere; any future pass
covering this territory starts from Serre and the committed Pass-23/24 files.

**Process fix (added to `CLAUDE.md`, Repository conventions):** commit + push every pass; `git
status` clean-tree check at every session start; uncommitted work does not exist as far as the
governance files are concerned. Root cause was 13 passes run without a single commit, then a
cross-machine divergence the spine files could not see.

---

# Pass 25 — rung L2: tame injectivity `G₀/G₁ ↪ 𝓀ˣ` under explicit monogenicity (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Per the Pass-24 pointer, candidate (b), user-approved: injectivity of the tame map, stated
WITH a monogenicity hypothesis at the abstract `ValuationSubring` level (the honest,
hypothesis-parametrized shape — Pass 23's Krull precedent) and discharged later at the
local-field level. (ii) Scope up front: detection lemma (Serre IV §1 Prop. 5) + `ker θ₀ = G₁` +
injectivity of Pass 24's `tameQuotientHom`; stretch: `G₀/G₁` abelian / cyclic-when-finite.
(iii) NOT in scope: discharging monogenicity (needs the finite-extension local-field instances);
the `i ≥ 1` additive injections. (iv) Hypothesis form: instance-free — `A₀ : Subring ↥A`
inertia-fixed, `Subring.closure (↑A₀ ∪ {π}) = ⊤`.

## Environment note (in-sandbox builds restored — read before any future Cowork pass)

This pass ran in the Cowork sandbox, which cannot reach Lean's release servers (egress
allowlist; the "package managers" tier the user enabled applies only to freshly booted
sessions). Resolved WITHOUT a session restart: the user dropped `lean-4.30.0-linux_aarch64.tar.zst`
into the repo folder (now gitignored — keep it there; it makes every future session
network-independent), extracted to session-local disk. Two environment facts that will recur:

1. **The FUSE mount caps simultaneously-open files at ~1019** (measured; the daemon's limit, not
   `ulimit` — shell soft/hard were already 524288). Lean holds ~2000 oleans open, so `lake build`
   **cannot run against the mounted repo**. Fix: a **hybrid local workspace** under the session
   tmp dir — olean/build trees of all packages rsynced to local disk (~6.2 GB; trim the
   toolchain's `*.a` + LLVM `.so`s to fit), *sources symlinked to the mount*, artifacts rsynced
   back to the mount after green. Mount-side `lake build --no-build` then re-verifies acceptance.
2. **Each bash call is a bwrap sandbox with `--die-with-parent` + 45 s cap** — no background
   builds survive a call. Builds fit anyway: with oleans local and the page cache warm,
   the new file elaborated in ~2 s; the full-project build (8,499 jobs, mostly replays) in ~30 s.
   **Known exception (post-Pass-27 style cleanup): `GaloisInertia.lean` elaborates LONGER than
   one 45 s call** (ten declarations with 1M-heartbeat instance searches; no intra-file
   checkpointing) — edits to that file cannot be compile-verified in-sandbox and must be
   verified by a host-side `lake build` before committing.

## Route-first-step probes (against the pinned Mathlib source, before writing)

All names verified by grep in `.lake/packages/mathlib` (the FUSE mount serves greps fine):
`Subring.closure_induction` (dependent motive, `Algebra/Ring/Subring/Basic.lean:507`; cases
`mem/zero/one/add/neg/mul`); `Ideal.mul_mem_right`; `QuotientGroup.ker_lift` +
`QuotientGroup.map_mk'_self` + `MonoidHom.ker_eq_bot_iff`; `isCyclic_of_injective_ringHom`
(**naming drift caught by probe**: `subgroup_units_cyclic` deprecated 2026-03-03,
`isCyclic_of_subgroup_isDomain` deprecated 2026-03-04 — the pin is newer than priors);
monogenicity **ABSENT** as a general lemma (only `PowerBasis.adjoin_gen_eq_top`-adjacent
machinery) — re-verified independently, not cited from the discarded orphans.

## What was built (`Anabelian/TameInjectivity.lean`, all standard-axioms-only)

- `smul_sub_dvd_of_mem_closure` — `(σπ − π) ∣ (σx − x)` on `closure (A₀ ∪ {π})`
  (`Subring.closure_induction`; `mul`: `σ(xy) − xy = σx·(σy − y) + (σx − x)·y`).
- **`mem_ramificationGroup_of_smul_uniformizer_sub_mem`** — detection on `π`, all `i`
  (Serre IV §1 Prop. 5 monogenic form): divide, `Ideal.mul_mem_right`.
- **`ker_tameCharacter`** — `ker θ₀ = (G₁).subgroupOf G₀`: `⊇` Pass 24; `⊆`: `u_σ ≡ 1 mod 𝔪` ⟹
  `σπ − π = π(u_σ − 1) ∈ 𝔪²` ⟹ detection at `i = 1`.
- **`tameQuotientHom_injective`** — `G₀/G₁ ↪ 𝓀ˣ` (`ker_lift` + kernel identification +
  `map_mk'_self`).
- `tameQuotient_mul_comm`; `tameQuotient_isCyclic` (`isCyclic_of_injective_ringHom` composed
  with `Units.coeHom`) — both stretch goals landed.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| `Units.map`-defeq friction unpacking `θ₀σ = 1` (P23/24's residue-vs-`mk` déjà vu) | did NOT bite: `have h1 : Units.map … = 1 := hσ` accepted by defeq; `simpa` finished | clean |
| `closure_induction` case/binder friction (recently refactored API) | none — probe-matched signature elaborated first try | probe paid off |
| `Finite (G₀ ⧸ N)` instance might need manual `Quotient.finite` | synthesized automatically | clean |
| writing Lean without a compiler is risky | the ONLY failures: four missing branch-closers (`exact dvd_zero _`/`dvd_rfl`) in the induction — caught on first in-sandbox elaboration, fixed in one edit | the in-sandbox loop matters |

## Build + headline

`lake build`: **8,499 jobs, clean** (in-sandbox; mount-side `--no-build` re-verified); all six
audits standard-only; zero `axiom` declarations project-wide. **HEADLINE: `ker θ₀ = G₁` and
`G₀/G₁ ↪ 𝓀ˣ` — the tame quotient is a proved embedding, abelian, cyclic when `G₀` is finite —
conditional on the explicit, named monogenicity hypothesis (Serre IV §2 Prop. 7 at level 0,
monogenicity-conditional).** No new `structure`/`class`; no owed witness incurred (hypothesis
not claimed irremovable — Pass-23 precedent); D1 N/A; D2 N/A. R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. L2's level-0 quotient structure closed modulo one named hypothesis.

## Scope: pointer to Pass 26

Candidates, leverage order: (a) **the concrete properly-decreasing chain** — `G₀ ≠ G₁` for an
explicitly tamely-ramified extension (the come-apart exhibit; worth more now that the tame
structure is closed: it would witness `θ₀ ≠ 1` somewhere — `𝔽_p((s))/𝔽_p((s²))`-style toy or
`Zsqrtd`-adjacent); (b) **the `i ≥ 1` additive injections** `G_i/G_{i+1} ↪ 𝓀⁺` — the detection
engine is already proved for all `i`, only the additive cocycle layer is new; (c) **the
finite-extension local-field instances** (~3-pass infra; ALSO the gate to discharging this
pass's monogenicity hypothesis and Pass 23's instantiation gap); (d) L1 polish (continuity of
`residueReductionHom`; the imperfect-case generality). Honest frame: R1–R3 distant; L2
finite-level structure closing rung by rung, one named hypothesis outstanding.

---

# Pass 26 — rung L2: the come-apart exhibit — `G₀ ≠ G₁` constructed (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Per the Pass-25 pointer, candidate (a), user-selected: the concrete properly-decreasing
chain — an explicit `(K, L, A)` with `ramificationGroup K A 0 ≠ ramificationGroup K A 1`,
discharging the obligation logged since Pass 23. (ii) Scope: ONE proper decrease, fully
witnessed; a hypothesis-free closed instance as the capstone. (iii) NOT in scope: the full chain
structure of the ambient group (`G₁ = ⊥` is false for the big decomposition group and the
quadratic-subextension statement needs `k⸨X²⸩`). (iv) Route decision deferred to inventory:
Laurent series `k⸨X⸩` (tame quadratic flavor, `G₀ ≠ G₁`) vs `ℤ[i]` at `(1+i)` (wild, jump at
`G₁ ≠ G₂`).

## Route decision (probe-driven)

**Laurent series won decisively.** Inventory finds (all pinned-Mathlib, grep-verified):
`LaurentSeries.valued : Valued k⸨X⸩ ℤᵐ⁰` + `val_le_one_iff_eq_coe` (membership in the unit ball
⟺ power series — the entire `A ≅ k⟦X⟧` bridge, free); `PowerSeries.evalNegHom` (`f(X) ↦ f(−X)`
pre-packaged, with `rescale_rescale`/`rescale_one` for the involution and `evalNegHom_X`);
`of_powerSeries_localization : IsLocalization (powers X) k⸨X⸩` (the lift device for `σ`);
`ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem` (decomposition membership);
`HahnSeries.ofPowerSeries_injective` (the push-down). The Gaussian-integer route would have
needed `HeightOneSpectrum` valuation API plus `WithZero ℤₘ₀` exponent bookkeeping on localized
fractions — strictly more friction for a *weaker-flavored* (wild) exhibit.

**The `σ ∉ G₁` design choice:** rather than `𝔪²`-valuation arithmetic, use **Pass 24's tame
character as the detector** — `σπ = π·(−1)` ⟹ `tameUnit σ = −1` (`tameUnit_unique`) ⟹
`θ₀(σ) = −1 ≠ 1`, while `tameCharacter_eq_one` makes `G₁`-membership force `θ₀(σ) = 1`. The
`−1 ≠ 1` step pushes down to `(2 : k) ≠ 0` through `ofPowerSeries_injective` at the constant
coefficient — no value-group arithmetic anywhere in the file.

## What was built (`Anabelian/RamificationExhibit.lean`, all standard-axioms-only)

- `laurentNegXAlgEquiv` — `σ` as a `k`-algebra involution of `k⸨X⸩`: `evalNegHom` through
  `IsLocalization.lift` (units of `(−X)^n` from `single_ne_zero`), involution via
  `IsLocalization.ringHom_ext`, `k`-linearity via `HahnSeries.algebraMap_apply'` (see below).
- `laurentIntegers` / `mem_laurentIntegers_iff` — `A` and its power-series membership.
- `laurentUniformizer` + **`maximalIdeal_laurentIntegers_eq_span`** — `𝔪_A = (X)`, `X ≠ 0`:
  nonunits ⟺ zero constant coefficient (`isUnit_iff_constantCoeff`, `X_dvd_iff`), the
  Pass-24/25 uniformizer package instantiated concretely for the first time.
- `laurentNegX_mem_decompositionSubgroup` — `σ • A = A` via `σ⁻¹ = σ`
  (`inv_eq_of_mul_eq_one_right`) + stability of the power-series subring.
- **`laurentNegXDecomp_mem_ramificationGroup_zero`** — `σ ∈ G₀` (constant terms cancel).
- **`laurentNegXDecomp_notMem_ramificationGroup_one`** — `σ ∉ G₁` (`(2:k) ≠ 0`), the
  tame-character detection above.
- **`laurentRamificationGroup_zero_ne_one`** and **`ramificationGroup_zero_ne_one_rat`** — the
  exhibit, and its fully closed `k = ℚ` instance (no hypotheses, no variables).

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the `↥A`-smul coe bridge to need a manual lemma | `rfl` — `coe_laurentNegXDecomp_smul` proved by `rfl` first try | the RamificationGroup `SubMulAction` is defeq-transparent |
| `σ ∈ G₀` to be the fiddly half | compiled on the **first** elaboration attempt | the `mem_span` helper carried it |
| `Algebra k k⸨X⸩` to be the HahnSeries base instance | it is `HahnSeries.powerSeriesAlgebra` (routes through `k⟦X⟧`; `IsScalarTower k k⟦X⟧ k⸨X⸩` does NOT exist) — diagnosed via `#synth` probe; `HahnSeries.algebraMap_apply'` is the right lemma | the one genuine surprise; two failed guesses before probing the instance directly |
| coercion bookkeeping (`↑(π*c)` vs `↑π*↑c`, `↑0`, units-val) to bite | it bit exactly as in P23–25 (`push_cast`, explicit `coe_*` rewrites, the P25 defeq-`have` for `Units.map`) | known friction, known fixes |
| `isUnit_of_mul_eq_one` available | unknown identifier at this pin | replaced by `isUnit_iff_exists.mpr` |

## Build + headline

`lake build`: **8,500 jobs, clean** (in-sandbox; mount-side `lake -R build --no-build`
re-verified all targets up-to-date); all seven audits standard-only; zero `axiom` declarations
project-wide. Environment refinement for the recipe: exclude lake's compiled config from the
artifact rsync-back (`.lake/config` is machine-pathed — it was cleared so each machine
reconfigures fresh). **HEADLINE: the ramification filtration provably comes apart —
`ramificationGroup ℚ (laurentIntegers ℚ) 0 ≠ ramificationGroup ℚ (laurentIntegers ℚ) 1`, a
fully closed witness, with the jump detected by the Pass-24 tame character.** The Pass-22
collapse and this pass's separation are now *both* constructed: the two regimes the
hypothesis-parametrized L2 architecture was built for. No new `structure`/`class`; no owed
witness (an obligation discharged, none incurred); D1 N/A; D2 N/A. R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. The Pass-23 logged obligation (come-apart exhibit) is DISCHARGED.

## Scope: pointer to Pass 27

Candidates, leverage order: (a) **the `i ≥ 1` additive injections** `G_i/G_{i+1} ↪ 𝓀⁺` — the
Pass-25 detection engine covers all `i`; only the additive cocycle layer is new; with it the
finite-level quotient structure is complete across all levels; (b) **the finite-extension
local-field instances** (~3-pass infra; gates the monogenicity-hypothesis discharge AND the
`A = 𝒪_L` instantiation of everything in L2); (c) **wild `G₁` pro-`p`** (needs (a) as input:
`G_i/G_{i+1}` embeds in `𝓀⁺`, an elementary abelian `p`-group at finite level); (d) L1 polish
(continuity of `residueReductionHom`; imperfect-case generality). The exhibit also suggests a
cheap stretch for whichever pass goes next: `θ₀(σ) = −1` computes the tame character's *value*
on a concrete element — the first numerical datum out of the L2 structure. Honest frame: R1–R3
distant; L2's level-0 theory is now complete (definition, basics, tame character, injectivity
modulo monogenicity, and both regimes witnessed).

---

# Pass 27 — rung L2: additive characters `θ_i : G_i →* 𝓀⁺` (`i ≥ 1`) + the `i = 0` witness (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Per the Pass-26 pointer, candidate (a), user-selected: the `i ≥ 1` additive injections.
(ii) Scope: `additiveCoeff` + the hom `θ_i` (`i ≥ 1`) + `G_{i+1} ≤ ker` + quotient hom + (under
Pass-25 monogenicity) `ker = G_{i+1}`, injectivity, commutativity. (iii) The `1 ≤ i` hypothesis
will be CLAIMED load-bearing ⟹ extended rule-2 obliges a witness: plan to discharge IN-PASS via
the Pass-26 exhibit (`σ² = 1` vs `res a_σ = −2`). (iv) Stretch: the uniformizer-twist law
`res(w)^i·res(a') = res(a)` (all `i`; recovers P24's independence at `i = 0`).

## What was built (`Anabelian/AdditiveCharacter.lean`, all standard-axioms-only)

- `additiveCoeff` (every level) + `_spec`/`_unique`/`_one`; `smul_uniformizer_eq_mul`
  (`linear_combination` from the spec — clean).
- **`additiveCharacter (hi : 1 ≤ i) : G_i →* Multiplicative 𝓀`**: cocycle
  `a_{στ} = a_σ + (1 + π^i a_σ)^(i+1)·σ(a_τ)` (proved by `smul_mul'`/`smul_pow'` + `ring`),
  straightened by `residue_one_add_pow_mul` (needs `i ≥ 1`) + P24's
  `residue_smul_eq_of_mem_ramificationGroup_zero` (via antitonicity).
- `additiveCharacter_eq_one`; `additiveQuotientHom`; under monogenicity:
  **`ker_additiveCharacter`** (P25 detection at `i+1` — the engine covered all `i` as designed),
  **`additiveQuotientHom_injective`**, **`additiveQuotient_mul_comm`**.
- **`additiveCoeff_residue_not_additive_at_zero`** — the rule-2 witness, discharged in-pass: on
  the P26 exhibit, `a_{σ·σ} = a_1 = 0` (`σ` is an involution) while `res a_σ + res a_σ = −4`,
  and `−4 ∉ 𝔪` because `4` is a unit of `A` (P26's `isUnit_of_constantCoeff_ne_zero` +
  `map_ofNat`/`norm_cast` for the numeral coercions). So additivity at `i = 0` is **refuted**,
  not just unproved — the `1 ≤ i` gate is witnessed.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the cocycle computation to be the hard part | landed first-try modulo an argument-order trap (`eq_add_of_sub_eq` adds on the wrong side — replaced by `linear_combination`) | the P24-style scaffolding (spec/unique) carries it |
| `K` as a section variable to stay out of K-free lemmas | it did (`residue_one_add_pow_mul` takes no `K`) — but my call sites passed `K` anyway | one-character fixes |
| the P24 `whnf`-timeout trap to reappear at the quotient corollary | it appeared — at the **twist** theorem, misattributed twice to neighbors (end-position error reporting) | see below |
| the twist (stretch) to be routine | its *statement* hits a reproducible `whnf` divergence elaborating `additiveCoeff` at the composite uniformizer `π * ↑w`: not cured by `maxHeartbeats 800000`, coercion ascription `(w : ↥A)`, `subst`-elimination of `π'`, or replacing `linear_combination` with explicit `calc`/`ring`. Root cause unisolated (suspect: unification unfolding `Exists.choose` through the composite-argument spec during statement elaboration) | **CUT from scope mid-pass** (the P22/P24 under-promise discipline applied to ourselves); the better target is the twist-free canonical `𝔪^i/𝔪^(i+1)`-valued map — named future work. A failed stretch goal, honestly reported; the core pass is unaffected |
| numeral coercion friction in the witness (`(4 : ↥A)` vs `(4 : k⟦X⟧)`) | bit as expected; `norm_cast` + `map_ofNat` resolved | known friction class |

## Build + headline

`lake build`: **8,501 jobs, clean** (in-sandbox; mount-side `lake -R build --no-build`
re-verified; lake's machine-pathed config cleared after sync — the rsync-back must exclude
`.lake/config`, now part of the recipe); all eight audits standard-only; zero `axiom`
declarations project-wide. **HEADLINE: every finite-level quotient of the ramification
filtration now carries its classical character — `G₀/G₁ ↪ 𝓀ˣ` (P24/25) and `G_i/G_{i+1} ↪ 𝓀⁺`
(`i ≥ 1`, this pass, monogenicity-conditional) — and the multiplicative/additive dichotomy at
`i = 0` is constructively witnessed, not asserted.** No new `structure`/`class`; one would-be
owed witness DISCHARGED in-pass; D1 N/A; D2 N/A. R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. Extended-rule-2 obligation for the `1 ≤ i` gate discharged in-pass.

## Scope: pointer to Pass 28

Candidates, leverage order: (a) **the finite-extension local-field instances** (the known
~3-pass infra subproject; now gates THREE things: the monogenicity-hypothesis discharge for
P25/P27, the `A = 𝒪_L` instantiation of all of L2, and eventual Herbrand work at honest
generality); (b) **wild `G₁` pro-`p`** — with the additive embeddings in hand, `G_i/G_{i+1}`
embeds in `𝓀⁺`; for finite residue characteristic `p` this is an elementary abelian `p`-group,
giving `G₁` pro-`p` at finite level (needs `CharP 𝓀 p` plumbing); (c) **the canonical
`𝔪^i/𝔪^(i+1)`-valued form** of the additive character (also resolves the twist question that
defeated this pass's stretch goal); (d) L1 polish (continuity of `residueReductionHom`;
imperfect-case generality). Honest frame: R1–R3 distant; the finite-level L2 quotient theory is
now COMPLETE modulo the named monogenicity hypothesis — the architecture's next genuinely new
content is either downward (concrete instances) or upward (Herbrand/upper numbering).

---

# Pass 28 — rung L2: wild inertia — `G₁` is a `p`-group, `p ∤ |G₀/G₁|` (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Per the Pass-27 pointer, candidate (b), user-approved: wild `G₁` pro-`p` at finite level.
(ii) Scope: exponent-`p` higher quotients (`CharP 𝓀 p`); `σ^(p^k)`-climbing; `IsPGroup p G₁`
(finite + separation + monogenicity); tame quotient `p`-torsion-free (`p` prime); `p ∤ |G₀/G₁|`
(Cauchy). (iii) NOT in scope: `Sylow` packaging (named); the pro-`p` limit form (upper
numbering); local-field instantiation. (iv) Design: `IsPGroup`'s definition is literally
`∀ g, ∃ k, g^(p^k) = 1` — match the proof to it (no extension-closure API needed).

## Route-first-step probes

`IsPGroup` (def shape confirmed), `ofAdd_nsmul`/`toAdd_pow`, `frobenius_inj`
(`Algebra/CharP/Reduced.lean` — fields qualify), Cauchy = `exists_prime_orderOf_dvd_card`
(`Fintype`-based; bridged via `nonempty_fintype` + `Nat.card_eq_fintype_card`),
`QuotientGroup.eq_one_iff`. All grep-verified pre-write.

## What was built (`Anabelian/WildInertia.lean`, all standard-axioms-only)

The six declarations as scoped (see ledger). Design notes: the fixed-ring hypothesis is taken
ONCE over `G₀` and restricted per level via `ramificationGroup_antitone` (cleaner than per-level
binders when quantifying over all `i`); `isPGroup_ramificationGroup_one` needs no primality of
`p`; the tame side kills `p`-torsion via `frobenius_inj` rather than binomial expansions.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| 2–4 build iterations (the P25–27 norm) | **compiled clean on the FIRST build** — zero errors, zero warnings | the probe-first + battle-tested-idiom stack has matured; every lemma name and every coercion pattern came from verified precedent |
| the `IsPGroup` chain to need extension-closure API | unnecessary — the definition is elementwise and matched the `σ^(p^k) ∈ G_{1+k}` climb exactly | reading the definition first beats assuming the textbook route |

## Build + headline

`lake build`: full project clean (in-sandbox; `--log-level=warning` now used for full-project
verification — replaying 8,500 cached info-lines through the pipe was itself eating the 45 s
call window); all six audits standard-only; zero `axiom` declarations project-wide.
**Environment incident, logged for the recipe: the ws→mount artifact rsync CLOBBERED the
host-built `GaloisInertia`/`UnramifiedQuotient`/`RamificationDegeneracy` artifacts with stale
ws copies** (the ws never successfully elaborated GaloisInertia — the 45 s wall; plain `rsync -a`
overwrote newer host artifacts with older ws ones). Benign — sources unchanged, the host build
self-heals by re-elaborating the trio once — but the recipe is now: **sync back only the targets
the sandbox actually built, or use `rsync -au`** (update-only). **HEADLINE: in residue
characteristic `p`, `G₁` is a `p`-group (`IsPGroup p G₁`, finite level, monogenicity-conditional,
`p` not even assumed prime) and `p ∤ |G₀/G₁|` — `G₁` is the normal Sylow `p`-subgroup of inertia:
the wild/tame dichotomy, completing Serre IV §2 at finite level.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 29

The finite-level L2 arc is closed. Candidates, leverage order: (a) **the finite-extension
local-field instances** (the ~3-pass infra block; discharges monogenicity, instantiates ALL of
L2 at `A = 𝒪_L` with `char 𝓀 = p` automatic, and opens honest-generality Herbrand); (b) **the
ascent: Herbrand `φ`/`ψ` + upper numbering** (Serre IV §3 — the path to the absolute-group
pro-`p` statement and, much later, `G^v`-compatibility); (c) the canonical `𝔪^i/𝔪^(i+1)`
characters + `Sylow` packaging (polish tier); (d) L1 polish (continuity; imperfect case).
Honest frame: R1–R3 distant; L2's finite-level chapter reads, end to end, like the textbook —
which was the point of the rung.

---

# Pass 29 — the descent, rung 1: `𝒪_L : ValuationSubring L` + hypotheses discharged (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) User-approved direction: descend (the finite-extension block). (ii) Rung-1 scope:
`extensionIntegers K L : ValuationSubring L` (= `integralClosure 𝒪[K] L`, mem_or_inv_mem via
spectral, Pass-18-localized); Noetherian-ness (separable); discharge of Pass 23's separation +
Pass 24's finiteness/eventual-triviality at `𝒪_L`. (iii) NOT in scope (later rungs, named): DVR,
finite residue, `IsNonarchimedeanLocalField L` assembly, monogenicity discharge, `e·f = n`.
(iv) Design: reuse the Pass-17/18 template verbatim with `L` for `K̄` — the spectral bridge
works for any algebraic extension; finiteness replaces algebraic closure.

## Route-first-step probes

`spectralNorm.normedField` (sig re-read: `NontriviallyNormedField K` + algebraic `L` — the
Pass-18 `letI` chain supplies everything; finite ⟹ `Algebra.IsIntegral`/`IsAlgebraic`
instances); `Mathlib/NumberTheory/LocalField/Basic.lean` re-inventoried — **richer than the
Pass-13-era notes**: it now has `IsDiscreteValuationRing 𝒪[K]`, `Finite 𝓀[K]`,
`CompleteSpace K`, `valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o ℤᵐ⁰`, `IsAdicComplete`
(the K-side is fully equipped; finite-extension instances still absent ✓);
`IsIntegralClosure.isNoetherianRing` (+ `.finite`, `.isNoetherian`) in
`DedekindDomain/IntegralClosure.lean` with exactly the `𝒪[K]`-available instance stack;
`isNoetherianRing_of_surjective` for the carrier transport; `AlgEquiv.fintype`.

## What was built (`Anabelian/ExtensionIntegers.lean`, all standard-axioms-only)

The six declarations as scoped (ledger). Notes: `mem_or_inv_mem` reduces to
`(Valued.v).valuationSubring.mem_or_inv_mem` after the membership bridge — i.e. the
ValuationSubring property is *inherited from the spectral valuation* through the
`integralClosure = Valued.integer` identification; `IsLocalRing` then comes free from Mathlib's
`ValuationSubring` instances (the finite-level analogue of Pass 18's transport, at zero cost).
The carrier-identity `RingEquiv` (Subalgebra-subtype ≃ ValuationSubring-subtype, all fields
`rfl`) transports Noetherian-ness.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the P17/18 template to adapt with light friction | **first-try clean build** (second consecutive) | template + probe discipline fully compounding |
| `LocalField/Basic.lean` to be as sparse as the P13 notes said | substantially richer now (DVR, finite residue, ℤᵐ⁰ value group, completeness all present for `K`) | re-inventory standing assumptions each block — the pin moves |

## Build + headline

`lake build`: full project clean (8,477-job closure for the new file; root clean at warning
level); all six audits standard-only; zero `axiom` declarations project-wide; artifact sync-back
now `rsync -au` (update-only — the Pass-28 clobber cannot recur). **HEADLINE: `𝒪_L` exists as a
`ValuationSubring` of any finite extension of a nonarchimedean local field — `mem_or_inv_mem`
proved via the spectral norm (the unique-extension theorem), Pass-18-contained — and the
abstract L2 theory's separation and eventual-triviality hypotheses are now THEOREMS at `𝒪_L`
(finite separable case).** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free. Two standing hypotheses of the abstract theory discharged at `𝒪_L`.

## Scope: pointer to Pass 30

The block continues, leverage order: (a) **`IsDiscreteValuationRing 𝒪_L`** (Noetherian ✓ + local
✓ + valuation ring ✓ + not-a-field — the last needs the valuation on `L` nontrivial, i.e. `K`'s
uniformizer is a non-unit in `𝒪_L`; with DVR comes the uniformizer package `𝔪_L = (π_L)` —
Passes 24–28's hypothesis discharged at `𝒪_L`); (b) **finite residue field `𝓀_L`** (residue ext
finite over `𝓀[K]` via module-finiteness; then `CharP 𝓀_L p` automatic — Pass 28's hypotheses
fully concrete); (c) the `IsNonarchimedeanLocalField L` instance assembly (completeness via
`FiniteDimensional.complete`); (d) the **monogenicity discharge** (the deepest rung — Serre IV
§1 Prop. 5's own proof; needs (a)+(b) and the unramified-subextension story). Honest frame:
R1–R3 distant; the descent's first rung is laid and the abstract/concrete gap is closing
hypothesis by hypothesis.

---

# Pass 30 — the descent, rung 2: `𝒪_L` is a DVR; uniformizer package discharged (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Continue the block per the Pass-29 pointer, candidate (a). (ii) Scope: the intersection
`𝒪_L ∩ K = 𝒪[K]`; `𝔪_L ≠ ⊥`; `IsDiscreteValuationRing 𝒪_L` (separable); the uniformizer
package `∃ π, 𝔪_L = (π) ∧ π ≠ 0`; showcase: the tame character of `L/K` exists. (iii) NOT in
scope: finite residue field, full instance assembly, monogenicity. (iv) Route: Noetherian +
Bezout ⟹ PID via `IsBezout.TFAE`; not-a-field via the base uniformizer through the
intersection lemma.

## Probes

`IsBezout.TFAE` (Noetherian ↔ PIR for Bezout domains, `.out 0 1`);
`IsDiscreteValuationRing extends IsPrincipalIdealRing, IsLocalRing` + `not_a_field'`;
`IsIntegrallyClosed.isIntegral_iff`; `isIntegral_algebraMap_iff`;
`IsDiscreteValuationRing.exists_irreducible` + `irreducible_iff_uniformizer` (P24's device).

## What was built (`Anabelian/ExtensionUniformizer.lean`, all standard-axioms-only)

The five declarations as scoped (ledger).

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| another first-try build | three iterations: an illegal `omit` (the lemma references `extensionIntegers`, which carries the full local-field stack — can't omit), a `field_simp` replaced by `inv_eq_of_mul_eq_one_right` (cheaper and correct-direction), and `Irreducible.not_unit → not_isUnit` (pin rename) | back to normal friction; the rename catalog grows |
| the per-call wall to be a non-issue | **new environment fact**: with the `import Mathlib` closure, ~30 s of every call is *olean-loading I/O* (sys-time-dominated; the 5.7 GB olean set exceeds the VM's 3 GB RAM, so the page cache can never hold it) — leaving ~10 s of elaboration budget per call. Descent files must stay individually light; `--log-level=warning` is now standard for build calls (replay printing was eating seconds) | logged for the recipe; future descent passes should keep declarations few and cheap per file |

## Build + headline

Full build clean at warning level; all five audits standard-only; zero `axiom` declarations
project-wide; sync-back update-only. **HEADLINE: `𝒪_L` is a discrete valuation ring for every
finite separable extension of nonarchimedean local fields, and the uniformizer package
`(π, 𝔪 = (π), π ≠ 0)` — the hypothesis triple of every character theorem since Pass 24 — is now
a THEOREM at `𝒪_L`; the tame character of `L/K` exists (`extensionTameCharacter`). Of the
abstract theory's hypothesis stack, only monogenicity remains open.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 31

(a) **Finite residue field `𝓀_L`** — module-finiteness of `𝒪_L` over `𝒪[K]`
(`IsIntegralClosure.finite`) pushed to the residue level (needs the `IsLocalHom` brick, the
P19 pattern at finite level); then `CharP 𝓀_L p` and Pass 28's wild/tame dichotomy is fully
concrete at `𝒪_L` except monogenicity. (b) The `IsNonarchimedeanLocalField L` assembly
(completeness via `FiniteDimensional.complete` + the pieces). (c) **Monogenicity** (deepest;
needs (a) + the unramified subextension story — possibly via Mathlib's
`IsLocalRing.IsUnramified`/Etale machinery, to be inventoried). Honest frame: R1–R3 distant;
the descent is two rungs down, one hypothesis from closing the loop on the abstract theory.

---

# Pass 31 — the descent, rung 3: `𝓀_L` is finite; `CharP` concrete (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) Per the Pass-30 pointer, candidate (a), user-approved: the finite residue field. (ii) Scope:
`extensionAlgebraMap` + unit transfer + `IsLocalHom` (the P19 brick at finite level);
`Finite 𝓀_L` (separable); `CharP` transfer. (iii) NOT in scope: instance assembly,
monogenicity. (iv) Design: the finiteness chain `Module.Finite 𝒪[K] 𝒪_L → (residue surjection)
→ Module.Finite 𝒪[K] 𝓀_L → (restrict scalars through the local hom) → Module.Finite 𝓀[K] 𝓀_L →
Finite`, with ALL module/algebra structures `letI`-local to the proof.

## Probes

`ResidueField.map` + `map_residue` (**rfl** — which makes the `IsScalarTower` step
`of_algebraMap_eq (fun _ => rfl)`); `Module.Finite.of_restrictScalars_finite`;
`Module.finite_of_finite`; `charP_of_injective_ringHom`; `Finite 𝓀[K]` (LocalField.Basic).

## What was built

The four declarations as scoped (ledger), in two files — **the build-granularity lesson
applied**: the single-file version did not fit the ~40 s per-call window (the `import Mathlib`
closure costs ~30 s of olean-loading I/O per call, leaving ~10 s of elaboration), so the
local-hom half and the finiteness half are separate modules. This is now the standing pattern
for descent files.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the letI tower to be the friction point | one defeq failure only: `Algebra.smul_def` is a theorem, not `rfl`, on the subalgebra side — `show` → explicit `SetLike.val_smul`/`smul_def` rewrite | known pattern |
| `map_residue` to need bridging | it is `rfl`, so the scalar tower came free | probe paid off |
| one file to suffice | split required (window variance: the same file built at 31–34 s or not at all) | the I/O wall is the binding constraint on descent passes; plan files at ≤ 2 substantial declarations |

## Build + headline

Full build clean at warning level; all four audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: the residue field of `𝒪_L` is FINITE for finite separable `L/K`, and
the residue characteristic transfers — at `𝒪_L`, the Pass-28 wild/tame dichotomy now has every
hypothesis concrete except monogenicity** (finite decomposition ✓ separation ✓ uniformizer ✓
`CharP 𝓀_L p` ✓). R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 32

(a) **The monogenicity discharge** — the last open hypothesis; inventory first: Mathlib's
unramified/étale machinery (`Algebra.IsUnramified`, `IsLocalRing` Etale files) and the classical
route (Serre IV §1 Prop. 5: complete DVR + finite separable residue ext ⟹ `𝒪_L = 𝒪_{L₀}[π]`;
needs the unramified subextension or a direct primitive-element argument at the residue level).
(b) The `IsNonarchimedeanLocalField L` assembly (completeness via `FiniteDimensional.complete`;
mostly bookkeeping given rungs 1–3). (c) `e·f = n`. Honest frame: R1–R3 distant; one hypothesis
stands between the abstract L2 theory and its full instantiation on local fields.

---

# Pass 32 — the descent, rung 4: the monogenicity engine, totally-ramified case (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) User-approved: the monogenicity discharge itself. (ii) Honest scope decision UP FRONT: the
FULL discharge needs the maximal-unramified-subextension tower (its own multi-pass story); what
one pass can deliver is the **totally-ramified engine** — `A₀ = range(𝒪[K])`, where `hfix` is
free and `hgen` is Serre I §6 Prop. 18's digit expansion. (iii) The totally-ramified DATA
(`hres`: residues covered; `he`: `𝔪_L^e ≤ (ι 𝔪[K])·𝒪_L`) enter as named hypotheses, to be
supplied by `e·f = n` bookkeeping later. (iv) Key design insight: **Nakayama replaces
completeness** — the classical successive-approximation argument needs completeness for infinite
expansions, but module-finiteness (Pass 29) + a depth-`e` expansion + Nakayama over the local
`𝒪[K]` gives `S = ⊤` with no topology at all.

## Probes

`Submodule.le_of_le_smul_of_le_jacobson_bot` (Nakayama, exactly the `N' := ⊤` shape);
`IsLocalRing.maximalIdeal_le_jacobson`; `Module.finite_def`; `Submodule.smul_induction_on`;
`mul_smul_comm`; the dependent-motive `Submodule.span_induction`.

## What was built

Per the ledger: the two global instances (Algebra + Module.Finite, promoted from P31), the free
`hfix` (`AlgEquiv.commutes`), and the engine (digit expansion by induction on depth via `hres` +
`hspan`; bridge `Ideal.map ι 𝔪[K] ⊆ 𝔪[K] • ⊤` by span- and smul-induction; Nakayama closes).

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the engine to be the hardest descent proof yet | ONE real iteration: the span-induction motive captured a duplicate hypothesis (fixed by `clear hz` — the dependent motive generalizes the element, dragging stale hypotheses into the IHs) | the P27 lesson (read the definition, match the proof to it) keeps paying |
| completeness to be needed somewhere | Nakayama + module-finiteness made the argument purely algebraic | the design insight of the pass |
| both files to fight the I/O wall | 31 s and 36 s — both fit | ≤2-declaration discipline works |

## Build + headline

Full build clean at warning level; both audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: for totally-ramified data, the monogenicity hypothesis — the LAST
open hypothesis of the abstract L2 theory — is DISCHARGED: `hfix` free
(`smul_extensionAlgebraMap_range_eq`), `hgen` proved (`closure_range_union_uniformizer_eq_top`).
The full tame/wild quotient structure of Passes 24–28 now instantiates end-to-end on
totally-ramified finite separable extensions of local fields.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 33

(a) **`e·f = n` bookkeeping** — defines `e` and `f` for `L/K` and proves the totally-ramified
characterizations that DISCHARGE `hres`/`he` (`f = 1 ⟹ hres`; `v_L(ϖ_K) = e ⟹ he`), turning
the engine's hypotheses into honest theorems; with it, an assembled showcase ("for totally
ramified `L/K`: `ker θ₀ = G₁`, `G₁` is the Sylow `p`-subgroup, ...") becomes one-line. (b) The
`IsNonarchimedeanLocalField L` assembly. (c) The maximal unramified subextension `L₀` (the
general-case reduction; the deepest remaining piece of the block). Honest frame: R1–R3 distant;
the descent has its engine — what remains is bookkeeping below it and the unramified tower
above it.

---

# Pass 33 — the descent, rung 5: data discharged, showcase assembled (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) User-approved: the `e·f = n` bookkeeping. (ii) Mid-planning REALIZATION that reshaped the
pass: the engine's `he` input is dischargeable **unconditionally** — in the DVR `𝒪_L`,
`span {ι ϖ_K}` is a power of `𝔪_L` by the ideal classification; no totally-ramified assumption,
no numerical `e` needed. Only `hres` is genuinely the totally-ramified datum, and its honest
form is surjectivity of the residue extension. (iii) So scope: discharge `he` outright; reduce
`hres` to `hsurj`; assemble the `hgen` package; instantiate the Pass-25 showcase. (iv) Full
numerical `e·f = n` bookkeeping deferred — not needed for the discharge.

## Probes

`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`; `Ideal.mem_map_of_mem`;
`Ideal.span_singleton_le_iff_mem`; (`ResidueField.map_residue` from P31, rfl).

## What was built

Per the ledger: the two data-discharge lemmas, the assembled `hgen` package, and
**`ker_tameCharacter_extensionIntegers`** — `ker θ₀ = G₁` for totally ramified finite separable
`L/K`, any uniformizer: the abstract Pass-25 theorem with all binders filled by Pass-29–33
theorems.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| to need numerical `e`/`f` definitions | the DVR ideal classification gives `he` with a bare `∃ e` — no arithmetic | the bookkeeping pass mostly dissolved its own bookkeeping |
| the showcase assembly to surface instance friction | the chain typechecked as written (one fix: an `Associated` witness needed `u⁻¹`, not `u`) | the hypothesis-parametrized architecture (P23–28) composes exactly as designed |

## Build + headline

Full build clean at warning level; all four audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: the descent block delivers — `ker θ₀ = G₁` and `G₀/G₁ ↪ 𝓀_Lˣ` hold
for totally ramified finite separable extensions of nonarchimedean local fields, with every
hypothesis of the Passes-23–28 abstract theory now a theorem. Serre IV §§1–2 at level 0, on
actual local fields, five descent rungs, zero axioms.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 34

(a) **The maximal unramified subextension `L₀`** — the general-case reduction (the block's
remaining depth: build `L₀` as the fixed field of inertia or via residue-theoretic lifting; the
engine then runs over `L₀` verbatim); (b) the analogous instantiations of the Pass-27/28
theorems (additive characters' kernels, the wild Sylow statement) at `𝒪_L` — near-one-liners on
the Pass-33 pattern, good consolidation; (c) the `IsNonarchimedeanLocalField L` assembly; (d)
back up the ladder: Herbrand/upper numbering (the ascent), now with a concrete finite-level
floor under it. Honest frame: R1–R3 distant; L2's lower-numbering chapter — abstract theory,
witnesses, characters, dichotomy, and concrete instantiation — is essentially a closed book for
the totally ramified case.

---

# Pass 34 — the descent, rung 6: inertia-fixed integers; engine generalized; general kernel theorem (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) User-approved: the maximal unramified subextension. (ii) Honest scope: the FULL `L₀` story
is two passes; this pass delivers the decisive reduction — define the **inertia-fixed
integers** (the ring-incarnation of `𝒪_{L₀}`; `hfix` free BY DEFINITION), generalize the
Pass-32 engine to arbitrary base subrings ⊇ `range ι`, and state the **general** kernel theorem.
(iii) Key structural observation driving the design: the engine's Nakayama spine never used
`A₀ = range ι` — only `S ⊇ range ι` (for the `𝒪[K]`-module structure on the generated subring)
and digit-residues-from-`A₀`. The Nakayama base stays `𝒪[K]` even for larger `A₀`. (iv) After
this pass the general case hangs on ONE lemma (`hresid`): inertia-fixed integers cover `𝓀_L`
(= "`L/L₀` totally ramified") — proof path: Mathlib's finite-level keystone
(`Ideal.Quotient.stabilizerHom_surjective`) + finite-field Galois descent; next rung.

## What was built

Per the ledger: the `inertiaFixedIntegers` subring (fixedness lemmas free), the generalized
engine (Pass-32 proof with abstracted base binder — verbatim adaptation), and
`ker_tameCharacter_of_inertiaFixed_cover`.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the generalization to need new module plumbing | verbatim Pass-32 proof with two-line changes (the base binder + `hA₀S`) | recognizing what a proof DOESN'T use is as valuable as the proof |
| friction somewhere | **both files first-try clean** (third and fourth first-try builds of the block) | the descent idiom is fully stabilized |

## Build + headline

Full build clean at warning level; all five audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: the general kernel theorem — for ANY finite separable extension of
nonarchimedean local fields, `ker θ₀ = G₁` holds modulo exactly one named classical lemma
(`hresid`: inertia-fixed integers cover the residue field). The maximal-unramified-subextension
reduction is in place; what remains of it is one lemma with a known proof path.** R1–R3
untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 35

(a) **Prove `hresid`** — the block's keystone finale: Mathlib's finite-level
`Ideal.Quotient.stabilizerHom_surjective` (the non-profinite sibling of the Pass-20 keystone)
gives `G ↠ Gal(𝓀_L/𝓀[K])` with kernel-side inertia; then for `x̄ ∈ 𝓀_L`, descend a
representative to the inertia-fixed subring (finite-field Galois theory + an averaging or
Hensel-free lifting argument — inventory first: the exact statement shape in
`RingTheory/Invariant/Basic.lean`). With it, `ker θ₀ = G₁` holds unconditionally on local
fields. (b) The P27/P28 instantiations (consolidation). (c) `IsNonarchimedeanLocalField L`
assembly. Honest frame: R1–R3 distant; the descent is one lemma from complete.

---

# Pass 35 — the descent, rung 7 (first half): the inertia orbit polynomial (2026-06-10)

## Restatement + the design discovery

(i) User-approved: prove `hresid`. (ii) The inventory of `RingTheory/Invariant/Basic.lean`
found `MulSemiringAction.charpoly` (the orbit polynomial) with `smul_coeff_charpoly` —
symmetric-function invariance FREE — and `Subgroup.mulSemiringAction` makes it apply over `G₀`
directly. (iii) The full proof design (elementary — **no Hensel, no Lucas, no completeness**):
coefficients of `∏_{σ∈G₀}(X − σ•b)` are inertia-fixed; mod `𝔪` the polynomial is
`(X − b̄)^{p^a·m}` (Pass 24's residue-fixing); freshman's dream
(`(X − b̄)^{p^a·m} = (X^{p^a} − b̄^{p^a})^m`) puts `±m·b̄^{p^a}` at the `X^{p^a(m−1)}`
coefficient; `p ∤ m` makes `m` invertible in the residue image (a finite subfield); take `b̄` a
generator of the cyclic `𝓀_Lˣ` — then `b̄^{p^a}` is also a generator (Frobenius is an
automorphism), so the image is all of `𝓀_L`. (iv) Two passes: bricks now, extraction+assembly
next.

## What was built

`coeff_inertiaCharpoly_mem` + `map_residue_inertiaCharpoly` (see ledger). Both essentially
one-liners over Mathlib's machinery once the right objects are named — the pass's substance was
the DESIGN (finding charpoly + the Lucas-free coefficient route).

## Build + headline

Clean (one window-variance retry); both audits standard-only. **HEADLINE: every coefficient of
`(X − b̄)^{|G₀|}` is the residue of an inertia-fixed integer — the raw material for `hresid` is
in place, with an elementary assembly plan.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 36

The finale: (1) coefficient extraction — in `𝓀_L[X]`: `(X − b̄)^{p^a m} = (X^{p^a} − b̄^{p^a})^m`
(`sub_pow_char_pow`), and the `X^{p^a(m−1)}`-coefficient of the right side is
`−m·b̄^{p^a}` (binomial expansion, single surviving term); (2) the residue image
`F := (inertiaFixedIntegers).map residue` is a finite subfield containing `m·b̄^{p^a}` and `m⁻¹`
⟹ `b̄^{p^a} ∈ F`; (3) choose `b` with `b̄` a generator of `𝓀_Lˣ` (cyclic ✓, lift via
`Ideal.Quotient.mk_surjective`); `b̄^{p^a}` is a generator (`p ∤ |𝓀_Lˣ|`) ⟹ `F = 𝓀_L` ⟹
**`hresid`**; (4) the unconditional kernel theorem
`ker_tameCharacter_extensionIntegers_general` := Pass 34's theorem + `hresid` — **the descent
closes**. Then: P27/P28 instantiations; `IsNonarchimedeanLocalField L`; or the ascent.

---

# Pass 36 — the descent finale: `hresid` proved; the unconditional kernel theorem (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) User-approved: the handoff's Pass-36 plan — prove `hresid`, then the unconditional kernel
theorem. (ii) Honest scope: one file (`Anabelian/InertiaResidueCover.lean`), two substantial
declarations + a one-liner finale (the finale adds no imports, so no second file). (iii) The
proof as designed during probing simplified the Pass-35 sketch twice: the cyclic-generator
transport is unnecessary (every `b̄` satisfies `b̄^{p^e} ∈ F`, and `x ↦ x^{p^e}` = iterated
Frobenius is *surjective* on the finite `𝓀_L` — injective ring hom out of a field + finite),
and no subfield structure on `F` is needed (`m⁻¹ = m^{q−2}` by `pow_card_sub_one_eq_one` keeps
everything in subring-membership arithmetic). `p := ringChar 𝓀_L` internally — the Pass-31
`CharP`-transfer is not even consumed. (iv) Coefficient extraction redesigned around
`Polynomial.expand`: `(X − b̄)^{p^e·m} = expand (p^e) ((X − C b̄^{p^e})^m)` (freshman's dream +
`expand` ring-hom-ness), so `coeff_expand` + `coeff_X_add_C_pow` read off the
`X^{p^e(m−1)}`-coefficient as `−(b̄^{p^e})·m` — no binomial sums, no `Finset.sum_eq_single`.

## Environment incident (governs future sessions) + the module-probe recipe

The handoff's verified hybrid-workspace recipe was **infeasible this session**: the `/sessions`
volume (9.8 G) was 99 % full with the *same-day* dead workspaces of the P25–35 sessions
(unreclaimable from inside the VM — owned by `nobody`), the root volume had 2.3 G free, no
root/sudo. Worse, the full library closure is irreducible: the project's union import closure
is the whole of Mathlib (8392 modules, 5.31 G of artifacts) regardless of import-narrowing —
three early files bare-`import Mathlib`, and even without them the union closure is full.
**Future sessions: check `df` on `/sessions` at start; dead session dirs from the same day eat
the volume; ~7 G free is the bar for the full recipe.**

What replaced it — a **module-probe environment** (new, verified, ~2.5 G total, sub-second
iterations; worth reusing even when disk is plentiful):

- Toolchain: extract via `zstd -dc <tarball> | tar -x` with `--exclude='*.a'`
  `--exclude='*libLLVM*'` etc.; delete `src/`, all bins except `bin/lean`, all `*.ilean` /
  `*.olean.server` — and **all toolchain `*.olean.private`** (1.2 G!) — but **keep/restore
  `*.ir`** (the interpreter IR: `module`-style imports demand it; "missing data file" errors
  name the module whose `.ir` is absent).
- Packages: copy **only `.olean` (publics) + `.ir`** of the needed Mathlib import closure
  (computed by a BFS over sources whose regex must handle `public import`, `meta import`,
  `import all`), plus `.olean.private` + `.ir` of the small dep packages
  (batteries/aesop/Qq/…, 179 MB). Mathlib privates (proof bodies) are NOT needed.
- Probe files start with the `module` keyword (loads public interfaces only — this is what
  makes the privates unnecessary), invoked as plain `lean` with a hand-set `LEAN_PATH` — no
  `lake`, hence no traces, no FUSE fd-cap exposure, no 30 s olean tax: **probe runs were
  0.4–1.0 s.**

In this environment the pass's mathematics was **kernel-verified in-sandbox before the file
ever met the project context**: `probe_engine` = the ENTIRE main proof with the Pass-35 bricks
abstracted as hypotheses (`P : 𝒪 → 𝒪[X]`, `hP1`/`hP2` with the bricks' exact statement shapes),
plus the lemma-B skeleton (`probe_cover`), the `key` rewrite chain, the `m^{q−2}` division, the
Frobenius surjectivity, and every individual Mathlib step — all standard-axioms-only. The
committed file then differed from kernel-checked code only by substituting the concrete project
names. The full `lake build` (which the sandbox cannot hold) ran on the host: **green on the
first try** — the abstract-probe methodology works. Two warning-clean follow-ups (below), both
host-rebuilt.

## What was built

Per the ledger: `map_residue_inertiaFixedIntegers_eq_top` (`F = 𝓀_L`),
`inertiaFixedIntegers_residue_cover` (`hresid` verbatim), and
`ker_tameCharacter_extensionIntegers_general` (the finale, a term-mode one-liner: Pass 34 +
`hresid`). Root import added.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the Pass-35 sketch's cyclic-generator argument | unnecessary — iterated-Frobenius surjectivity closes `F = 𝓀_L` directly (the sketch's own "or argue via the Frobenius automorphism" was the better route) | probe before committing to a plan's combinatorics |
| `sub_pow_char_pow`, `Nat.ord_proj`/`ord_compl` | renamed/superseded: `sub_pow_expChar_pow_of_commute` (ExpChar drift), `Nat.exists_eq_pow_mul_and_not_dvd` (the exact decomposition, one `obtain`) | the pin is newer than priors — grep everything |
| binomial-sum coefficient extraction | `Polynomial.expand` + `coeff_expand` + `coeff_X_add_C_pow` — three rewrites, no sums | Mathlib's `expand` API is precisely the freshman's-dream bookkeeping |
| in-sandbox build per the handoff recipe | volume dead (same-day sessions' corpses); invented the module-probe env; host ran the real build, green first try | kernel-verify the mathematics abstractly when the project context won't fit |
| `[Fintype G₀]` hypothesis style (P33–35 precedent) | `unusedFintypeInType` linter: the types never mention cardinality — `[Finite G₀]` + proof-local `Fintype.ofFinite` is correct; P35's bricks keep `Fintype` legitimately (their *types* mention `charpoly`/`card`) | the linter caught a real style debt the precedent files masked |

## Build + headline

Host `lake build` green (8514 jobs), warning-clean after two follow-ups (the `Finite`/`Fintype`
refinement; one long docstring line); all three audits standard-only; zero `axiom` declarations
project-wide. **HEADLINE: `hresid` is a theorem and the descent closes — `ker θ₀ = G₁`
unconditionally, for every finite separable extension of nonarchimedean local fields. Serre IV
§2 Prop. 7 (level 0), general case, on actual local fields, axiom-free. The descent block
(Passes 29–36): eight rungs, zero axioms.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 37

(a) The Pass-27/28 instantiations at `𝒪_L` (additive-character kernels, the wild Sylow
statement — near-one-liners on the Pass-33 pattern, consolidation); (b) the
`IsNonarchimedeanLocalField L` instance assembly; (c) the **ascent**: Herbrand `φ`/`ψ`, upper
numbering (Serre IV §3), now with the complete finite-level floor under it. Honest frame:
R1–R3 distant as ever; what is *done* is the lower-numbering chapter of L2 on actual local
fields, in full generality.

## Post-pass addendum (same session) — the VM session-volume reset, verified (host ops)

The dead-session disk problem was fixed host-side after the pass; recording the procedure
because it WILL recur (every completed session leaves its workspace on the session volume
until a reset):

- The session volume (`/sessions`, ~9.8 G) is **`sessiondata.img`** inside
  `~/Library/Application Support/Claude/vm_bundles/claudevm.bundle`; the VM's root disk is
  `rootfs.img` (this is where `/var/tmp` probe environments live). **An app restart does NOT
  garbage-collect dead session dirs** — the VM and both disks persist across app restarts —
  and deleting conversations in the sidebar frees nothing either (dirs from four days prior
  were still present).
- Deleting `sessiondata.img` alone (app quit) was tried first, but the in-flight session's
  shell bridge never reconnected, so whether the app recreates that image standalone is
  unconfirmed. **Deleting the entire `claudevm.bundle` (app fully quit, ⌘Q) is the verified
  reset**: on relaunch the app re-provisions the whole VM, `/sessions` came back with 9.3 G
  free, and even the running conversation's shell reconnected cleanly to the fresh VM.
- Cost: a bundle reset wipes `rootfs.img`, i.e. any module-probe environment — rebuild from
  the recipe above (~15 min of calls).
- Unchanged on the fresh VM (so it is the mount layer's policy, not stale state): the repo
  mount denies `unlink` — file creation works, deletion fails with EPERM — so **`git commit`
  from the sandbox is impossible** (lock-file cycling) and commits remain host-side. Check at
  session start with `touch .unlinktest && rm .unlinktest` in the repo (if `rm` fails, the
  leftover shows up in `git status`, which the clean-tree check will catch — have the host
  remove it).

---

# Pass 37 — consolidation: the P27/P28 quotient theory concrete at `𝒪_L` (2026-06-10)

## Restatement (i)–(iv), pre-search

(i) User-approved (queue option (a)): instantiate the remaining abstract theorems at `𝒪_L` in
the now-general case. (ii) Honest scope: near-one-liners on the P33/P36 pattern; one file,
five thin theorems; the only "design" is the packaging. (iii) The feeder decision: factor the
general monogenicity statement (`Subring.closure ((inertiaFixedIntegers ∪ {π})) = ⊤`) as a
standalone theorem once, rather than re-deriving it inside each instantiation — it is the
single input every P27/P28 statement shares, and it is a headline in its own right. (iv) The
inputs inventory, all named priors: `hgen` = P34 engine + P36 cover; `hfix` at level `i`
descends from level 0 along `ramificationGroup_antitone` (subtype repackaging, one lambda);
`hsep` = the P23 Krull idiom (`Ideal.iInf_pow_eq_bot_of_isLocalRing` + P29 Noetherian);
`CharP 𝓀_L p` = P31's transfer (consumed for the first time); finiteness = P29's
decomposition-subgroup `instance` + subtype synthesis — **no `Finite`/`Fintype` hypotheses on
any statement**.

## What was built

Per the ledger: `Anabelian/ExtensionWildTame.lean` — the general monogenicity feeder, the two
P27 instantiations (`ker θ_i = G_{i+1}`, `G_i/G_{i+1} ↪ 𝓀_L⁺`, `i ≥ 1`), the two P28
instantiations (`G₁` a `p`-group, `p ∤ |G₀/G₁|`). Root import added.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| pure composition, no friction | one real miss: the descent chain never imports the abstract P27/P28 files (`AdditiveCharacter`, `WildInertia`) — first host build failed on unknown identifiers; two import lines fixed it | "in the root" ≠ "in the chain": check the import graph of the *new file's* chain, not the project's |
| `[Finite ↥G₀]`-style hypotheses needed (P35/P36 precedent) | none needed anywhere — P29's decomposition-subgroup `instance` + subtype synthesis covers every finiteness demand; the feeder audited clean on the first build | the P35/P36 `[Fintype/Finite G₀]` hypotheses were already synthesizable — candidate cleanup pass, low priority |
| `hsep` available concrete somewhere | only the ramification-level infimum was packaged (P29); the ideal-level form is re-derived inline by the P23 idiom, verbatim | the abstract/concrete seam is exactly one idiom wide |
| binder-order risk on abstract heads | all five bodies elaborated on the first build that could see the imports | source-read signatures + verbatim-idiom reuse is reliable; no probe environment was needed for this pass |

## Build + headline

Host `lake build` green (8515 jobs), warning-clean, second attempt (import fix only); all five
audits standard-only; zero `axiom` declarations project-wide. **HEADLINE: Serre IV §§1–2 at
finite level is complete and unconditional on actual local fields — filtration, tame
character `θ₀` with `ker θ₀ = G₁`, additive characters `θ_i` with `ker θ_i = G_{i+1}` and
`G_i/G_{i+1} ↪ 𝓀_L⁺`, and `G₁` = the normal Sylow `p`-subgroup of `G₀` — for every finite
separable extension of nonarchimedean local fields, zero conditional hypotheses, zero
axioms.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 38

(a) The `IsNonarchimedeanLocalField L` instance assembly — `L` itself a local field, enabling
iteration up towers (`M/L/K`); plumbing-heavy, topology friction possible; (b) the **ascent**:
Herbrand `φ`/`ψ` and upper numbering (Serre IV §3) — the next mathematical chapter, toward
statements about the absolute group. Honest frame: R1–R3 distant; the finite-level
lower-numbering theory is a closed book on actual local fields, and the project's next
genuinely new mathematics is the ascent.

---

# Pass 38 — the assembly, rung 1: the valuative structure on `L` (2026-06-11)

## Restatement (i)–(iv), pre-search

(i) User-delegated scope decision, taken: the **assembly** before the ascent — because
Herbrand's theorem (the ascent's centerpiece and R1's eventual input) quantifies over
intermediate extensions `L/L'/K`, which requires intermediate fields as *base* fields;
ascent-first would strand a half-chapter at exactly the theorem that gives upper numbering its
point. (ii) Honest scope: rung 1 of a 2–3-rung sub-block — the valuative structure and the
cheap parents; local compactness deferred. (iii) Inventory verdicts: Mathlib's
`IsNonarchimedeanLocalField` is three parents (`IsValuativeTopology` + `LocallyCompactSpace` +
`IsNontrivial`) over `[Field] [ValuativeRel] [TopologicalSpace]`, everything else derived;
**no finite-extension instance upstream** (the class's only mention in all of Mathlib is its
defining file); no `ValuativeRel` on extensions upstream (`Valuation/Extension.lean` is
relational — `IsValExtension`-style — not constructive). (iv) Design, D2-governed: `def`s +
`letI` discharge, **no global instances** — `extensionValuativeRel` depends on the base `K`,
and for towers the relations from different bases agree only up to a base-independence theorem
(named canonicity obligation, future pass); Mathlib's own `ValuativeRel.topologicalSpace` is a
`local instance` "to avoid diamonds", blessing exactly this pattern.

## Environment

Probe environment rebuilt from the Pass-36 recipe at the new scratch (post-reset `/sessions`,
9.3 G free): **three calls** — toolchain (822 M after trim, `.ir` kept from the start this
time), closure for the ValuativeRel/LocalField seed set (2342 modules, 0.62 G publics+ir),
deps' privates+ir. All three substantive proofs of the pass were **kernel-verified in-sandbox
before the file existed**: the nontriviality bridge, the concrete leg (generic over any
`ValuationSubring` with a uniformizer — so the committed file is again name-substitution from
checked code), and the free-parent smoke test. Probe runs 0.5–1.0 s.

## What was built

Per the ledger: `Anabelian/ExtensionLocalField.lean` — `extensionValuativeRel` (the relation
on `L` from `𝒪_L`'s valuation), `isNontrivial_ofValuation` (reusable bridge),
`isNontrivial_extensionValuativeRel` (parent 3 discharged via the Pass-30 uniformizer),
`isValuativeTopology_extensionValuativeRel` (parent 1, free upstream). Root import added.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| assembly = heavy plumbing, "topology friction possible" | the class has exactly three parents and Mathlib's valuative-topology layer hands over `IsValuativeTopology` + `NonarchimedeanRing` for free under its blessed local instance | the friction concentrates entirely in `LocallyCompactSpace` — rung 2 is the whole fight |
| a diamond-design dilemma to resolve ourselves | Mathlib's own comment ("not made into a global instance to avoid diamonds") prescribes the `def` + by-hand pattern | upstream and house discipline (D2) agree; no novel design needed |
| `valuation_eq_zero_iff` to land on `x = 0` | it lands on the *relation* (`x ≤ᵥ 0`) — one extra hop through `vle_iff_le` + `le_zero_iff` | the probe env caught it in one 0.9 s iteration; cost ≈ zero |
| concrete-leg friction at the subring valuation | `ValuationSubring.valuation_lt_one_iff` + `Valuation.ne_zero_iff` + `exact_mod_cast` — first try | the generic-over-`ValuationSubring` probe shape is the right de-risking unit |
| a plain `def` of class type to be fine | linter: definitions of class type must be `@[reducible]`/`@[implicit_reducible]` (else TC/unification can't see through the wrapper) — upstream `ofValuation` carries the attribute for the same reason | one-attribute fix; the probe env can't catch lake-level linters, only elaboration |

## Build + headline

Host `lake build` green, warning-clean; all four audits standard-only; zero `axiom`
declarations project-wide. **HEADLINE: the assembly is open and two of the three parents of
`IsNonarchimedeanLocalField L` are discharged — the valuative relation on `L` exists
(canonically from `𝒪_L`, instance-free by design), its topology is valuative, and it is
nontrivial. The assembly now hangs on exactly one parent: local compactness.** R1–R3
untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 39

**`LocallyCompactSpace L`** — the heavy parent: the finite-dimensional route (L ≅ Kⁿ as
topological `K`-vector spaces; `K` locally compact + complete ⟹ `L` locally compact) over the
Pass-17 normed bridge (`Valued.toNontriviallyNormedField`, the P29 idiom at ExtensionIntegers
lines 119–125) — inventory Mathlib's finite-dimensional TVS/locally-compact lemmas first, and
mind that the normed topology must be *identified* with the valuative topology of rung 1 (the
predicted friction point). Then the assembly theorem `IsNonarchimedeanLocalField L` itself.
Later: base-independence (the canonicity obligation) when towers arrive. Honest frame: R1–R3
distant; the assembly is infrastructure for the ascent, and the ascent is where the next real
mathematics lives.

---

# Pass 39 — the assembly, rung 2: the `Valued` framework on `L` (2026-06-11)

## Restatement (i)–(iv), pre-search

(i) User-approved: continue the assembly — the local-compactness fight. (ii) Honest scope as
re-planned mid-inventory: the fight decomposed far better than the Pass-38 pointer predicted —
this rung delivers the `Valued` framework + two of three compactness conjuncts; completeness
and the assembly are the next rung. (iii) Three successive inventory discoveries reshaped the
route, each strictly shrinking it: (1) `LocallyCompactSpace.of_finiteDimensional_of_complete`
exists upstream and needs no T2 (it quotients internally) — but better, (2) Mathlib's
`Valued/LocallyCompact.lean` has the **`Valued`-native characterization**
`CompactSpace 𝒪 ↔ CompleteSpace 𝒪 ∧ IsDiscreteValuationRing 𝒪 ∧ Finite 𝓀` — and best, (3)
Mathlib's porting-helper instance (`Topology/Algebra/Valued/ValuativeRel.lean`) makes `L`
`Valued` **on the rung-1 structures, adopting the given uniformity** — `Valued.v = valuation L`
is `rfl`, so the feared topology-identification seam *does not exist*. The f.d.-TVS route and
the spectral identification both became unnecessary for this rung; the spectral norm is
deferred to exactly one place — the completeness conjunct (Pass 40). (iv) The integer-ring
identity is pure rung-1 bookkeeping: `Valued`-integers `= {valuation L ≤ 1}` `= 𝒪_L` via
`Compatible.vle_iff_le` + `valuation_le_one_iff`; the other two conjuncts are transports of
P30/P31 along that subring equality.

## What was built

Per the ledger: `Anabelian/ExtensionValued.lean` — the abstract integer-ring identity, the two
abstract transports (`RingEquiv.subringCongr` + the nested-name DVR transport +
`ResidueField.mapEquiv`), and the concrete trio under the rung-1 `letI`-tower. Root import
added.

## Pre-search expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the normed/valuative topology identification to be the pass's hard center | the porting-helper `Valued` instance adopts the given uniformity — the seam is `rfl` | inventory before fighting: the predicted battle was already won upstream |
| spectral-norm content throughout | zero spectral content in the entire rung; it survives only in the completeness conjunct | route shrinkage is real progress even when no theorem is "hard" |
| `Valued.integer` / `subringCongr` / DVR-transport names | `Valuation.integer` via `Valued.v`; `RingEquiv.subringCongr`; the DVR transport is the *nested* `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing` | namespace nesting is a probe-catchable failure class (two 0.5 s iterations) |
| `vle_iff_le` applied-form friction | `(... x 1).symm.trans (... x 1)` — explicit binders, one fix | same |
| the `letI`-tower to fight instance resolution | `probe_chain` (the full tower, abstractly) fired first try | the helper instance's design is exactly compatible with the rung-1 `def`-discipline |
| the P37 import-chain lesson to be learned | repeated it: P31's file absent from the new chain (P30's present), one host round-trip — while both *flagged* risks (the `↥`-defeq hops) passed | the discipline must be mechanical: before host hand-off, grep every project name in the new file against its transitive chain — added to the pass ritual below |

All five substantive pieces were kernel-verified in-sandbox (probe runs 0.5–0.7 s) before the
file existed; the committed file is name-substitution from checked code. The probe environment
was extended with the analysis closure (+6117 modules, 1.33 GB) in two rsync calls.

## Build + headline

Host `lake build` green, warning-clean; all six audits standard-only; zero `axiom`
declarations project-wide. **HEADLINE: `L` is a `Valued` field on the rung-1 structures with
integer ring `𝒪_L`, a DVR with finite residue field — the compactness criterion is two-thirds
discharged, with no topology identification anywhere and no spectral content yet. The assembly
hangs on the completeness conjunct.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 40

The completeness conjunct: `CompleteSpace ↥((Valued.v).integer)` under the rung-1 tower —
either via `CompleteSpace L` (the spectral seam at last: spectral norm complete for f.d. `L/K`,
+ closed-subring) or via the 𝔪-adic route (`Module.Finite` over the adically-complete `𝒪[K]`,
P34's `exists_pow_maximalIdeal_le_map` giving adic-topology agreement) — inventory both, take
the cheaper. Then: `CompactSpace` via the criterion's `.mpr`, the integers as a 𝓝0-neighborhood
(`is_topological_valuation` at `γ = 1`), `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup`,
and the **assembly theorem `IsNonarchimedeanLocalField L`** — parents 1–3 + local compactness.
Honest frame: one rung from the assembly closing; R1–R3 distant as ever.

---

# Pass 40 — the assembly, rung 3: the spectral seam, crossed as equalities (2026-06-11)

## Restatement + what was built

(i) User-approved (emphatically): continue in-session per the freshly committed HANDOFF.md.
(ii)–(iv) The handoff's own plan, executed as written: the keystone pair committed
(`ofValuation_congr` — the class is `@[ext]`, so equivalent valuations give *equal* relations —
and `ofValuation_eq_of_same_subring`), P29's internal `hmem` exported verbatim
(`𝒪_L` = the spectral unit ball; same `maxHeartbeats` raise, same reason), hence
**`extensionValuativeRel K L = ofValuation (spectral Valued.v)`** — the seam is an equality;
`CompleteSpace L` proved spectrally (`spectralNorm.normedSpace` + `FiniteDimensional.complete`);
and the uniformity-uniqueness brick (`uniformSpace_eq_of_isUniformAddGroup`, via
`uniformity_eq_comap_nhds_zero` with the `IsRightUniformAddGroup` refinement instance-derived)
ready for the transfer. Files: `ValuativeRelCongr.lean` (abstract trio),
`ExtensionSpectralSeam.lean` (concrete trio). Root imports added.

## Expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| `seminormedAddCommGroup`-keying friction at `spectralNorm.normedSpace` + `FiniteDimensional.complete` | the chain fired first probe, zero friction | the dFF spectral API is internally coherent under `letI` |
| `uniformity_eq_comap_nhds_zero` keyed to `IsUniformAddGroup` | keyed to `IsRightUniformAddGroup`; the comm-group bridge is the instance `IsUniformAddGroup.isRightUniformAddGroup` | one probe iteration |
| the P29 `hmem` copy to be the risky part | verbatim copy of host-verified code; the probes covered everything else | copying verified code is the *lowest*-risk move available |
| (post-build) clean | 13 `unusedVariables` warnings: I had NAMED the `letI` binders in the STATEMENT-level blocks (`letI rk : ... :=`) — names nothing can reference — and my probe run showed these very warnings, which I filtered with `grep -v` instead of reading | **never filter probe warnings** — they are signal; statement binders are anonymous (`letI : T := ...`); and the gate is now mechanical: `scripts/preflight.sh` |

**Process hardening (user-requested, committed this pass): `scripts/preflight.sh`** — the
pre-commit gate: long-line check, named-statement-binder check, `scripts/chain_check.py` (the
P37/P39 import-chain class, now comment-stripping so docstring prose and forward references
don't false-positive — validates clean on all 43 files), and a full `lake build` failing on ANY
warning. A pass is committable only if preflight exits 0; the sandbox runs the static checks
pre-handoff, the host run is authoritative.

All novel content kernel-verified in-sandbox pre-file (probe runs 0.5–0.7 s; env from P38–39
reused warm). The chain-checker ran clean on both files before hand-off.

## Build + headline

Host `lake build` green, warning-clean; all six audits standard-only; zero `axiom`
declarations project-wide. **HEADLINE: the spectral seam is crossed as equalities — the rung-1
relation literally equals the spectral relation, `L` is spectrally complete, and the
uniformity-uniqueness brick is in place. All three conjuncts of the compactness criterion are
now proved on one side of the seam or the other.** R1–R3 untouched.

## Ledger delta

- **0 / 0.** Axiom-free.

## Scope: pointer to Pass 41 (the assembly closes)

(1) The `IsValuativeTopology`-uniqueness lemma: two topologies valuative for the same relation
are equal (`TopologicalSpace.ext_nhds` + `IsValuativeTopology.mem_nhds_iff` on both sides) —
with it, rung-1 topology = spectral topology (the relations being EQUAL), hence rung-1
uniformity = metric uniformity (`uniformSpace_eq_of_isUniformAddGroup`), hence
`CompleteSpace L` on the tower; (2) the integer ring closed (`Valuation.integer` is a closed
unit ball) ⟹ `CompleteSpace 𝒪`; (3) the criterion's `.mpr` ⟹ `CompactSpace 𝒪`; (4) the
integers are a `𝓝 0`-neighborhood (`is_topological_valuation` at `γ = 1`) +
`IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup` ⟹ `LocallyCompactSpace L`; (5)
**`IsNonarchimedeanLocalField L`** — the assembly theorem, closing the block opened at
Pass 38. Then: the canonicity obligation, then the ascent.

---

# Pass 41 — the assembly closes: `IsNonarchimedeanLocalField L` (2026-06-24)

## Restatement + what was built

Returning to the project after a break; user reviewed the recent passes and greenlit Pass 41 (the
assembly capstone). **One file, `Anabelian/ExtensionLocalFieldInstance.lean`**, three theorems:

- **`isValuativeTopology_unique`** (abstract, reusable): two topologies on a `CommRing` that are
  both valuative for the *same* `ValuativeRel` are equal. `IsValuativeTopology.mem_nhds_iff`
  characterizes `s ∈ 𝓝 x` by the relation alone (RHS topology-independent), so the nhds filters
  agree pointwise — `TopologicalSpace.ext_nhds` + `Filter.ext`. A two-line proof; the clean
  formalization of the NOTES-plan "step 1".
- **`locallyCompactSpace_extensionValuativeRel`** (parent 2): `L` is locally compact in its
  rung-1 valuative topology.
- **`isNonarchimedeanLocalField_extension`** (the capstone): assembles the three parents.

## The route I actually took (and why it diverged from the Pass-40 pointer)

The Pass-40 pointer planned the **compactness-criterion** route: complete `𝒪` on the rung-1
tower (transfer `completeSpace_spectral` across the uniformity via
`uniformSpace_eq_of_isUniformAddGroup`), `CompactSpace` via the criterion `.mpr`, then
`LocallyCompactSpace`. During inventory I found a **shorter, more conceptual** route for the bare
`LocallyCompactSpace`: `L` is a finite-dimensional normed space over `K`, and `K` is a local
field hence proper (`ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`, exactly
as Mathlib's own `LocalField/Basic.lean:163` does), so **`FiniteDimensional.proper K L : ProperSpace L`**
and `ProperSpace → LocallyCompactSpace` is an instance. This bypasses the criterion, DVR, finite
residue, RankOne, and the completeness transfer entirely. The topology identification (rung-1 =
spectral) is still required — to transport `LocallyCompactSpace` from the spectral topology to the
rung-1 topology — and is the genuine crux, but the abstract `isValuativeTopology_unique` brick +
P40's `extensionValuativeRel_eq_spectral` made it clean. The criterion route is **not wasted**:
P39–40's DVR/finite/completeness are real local-field structure (and Mathlib re-derives them *from*
the assembled class for free).

## Expectation vs. reality

| I expected | Reality | Verdict |
|------------|---------|---------|
| the compactness-criterion route (NOTES-plan) | `FiniteDimensional.proper` gives `LocallyCompactSpace` far more directly; criterion superseded for the assembly | inventory before executing a stale plan; the conceptual proof was shorter |
| spectral side `IsValuativeTopology` to be a grind | `IsValuativeTopology.of_zero` + `Valued.mem_nhds_zero` + `exists_setOf_restrict_le_iff` (with ambient relation set to `ofValuation Valued.v`, then `rw` the P40 equality) — one `simpa` | the `exists_setOf_restrict_le_iff` API is exactly the needed bridge |
| `@IsValuativeTopology R _ t` to typecheck | wrong arity: the class takes `[CommRing][ValuativeRel][TopologicalSpace]`, so `@... R _ _ t` — `t` was landing in the `ValuativeRel` slot | one underscore; trivial once the error named it |
| post-build warnings | exactly two style-linter warnings (maxHeartbeats comment; an unnecessary `show`) — both real, both fixed; preflight then CLEAN | the gate works; named binders (`letI rk :` etc., 2-space tactic level) did NOT warn |

## Build + headline

Host `lake build` green; `scripts/preflight.sh` CLEAN (8520 jobs, 44 files chain-checked, zero
warnings). All three `#print axioms` standard-only; zero `axiom` declarations project-wide.
**HEADLINE: the assembly opened at Pass 38 is COMPLETE — `IsNonarchimedeanLocalField L` for every
finite separable extension `L/K` of nonarchimedean local fields, axiom-free.** The gate to towers
`M/L/K` and the ascent (Herbrand, upper numbering) is open. R1–R3 untouched and distant as ever.

## Ledger delta

- **0 / 0.** Axiom-free. No new `structure`/`class`; no owed witness; D1 N/A; D2 intact.

## Scope: pointer to Pass 42 (the canonicity obligation, then the ascent)

(1) **The canonicity obligation** — `extensionValuativeRel` is a `def`, not an instance, because
for a tower `M/L/K` the relation on `L` built from base `K` must agree with the one built from an
intermediate base; this base-independence is the named obligation deferred since Pass 38. It must
be discharged before the theory iterates up towers. Likely shape: the relation depends only on the
integral closure `𝒪_L`, which is base-independent (`integralClosure` is transitive); state and
prove `extensionValuativeRel K L = extensionValuativeRel K' L` for `K ⊆ K' ⊆ L`. (2) Then the
**ascent**: Herbrand's `φ`/`ψ` functions and the upper numbering `G^v(L/K)` (Serre IV §3), which
the assembly was built to enable — intermediate fields can now serve as base fields carrying the
full `IsNonarchimedeanLocalField` structure, making the quotient-compatibility (Herbrand's
theorem) statable. R1–R3 remain the distant, must-be-earned targets.

### Pass 42 (2026-06-24) — governance/cleanup: orphan discard, R1-floor deferred, clean-tree gate

**No mathematics; ledger delta 0 / 0.** A governance pass, triggered by the session-start
clean-tree check (`CLAUDE.md`) finding the working tree dirty: two untracked files orphaned since
2026-06-12 that the Pass-41 commit (2026-06-24) had passed over without resolving. This is a
recurrence — smaller but more dangerous — of the 2026-05-31 orphan pattern the clean-tree rule
exists to stop. Resolved this pass; the rule is now mechanically backstopped so it cannot recur.

**The orphans found:**
1. `Anabelian/Reconstruction/Inputs.lean` (created 2026-06-12 17:43; untracked; **not imported,
   not in `Anabelian.lean`, not in any commit, not in `AXIOM_LEDGER.md`**). It introduced **two
   `FOUNDATIONAL` axioms** for a "conditional R1-floor program" — i.e. a jump past L2/L3/L4 to a
   conditional R1 reconstruction result, powered by axiomatized local class field theory. The
   committed ledger said `0 / 0` while the tree carried 2 axioms: the exact contradiction
   (`CLAUDE.md`: "the working tree must never silently contradict the ledger") the discipline
   forbids. Because the file was never wired into the build, **no axiom ever entered the kernel** —
   the committed `#print axioms` audits remain honestly standard-only — but as live-but-invisible
   work it had to be resolved, not tolerated.
2. `scripts/refactor.sh` (created 2026-06-12 17:22; untracked; never run — the `Anabelian/` tree is
   still flat at 44 files). A well-formed one-shot flat→folders structural refactor.

**Decision (user, this session): cleanup-only.** The R1-floor direction was **not** adopted; the
canonicity-then-ascent ROADMAP course stands. Dispositions:
- **`Inputs.lean`: DISCARDED** (host-side `rm`; the sandbox mount denies unlink). Following the
  pre-Pass-25 precedent (discard + incident note), its content is preserved **here** so a future
  *deliberate* R1-floor decision can re-derive it cheaply rather than re-discover it blind. The two
  axioms, verbatim, were:
  - **A1 `localReciprocity_abelianization`** (FOUNDATIONAL, L3): for `K/ℚ_p` finite,
    `Nonempty (Field.absoluteGaloisGroupAbelianization K ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ))`
    — local reciprocity, abelianized (`G_K^ab ≅ Kˣ^`). Cite Neukirch ANT V; Serre LF XIV;
    Cassels–Fröhlich VI. Discharge path: de Frutos-Fernández's external `LocalClassFieldTheory`.
  - **A2 `padicUnitGroup_structure`** (FOUNDATIONAL, L1/L3): for `K/ℚ_p` finite of degree `d`,
    `∃ q a, 1 < q ∧ ¬ p ∣ (q-1) ∧ Nonempty (Kˣ ≃* Multiplicative (ℤ × ZMod (q-1) × ZMod (p^a) × (Fin d → ℤ_[p])))`
    — the `Kˣ` structure theorem. Cite Neukirch II.5.3 + II.5.7. (The author deferred identifying
    the existential `q` with `|𝓀_K|`.)
- **Why deferred, not adopted (the substantive call).** Axiomatizing L3 *is* ROADMAP-permitted as a
  `FOUNDATIONAL` input for R1, so this is not the cardinal sin per se. But: (i) it was done
  **unledgered and uncommitted** — process-invalid regardless of content; (ii) it would take the
  ledger `0 → 2 FOUNDATIONAL` in one move, the breadth-without-depth / FOUNDATIONAL-stacking trap the
  project disciplined against across Passes 6–20; (iii) **cardinal-sin proximity**: A1 + A2 together
  nearly *hand you* the residue data of `K` from `G_K^ab` (read `q−1`'s prime-to-`p` part off the
  abelianization), and "recover `q` from `G_K^ab`" is a named R1 target — so a conditional R1 theorem
  on these inputs risks being a disguised rule-5 violation (an axiom that trivially implies the
  target). The author's deferral of the `q = |𝓀_K|` identification is the fig leaf that keeps it on
  the right side of the line; that very deferral shows the line was felt. **If/when the R1-floor is
  taken, it must be a deliberate, ledgered decision** with a ROADMAP R1-spine section AND a proof the
  conditional result does not trivially imply R1 — never something backed into via an untracked file.
- **`refactor.sh`: TRACKED, NOT RUN.** Committed as an available maintenance tool (alongside
  `preflight.sh`/`chain_check.py`); running it (a 44-file `git mv` + import rewrite) belongs in its
  own dedicated pass with a host-side `lake build` to verify — mixing it into a governance commit
  would make the diff unreviewable. The flat `Anabelian/` dir is a real smell; the refactor is the
  fix, deferred to its own verified pass.

**Mechanical fix so this cannot recur.** `scripts/preflight.sh` gains **clause 0**: the pre-commit
gate now fails on any untracked file outside `.gitignore` (`git ls-files --others --exclude-standard`).
Had this existed, the Pass-41 commit would have failed until the orphans were resolved. `.claude/`
(local settings, expected-untracked per HANDOFF) is added to `.gitignore` so it is no longer flagged.
The prose clean-tree rule failed twice (2026-05-31, 2026-06-12) precisely because nothing enforced
it; clause 0 is the enforcement. `CLAUDE.md`'s rule text now points at it.

**Tree after this pass (host-side, user-run):** `rm Anabelian/Reconstruction/Inputs.lean`, remove the
empty `Anabelian/Reconstruction/` dir, `rm _probe_test_5` (a stray probe file this session created in
the mount and could not unlink), `git add scripts/refactor.sh` + the governance/script edits, then
`scripts/preflight.sh` must exit 0 (clause 0 now clean), then commit + push.

**Ledger delta: 0 / 0.** No axiom entered the build at any point. No new `structure`/`class`; no owed
witness; D1/D2 untouched. **Next math pass (Pass 43): the canonicity obligation** (base-independence
of `extensionValuativeRel` across towers — `integralClosure` transitivity), then the ascent
(Herbrand `φ`/`ψ`, upper numbering, Serre IV §3).

### Pass 43 (2026-06-24) — the canonicity obligation DISCHARGED: `extensionValuativeRel` base-independent across towers

**Mathematics; ledger delta 0 / 0.** Discharged the obligation deferred since Pass 38 — the reason
`extensionValuativeRel K L` is a `def` and not an instance. For a tower `K ⊆ K' ⊆ L` of finite
separable extensions, the valuative relation on `L` built from the base `K` **equals** the one built
from the intermediate base `K'` (carrying its Pass-41 extension local-field structure). This was the
last L-rung prerequisite before the ascent: the theory can now iterate up towers with intermediate
fields as base fields. `Anabelian/ExtensionCanonical.lean`, four theorems, all standard-axioms-only.

## What was proved

The relation depends only on the integral closure `𝒪_L`, which is base-independent because
`integralClosure` is transitive. Two halves, then the assembly:

- **Self-consistency** (`integer_extensionValuativeRel_eq`): under `extensionValuativeRel K K'`, the
  integer ring `𝒪[K']` *is* `extensionIntegers K K'` (= integral closure of `𝒪[K]` in `K'`). Pure
  `Compatible` bookkeeping on the canonical valuation (`Valuation.Compatible.vle_iff_le` both ways +
  `mem_of_valuation_le_one`/`valuation_le_one`), the `K'`-analogue of Pass 39's
  `valued_integer_eq_of_compatible` without the `Valued` layer. Built axiom-clean already in the
  draft — the high-confidence anchor.
- **Transitivity** (`isIntegral_base_iff`): for `x : L`, `IsIntegral ↥𝒪[K] x ↔ IsIntegral
  ↥(extensionIntegers K K') x`. Forward = base enlargement (`IsIntegral.tower_top`); backward =
  `extensionIntegers K K'` is integral over `𝒪[K]` (`isIntegral_trans`). This is the engine and the
  only lemma the draft left broken (4 errors); see "How the draft was fixed" below.
- **Subring base-independence** (`extensionIntegers_base_independent`): `extensionIntegers K L =
  extensionIntegers K' L` as `ValuationSubring L`. `SetLike.ext` + `mem_extensionIntegers_iff` (which
  is `Iff.rfl`) reduces membership to `isIntegral_base_iff`, then the bridge `IsIntegral
  ↥(extensionIntegers K K') x ↔ IsIntegral ↥𝒪[K'] x` along self-consistency
  (`RingEquiv.isIntegral_iff (RingEquiv.subringCongr hSC.symm) (by ext b; rfl)` — the `ext b; rfl`
  compatibility went through unchanged once the engine compiled).
- **THE CANONICITY THEOREM** (`extensionValuativeRel_base_independent`): `extensionValuativeRel K L
  = extensionValuativeRel K' L`, by `congrArg (fun A => ofValuation A.valuation)` of the subring
  equality. Rests only on self-consistency + transitivity — not behind a hypothesis that gives it
  away.

## How the draft was fixed (the engine, `isIntegral_base_iff`)

The draft hand-rolled `letI algBL : Algebra ↥(extensionIntegers K K') L` and a fragile `rw` chain;
4 errors. The fix, verified empirically with the local toolchain (the prior agent had none) via
throwaway `lake env lean` probes before editing:

- **Mathlib provides `Algebra ↥(extensionIntegers K K') L` ambiently** (`Algebra.ofSubsemiring` —
  `extensionIntegers K K'` is a subring of `K'`, which acts on `L`), with `algebraMap … b =
  algebraMap K' L ↑b` by `rfl`. The hand-rolled `algBL` *conflicted* with it (the "synthesized
  instance not defeq" errors). **Deleted it; use the ambient one.**
- `IsScalarTower ↥𝒪[K] ↥(extensionIntegers K K') L` (and the `… → K'` tower) do **not** infer — built
  by hand with `IsScalarTower.of_algebraMap_eq`, both sides rewritten to a syntactically identical
  `algebraMap K _ ↑r` (probe-confirmed: `algebraMap ↥𝒪[K] K' r = algebraMap K K' ↑r` and `algebraMap
  ↥𝒪[K] L r = algebraMap K L ↑r` are both `rfl`; the seam is `hcoe`, the `extensionAlgebraMap`
  coercion via `coe_extensionAlgebraMap`).
- `Algebra.IsIntegral ↥𝒪[K] ↥(extensionIntegers K K')`: the elements are integral by
  `mem_extensionIntegers_iff`, but in `K'` — lifted to the subring by `isIntegral_algebraMap_iff
  Subtype.coe_injective` (needs the `… → K'` tower above).
- Lint: `isIntegral_base_iff` doesn't use `[FiniteDimensional K' L]` ⟹ `omit [FiniteDimensional K' L]
  in` (the `ExtensionIntegers.lean` precedent); the three goal-changing `show`s became `change` (the
  `linter.style.show` gate). Both caught by the host `lake build` warning-gate, invisible to the
  draft author.

## Mathlib API that did the real work

`IsIntegral.tower_top`, `isIntegral_trans` (integral-closure transitivity, `IsIntegralClosure/Basic`);
`isIntegral_algebraMap_iff` (reflect integrality through an injective algebra map); `RingEquiv.isIntegral_iff`
(transport along the self-consistency iso); `IsScalarTower.of_algebraMap_eq`; the ambient
`Algebra.ofSubsemiring` subring-algebra instance.

## Build + headline

Host `lake build` green; new file `Anabelian/ExtensionCanonical.lean` imported in `Anabelian.lean`;
`scripts/preflight.sh` CLEAN. All four `#print axioms` standard-only
(`[propext, Classical.choice, Quot.sound]`); zero `axiom` declarations project-wide.
**HEADLINE: `extensionValuativeRel K L = extensionValuativeRel K' L` for every tower `K ⊆ K' ⊆ L` of
finite separable extensions of nonarchimedean local fields — base-independence proved, axiom-free.**
Intermediate fields are now usable as base fields; the ascent is unblocked.

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (the four declarations are theorems; the only
  objects are existing Mathlib structures — `ValuationSubring`, `ValuativeRel`), so **no rule-2
  obligation**; **no owed witness** (no load-bearing-hypothesis come-apart is claimed — the tower
  hypotheses are what make the statement typecheck, not a separately-claimed essential hypothesis).
  D1 N/A; D2 untouched (no spectral structure in any statement — `mem_extensionIntegers_iff` is
  `Iff.rfl`). Recovers nothing from an abstract group; R1–R3 untouched and distant.

## Scope: the ascent (Pass 44)

With canonicity discharged the **ascent** is unblocked: Herbrand's `φ`/`ψ` functions and the upper
numbering `G^v(L/K)`, quotient-compatible (Serre IV §3) — the assembly was built precisely so that
intermediate fields carry the full `IsNonarchimedeanLocalField` structure, making Herbrand's quotient
theorem statable. Inventory Mathlib's ramification API (the L2 file carries a literal `TODO: Define
higher ramification` for `φ`/`ψ`) before writing. R1–R3 remain the distant, must-be-earned targets.

### Pass 44 (2026-06-24) — the ascent opens: the Herbrand function `φ` (Serre IV §3, rung 1)

**Mathematics; ledger delta 0 / 0.** Opened the **ascent** by constructing the Herbrand function
`φ` and proving its foundational analytic properties, all axiom-free. `Anabelian/HerbrandFunction.lean`,
18 declarations, all standard-axioms-only.

## Inventory (done first, per the rule — the absence is itself a deliverable)

`grep` over `.lake/packages/mathlib`: **`herbrand` = 0 hits, `upperRamification`/`upperNumbering` = 0
hits.** Mathlib's `RingTheory/Valuation/RamificationGroup.lean` defines only `decompositionSubgroup`
and `inertiaSubgroup` (`G_0`) and carries a literal `TODO: Define higher ramification groups in lower
numbering`. So the **entire** ascent — lower-numbering `G_i`, Herbrand `φ`/`ψ`, upper numbering — is
absent from Mathlib. The project's own lower-numbering filtration (`ramificationGroup`, Pass 23) is
the foundation; this pass builds `φ` on it.

## What was proved

Serre defines `φ(u) = ∫_0^u dt/(G_0 : G_t)`. We define it **literally as that integral**, split into:

- **An analytic engine** `herbrandPhiSeq (g : ℕ → ℝ)` on an abstract decreasing order-sequence
  (`g i = |G_i|`), and
- **the instantiation** `herbrandPhi K A := herbrandPhiSeq (fun i => Nat.card (ramificationGroup K A i))`.

This separation mirrors Serre: §3's lemmas are about the *function*; the *ramification* enters only
as "the filtration decreases". The enabling observation: the integrand `t ↦ g_{⌈t⌉}/g_0` is
**`Antitone`** (the groups shrink as the level rises), hence `IntervalIntegrable`
(`Antitone.intervalIntegrable`) — which makes every property a clean interval-integral fact:

- `herbrandPhi_zero`: `φ(0) = 0` (`integral_same`).
- **`herbrandPhi_strictMono`**: strictly increasing — integrand `> 0` (every `|G_i| ≥ 1`), via
  `intervalIntegral_pos_of_pos_on` + `integral_add_adjacent_intervals`.
- `herbrandPhi_monotone`: `Monotone` (corollary of StrictMono; also a standalone weaker-hypothesis
  proof for the abstract engine via `integral_nonneg`).
- **`herbrandPhi_continuous`**: `Continuous` (`continuous_primitive`).
- `herbrandPhi_eq_id`: `φ(u) = u` for `u ≤ 0` (Serre's `[-1,0]` normalisation — there the acting
  group is `G_0`, slope `(G_0:G_0)⁻¹ = 1`; `integral_congr` to the constant `1` + `integral_const`).
- `herbrandPhi_le_self`: `φ(u) ≤ u` for `u ≥ 0` — slopes `g_{⌈t⌉}/g_0 ≤ 1` because `G_t ≤ G_0`
  (`integral_mono_on` against the constant `1`). The genuine ramification content separating `φ`
  from the identity.

**StrictMono + Continuous are exactly what defining the inverse `ψ = φ⁻¹` needs** — the immediate
next rung.

## Why the integral definition (the design choice)

The two candidate encodings were (a) the explicit floor-based piecewise-linear formula and (b)
Serre's literal integral. (b) won: it is the most faithful to Serre, and — because the integrand is
antitone — Mathlib's interval-integral API delivers integrability, monotonicity, strict
monotonicity, AND continuity almost for free, where (a) would have needed a hand telescoping
argument for monotonicity and a manual kink-continuity proof. Verified empirically with the local
toolchain (`lake env lean` probes) before writing the project file.

## Mathlib API that did the real work

`intervalIntegral` (the def is a literal interval integral); `Antitone.intervalIntegrable`;
`intervalIntegral.integral_add_adjacent_intervals`, `integral_nonneg`,
`intervalIntegral.intervalIntegral_pos_of_pos_on` (mono/strictMono); `continuous_primitive`
(continuity); `integral_mono_on`, `integral_const`, `integral_congr` (the `id`-comparisons);
`Subgroup.card_le_of_le`, `Nat.card_pos`, `Nat.floor_mono` (the order sequence is positive +
decreasing, given `[Finite (A.decompositionSubgroup K)]`).

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN
(46 files chain-checked, 8522 jobs, zero warnings). All 18 `#print axioms` standard-only; zero
`axiom` declarations project-wide. **HEADLINE: the Herbrand function `φ` of Serre IV §3 — absent from
Mathlib — is constructed and shown strictly monotone, continuous, `φ(0)=0`, `φ=id` on `(-∞,0]`, and
`φ ≤ id` on `[0,∞)`, axiom-free, on the real ramification filtration.** The ascent is open.

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (the objects are `def`s of real functions) ⟹
  no rule-2 come-apart obligation. The instantiation's `[Finite (A.decompositionSubgroup K)]` is
  **automatic at the intended finite level** (`A = 𝒪_L`, `L/K` finite) and is needed only so the
  orders `|G_i|` are positive (else `Nat.card = 0` and `φ ≡ 0`) — a standing finiteness, **not** a
  claimed-essential hypothesis, so **no owed witness**. D1 N/A; D2 N/A (real analysis +
  `ramificationGroup`; no spectral/normed structure). Recovers nothing from an abstract group;
  R1–R3 untouched.

## Scope: the inverse `ψ` and the upper numbering (Pass 45)

`ψ = φ⁻¹` is reachable now (`φ` is StrictMono + Continuous; needs the range/surjectivity onto
`[-1,∞)` — `φ` is unbounded above since the slopes are `≥ 1/g_0 > 0` and the domain is unbounded —
giving a continuous strictly-monotone bijection, hence an inverse). Then the **upper numbering**
`G^v(L/K) = G_{ψ(v)}` and **Herbrand's theorem** (the upper numbering is compatible with quotients
`Gal(L/K) ↠ Gal(M/K)` — this is where the canonicity of Pass 43 and the tower theory earn their
keep). Also deferred: concavity, the explicit piecewise-linear formula, and the slope/derivative
`φ'(u) = 1/(G_0 : G_u)`. R1–R3 remain the distant, must-be-earned targets.

### Pass 45 (2026-06-24) — the ascent, rung 2: the inverse `ψ = φ⁻¹` and the upper numbering

**Mathematics; ledger delta 0 / 0.** Inverted `φ` and defined the upper numbering — both absent from
Mathlib, both axiom-free. `Anabelian/UpperNumbering.lean`, 21 declarations, all standard-axioms-only.

## What was proved

Pass 44 left `φ` strictly monotone + continuous. To invert it:

- **`φ` is surjective onto `ℝ`** (`herbrandPhiSeq_surjective`): continuous, `→ -∞` at `-∞` (it is
  `id` on `(-∞,0]`) and `→ +∞` at `+∞`. The latter needed a new **lower bound**
  `herbrandPhiSeq_div_le`: every order is `≥ 1`, so the integrand is `≥ 1/g_0`, so `φ(u) ≥ u/g_0`
  (the companion to Pass 44's `φ ≤ id`). Then `Continuous.surjective` from the two `Tendsto`s.
- **`ψ = φ⁻¹`** (`herbrandPsi`), defined proof-free via `Function.invFun` (so the def carries no
  hypotheses; the properties are theorems). Inverse identities `herbrandPhi_psi`/`herbrandPsi_phi`
  from `rightInverse_invFun`/`leftInverse_invFun`. `ψ` **strictly monotone** (inverts the strict
  `φ`, via `StrictMono.lt_iff_lt`), `ψ(0)=0`, `ψ=id` on `(-∞,0]`.
- **`ψ` continuous** — the one delicate proof: `φ` strict-mono + surjective ⟹ an order isomorphism
  `e : ℝ ≃o ℝ` (`StrictMono.orderIsoOfSurjective`, whose `coe` is `φ` by `rfl`), whose inverse is a
  homeomorphism (`OrderIso.toHomeomorph`); bridged `ψ = ⇑e.symm` by injectivity of `φ`
  (`orderIsoOfSurjective_self_symm_apply`), then `e.symm.toHomeomorph.continuous`.
- **The upper numbering** `G^v(L/K) := G_{⌈ψ(v)⌉}` (`upperRamificationGroup`): `G^0 = G_0` (inertia,
  since `ψ(0)=0` and `⌈0⌉₊=0`), **antitone in `v`** (`ψ` mono, `⌈·⌉₊` mono, filtration antitone),
  **eventually `⊥`** (some `G_i=⊥` by Pass 24; take `v = φ(i)`, then `⌈ψ(φ i)⌉₊ = ⌈i⌉₊ = i`, so
  `G^{φ(i)} = G_i = ⊥` — uses the inverse identity `ψ(φ i)=i`).

Like `φ`, `ψ` is an abstract engine `herbrandPsiSeq (g : ℕ → ℝ)` (hyp `1 ≤ g i`) then instantiated.

## Mathlib API that did the real work

`Continuous.surjective`, `tendsto_atTop_mono'`, `tendsto_id.atTop_div_const`, `Tendsto.congr'`
(surjectivity); `Function.invFun` + `rightInverse_invFun`/`leftInverse_invFun` (the inverse);
`StrictMono.orderIsoOfSurjective` (+`coe_orderIsoOfSurjective` (`rfl`),
`orderIsoOfSurjective_self_symm_apply`) + `OrderIso.toHomeomorph` (ψ continuity);
`intervalIntegral.integral_mono_on` (lower bound); `Nat.ceil_mono`, `Nat.ceil_natCast`,
`Nat.ceil_zero`, `exists_ramificationGroup_eq_bot` (upper numbering). All probe-verified with
`lake env lean` before the project file — the OrderIso continuity bridge compiled first try.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN
(47 files chain-checked, 8523 jobs, zero warnings). All 21 `#print axioms` standard-only; zero
`axiom` declarations project-wide. **HEADLINE: the inverse Herbrand function `ψ = φ⁻¹` and the upper
numbering `G^v(L/K) = G_{⌈ψ(v)⌉}` (Serre IV §3) — both absent from Mathlib — constructed axiom-free,
with `ψ` strictly monotone + continuous and `G^v` satisfying `G^0=G_0`, antitone, eventually `⊥`.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (`ψ` is a `def` of a real function; `G^v` a
  `def` of a `Subgroup`-valued function) ⟹ no rule-2 come-apart obligation. `upperRamificationGroup`
  is **not vacuous** (`G^0=G_0`, antitone, eventually `⊥` are proved constraints), but its **defining
  property — quotient-compatibility (Herbrand's theorem) — is the next rung, explicitly not claimed
  here.** The `[Finite (A.decompositionSubgroup K)]` hypothesis is automatic at the finite level and
  only ensures `|G_i| ≥ 1` (needed for surjectivity / for `ψ` to exist) — a standing finiteness, not
  a claimed-essential hypothesis, **no owed witness**. D1 N/A; D2 N/A. Recovers nothing from an
  abstract group; R1–R3 untouched.

## Scope: Herbrand's theorem and its prerequisites (Pass 46+)

The upper numbering's payoff is **Herbrand's theorem** `(G/H)^v = G^v H/H` — quotient-compatibility,
the reason the upper numbering exists. It is genuinely multi-pass, needing (a) the lower-numbering
**subgroup compatibility** `H_u = H ∩ G_u` (Serre IV §1 Prop 2 — fairly elementary, the congruence
restricts almost definitionally), (b) **`φ`-transitivity** `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` (Serre IV
§3 Prop 15), and (c) the quotient relationship itself. This is where Pass 43's canonicity and the
tower theory earn their keep. Also still deferred: concavity, the explicit piecewise-linear formula,
the slope `φ'(u) = 1/(G_0 : G_u)`, Hasse–Arf. R1–R3 remain the distant, must-be-earned targets.

### Pass 46 (2026-06-25) — toward Herbrand: lower-numbering subgroup compatibility `H_u = H ∩ G_u`

**Mathematics; ledger delta 0 / 0.** Built the first prerequisite for Herbrand's theorem — Serre IV
§1 Prop. 2, the behavior of the lower numbering under a sub-extension. `Anabelian/RamificationSubgroup.lean`,
7 declarations, all standard-axioms-only. The proof was short: the key facts are `rfl`.

## What was proved

For a tower `K ⊆ K' ⊆ L` and a **fixed** `A : ValuationSubring L`:

- **`ramificationGroup_eq_comap`** (the headline, Serre IV §1 Prop. 2): `ramificationGroup K' A i =
  (ramificationGroup K A i).comap decompositionRestrict` — the comap form of `H_u = H ∩ G_u`. Plus
  the textbook intersection form **`ramificationGroup_map_eq`**: `(G_i^{K'}).map decompositionRestrict
  = decompositionRestrict.range ⊓ G_i^K`.
- **`decompositionRestrict`** — the restriction-of-scalars monoid hom `Gal(L/K') →* Gal(L/K)` (built
  on `AlgEquiv.restrictScalars`), injective (`decompositionRestrict_injective`); the tower's group
  inclusion.
- supporting: `restrictScalars_smul_valuationSubring` (`σ.restrictScalars K • A = σ • A` — the
  restriction acts on the valuation subring exactly as the original), `mem_stabilizer_restrictScalars`
  (so it preserves the decomposition group), `decompositionRestrict_smul` (the actions on `↥A` agree,
  **by `rfl`**).

## Why it was easy (the key observation)

The lower numbering is **intrinsic to `L`**: `G_i = {σ | ∀ a, σa − a ∈ 𝔪_A^{i+1}}` depends only on
the action on `A`, not the base field `K`. Restriction of scalars (`AlgEquiv.restrictScalars`) leaves
the underlying map `L → L` literally unchanged (`restrictScalars_apply`/`coe_restrictScalars` are
`rfl`), so the action on `A` is **definitionally** the same — `decompositionRestrict_smul` is `rfl`,
and `ramificationGroup_eq_comap` is then `simp [Subgroup.mem_comap, mem_ramificationGroup_iff,
decompositionRestrict_smul]`. The only real work is the `ValuationSubring` stabilizer bookkeeping
(`mem_pointwise_smul_iff_inv_smul_mem`). **Using the *same* `A` for both base fields is legitimate
precisely because Pass 43 proved `𝒪_L` base-independent across the tower** — Prop. 2 is where that
canonicity first pays off.

## Mathlib API that did the real work

`AlgEquiv.restrictScalars` (+ `restrictScalars_apply`/`coe_restrictScalars`, both `rfl`);
`ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`, `MulAction.mem_stabilizer_iff`;
`Subgroup.mem_comap`, `Subgroup.map_comap_eq`; the project's `mem_ramificationGroup_iff`. The whole
construction was probe-verified with `lake env lean` and compiled first try (the action-agreement
`rfl` was confirmed before writing).

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN
(48 files chain-checked, 8524 jobs, zero warnings). All 7 `#print axioms` standard-only; zero `axiom`
declarations project-wide. **HEADLINE: Serre IV §1 Prop. 2 (`H_u = H ∩ G_u`) — the lower numbering
of a sub-extension is the restriction of the lower numbering of the whole — proved axiom-free, in
both `comap` and `map`/`∩` forms.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (`decompositionRestrict` is a `def` of a
  `MonoidHom`; results are about `Subgroup`s) ⟹ no rule-2 come-apart obligation. Stated for a general
  `A : ValuationSubring L` — **no finiteness or local-field hypothesis**, so no claimed-essential
  hypothesis, **no owed witness**. D1 N/A; D2 N/A. Recovers nothing from an abstract group; R1–R3
  untouched.

## Scope: `φ`-transitivity, then Herbrand's theorem (Pass 47+)

With Prop. 2 in hand, the next rung is **`φ`-transitivity** `φ_{L/K} = φ_{M/K} ∘ φ_{L/M}` (Serre IV
§3 Prop. 15): Prop. 2 relates the order sequences `|G_i|`, `|H_i|`, `|(G/H)_j|` across the tower,
which is what makes the two Herbrand functions compose. Harder than Prop. 2 (it touches the integral
formula and the quotient orders), but now unblocked. Then **Herbrand's theorem** `(G/H)^v = G^v H/H`
(Prop. 14) — the upper numbering's defining quotient-compatibility, the capstone. Still deferred:
concavity, the explicit piecewise-linear formula, the slope `φ'(u) = 1/(G_0 : G_u)`, Hasse–Arf.
R1–R3 remain the distant, must-be-earned targets.

### Governance reconciliation (2026-06-25) — README un-frozen; consistency rule added (no pass number; ledger 0 / 0)

**No mathematics; no pass number consumed** (the next *math* pass is Pass 47, `φ`-transitivity). A
governance-only commit, at the user's request, to make all six governance files agree on the current
state before resuming the ascent — and to mechanise that they stay agreeing.

**The inconsistency found.** `README.md` was **frozen at Pass 20**: its "Current state" header said
Pass 20, its governance-files blurb claimed "**zero `FOUNDATIONAL`, one `DEBT`**" (flatly wrong — and
self-contradicting its own line further down that said `0/0`), and it omitted all 26 passes since
(the descent, the assembly, canonicity, the entire Herbrand ascent). It had simply never been
updated as the per-pass governance edits went to `ROADMAP`/`AXIOM_LEDGER`/`NOTES`/`HANDOFF`.

**What was reconciled.**
- **`README.md` rewritten** as a concise, **current**, forward-stable overview: project description,
  the governance-file guide, a `Current state — Pass 46` section (ledger `0/0`, 48 files, Mathlib
  v4.30.0, the L1/L2/L3–L4/R1–R3 strata at a high level), and the current frontier
  (`φ`-transitivity → Herbrand). It now explicitly **mirrors** the authoritative status rather than
  duplicating per-pass detail (which lives in `NOTES.md`), so it is cheap to keep in sync.
- **`CLAUDE.md`**: added `README.md` and `HANDOFF.md` to the Repository-conventions list and a new
  **"Governance consistency is paramount"** rule — every pass must leave all six governance files
  telling one consistent current-state story; the *authoritative* source for each fact is fixed
  (current pass/status = `ROADMAP.md` header; ledger count = `AXIOM_LEDGER.md` "Active axioms" table;
  per-pass record = `NOTES.md`), the rest mirror it; historical log entries are immutable, only
  current-state claims are kept in sync; session start now skims all six headers.
- **`ROADMAP.md`**: the L2 stratum header (parenthetical was frozen at Pass 28) extended through Pass
  46 (descent / assembly / canonicity / Herbrand ascent).
- **`HANDOFF.md`**: the stale "44-file `Anabelian/` tree" note (the `refactor.sh` bullet) corrected to
  48.

**Verified consistent** (`grep`): every governance file's current-state header now reads Pass 46
(next Pass 47), ledger `0 FOUNDATIONAL / 0 DEBT`, 48 project files. Historical per-pass entries
untouched. **Ledger delta: 0 / 0**; preflight CLEAN; committed.

### Pass 47 (2026-06-25) — the slope `φ'(u) = 1/(G_0 : G_u)`

**Mathematics; ledger delta 0 / 0.** Proved the defining derivative property of the Herbrand
function (Serre IV §3): on each `(n, n+1)`, `φ` is affine with slope `|G_{n+1}|/|G_0| =
1/(G_0 : G_u)`. `Anabelian/HerbrandSlope.lean`, 8 declarations, all standard-axioms-only.

## What was proved + the method

Because Pass 44 defined `φ(u) = ∫_0^u dt/(G_0 : G_t)` as a **literal interval integral**, the slope
is a direct **fundamental theorem of calculus** application:

- The integrand `t ↦ g_{⌈t⌉}/g_0` is **locally constant off the integer breakpoints**: on
  `(n, n+1)` it equals the constant `g_{n+1}/g_0` (`Nat.floor_eq_on_Ico` ⟹ `EventuallyEq` to a
  constant near `u` ⟹ `ContinuousAt` via `Filter.EventuallyEq.continuousAt`).
- `intervalIntegral.integral_hasDerivAt_right` (FTC) then gives `HasDerivAt φ (integrand u) u`; the
  `StronglyMeasurableAtFilter` side hypothesis is discharged from global measurability
  (`Antitone.measurable`, the integrand being antitone). Result: `herbrandPhiSeq_hasDerivAt_Ioo`.
- The negative side: for `u < 0` the integrand is the constant `1` (`= g_0/g_0`), so `φ` has slope
  `1` (it is `id` there) — `herbrandPhiSeq_hasDerivAt_neg`. Plus the two `deriv` corollaries.
- **Instantiated:** `herbrandPhi_hasDerivAt_Ioo` — `φ'_{L/K}(u) = |G_{n+1}|/|G_0|` for `u ∈ (n,n+1)`,
  which is `1/(G_0 : G_{n+1}) = 1/(G_0 : G_u)` (`G_u = G_{⌈u⌉} = G_{n+1}`; Lagrange) — plus the neg
  and `deriv` forms.

Probe-verified with `lake env lean`; the `Ioo` slope compiled first try, the negative side needed
one fix (`x ∈ Iio 0` → `x < 0` coercion). Both abstract engine + instantiation, as with `φ`/`ψ`.

## Mathlib API that did the real work

`intervalIntegral.integral_hasDerivAt_right` (FTC, primitive of an integrand continuous at the
point); `Nat.floor_eq_on_Ico` (floor constant on `[n, n+1)`); `Filter.EventuallyEq.continuousAt` and
`.eq_of_nhds`; `Antitone.measurable` + `AEStronglyMeasurable` (for `StronglyMeasurableAtFilter` via
`Measure.restrict_univ`); Pass 44's `herbrandPhiSeq_intervalIntegrable`, `herbrandIntegrand_antitone`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN
(49 files chain-checked, 8525 jobs, zero warnings). All 8 `#print axioms` standard-only; zero
`axiom` declarations project-wide. **HEADLINE: `φ'_{L/K}(u) = 1/(G_0 : G_u)` — the Herbrand
function's defining derivative — proved axiom-free, directly from the integral definition by FTC.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 come-apart obligation. The
  `[Finite (A.decompositionSubgroup K)]` hypothesis is automatic at the finite level (gives
  `|G_i| ≥ 1`) — a standing finiteness, **no owed witness**. D1 N/A; D2 N/A. R1–R3 untouched.

## Honest scope: this is NOT `φ`-transitivity (Pass 48+)

The slope is the **input** to the differentiation route to transitivity, not transitivity itself.
`φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` compares slopes via the chain rule, which needs the
**index-multiplicativity** `1/(G_0 : G_u) = 1/((G/H)_0 : (G/H)_{φ_{L/K'}(u)}) · 1/(H_0 : H_u)` —
i.e. the quotient relationship `(G/H)_{φ(u)} = G_u H/H` (Serre Lemma 5 / the quotient half of
Herbrand's theorem). That is the genuinely multi-pass arithmetic wall, **deliberately not
half-built** (a clean partial beats a half-discharge — the README incident's lesson). **Two honest
options for Pass 48:** (a) attack the quotient relationship (hard); or (b) cash in clean
`φ`-deepening now unlocked by the slope — the **explicit piecewise-linear formula**
`φ(u) = (g_1+…+g_n+(u−n)g_{n+1})/g_0` on `[n,n+1]` (now provable from the slope + `φ(0)=0` via
"equal derivative ⟹ equal", sidestepping Pass 44's endpoint obstruction) and **concavity** (the
slopes `g_{n+1}/g_0` decrease since `g` does). R1–R3 remain the distant, must-be-earned targets.

### Pass 48 (2026-06-26) — the explicit piecewise-linear formula for `φ`

**Mathematics; ledger delta 0 / 0.** Proved the closed form of the Herbrand function (Serre IV §3),
the concrete counterpart of Pass 47's slope. `Anabelian/HerbrandFormula.lean`, 7 declarations, all
standard-axioms-only.

## Wall check first, then scope

Per the discipline, re-confirmed the transitivity/Herbrand **wall**: `grep` over Mathlib found no
higher-ramification quotient API (only `RamificationIdx` quotient-algebra instances, unrelated). So
full `φ`-transitivity remains the multi-pass wall; I took the clean, high-value `φ`-deepening
HANDOFF flagged — the explicit formula.

## What was proved + the method

`φ(n) = (|G_1|+…+|G_n|)/|G_0|` (`herbrandPhi_natCast`) and, on `[n,n+1]`,
`φ(u) = (|G_1|+…+|G_n|+(u−n)·|G_{n+1}|)/|G_0|` (`herbrandPhi_eq_affine_formula`). Read off the
**integral** definition (Pass 44), not the slope — which turned out cleaner:

- The crux `herbrandSeq_integral_sub_Icc`: over `[a,b] ⊆ [n,n+1]`, `∫_a^b dt/(G_0:G_t) =
  (b−a)·g_{n+1}/g_0`. The key observation that avoids endpoint pain: the interval integral only sees
  `Ι a b = Ioc a b`, which **excludes the left endpoint**, so the only a.e.-exceptional point is the
  right breakpoint `n+1` (null) — `integral_congr_ae` against the constant then `integral_const`.
- `herbrandPhiSeq_natCast`: `φ(n) = ∫_0^n` splits via `sum_integral_adjacent_intervals` into
  `Σ_{k<n} ∫_k^{k+1} = Σ_{k<n} g_{k+1}/g_0`.
- `herbrandPhiSeq_affine`: `φ(u) = ∫_0^n + ∫_n^u = φ(n) + (u−n)·g_{n+1}/g_0`
  (`integral_add_adjacent_intervals` + the crux). Combined into the closed form by `ring`.

Why the integral route over integrating Pass 47's slope: the slope route would need the *right*
derivative at each left endpoint `n`, which fails the FTC continuity hypothesis at `n=0` (integrand
value `1` ≠ right-limit `g_1/g_0`). The integral route's `Ι = Ioc` left-openness dodges this entirely.

Probe-verified with `lake env lean`; the integer values compiled after fixing a `↑(k+1)` vs `↑k+1`
cast and the `Ι`→`Set.uIoc` notation, then the affine part went through directly.

## Mathlib API that did the real work

`intervalIntegral.integral_congr_ae` (+ `Set.uIoc_of_le`, `compl_mem_ae_iff`/`measure_singleton` for
the a.e. statement, `Nat.floor_eq_on_Ico` for the constant value); `sum_integral_adjacent_intervals`,
`integral_add_adjacent_intervals`, `integral_const`; `Finset.sum_div`/`sum_congr`; Pass 44's
`herbrandPhiSeq_intervalIntegrable`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN
(50 files chain-checked, 8526 jobs, zero warnings). All 7 `#print axioms` standard-only; zero
`axiom` declarations project-wide. **HEADLINE: the explicit piecewise-linear formula for the Herbrand
function — `φ(u) = (|G_1|+…+|G_n|+(u−n)|G_{n+1}|)/|G_0|` on `[n,n+1]` — proved axiom-free, read off
the integral definition.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation. The
  `[Finite (A.decompositionSubgroup K)]` hypothesis is automatic at the finite level (gives
  `|G_i| ≥ 1`) — a standing finiteness, **no owed witness**. D1 N/A; D2 N/A. R1–R3 untouched.

## Scope: still NOT transitivity (Pass 49+)

The `φ` analytic theory is now concrete (Pass 47 slope + Pass 48 closed form), which makes the
order-arithmetic across a tower explicit — a genuine prerequisite. But `φ`-transitivity still needs
the **quotient relationship** `(G/H)_{φ_{L/K'}(u)} = G_u H/H` (Serre Lemma 5), the multi-pass wall
(absent from Mathlib). **Pass 49 options:** (a) attack the quotient relationship (hard — would need a
project-built quotient-ramification theory); or (b) the remaining clean deepening — **concavity** of
`φ` (slopes antitone) and the **`ψ` slope / closed form** (symmetric to P47/P48). R1–R3 remain the
distant, must-be-earned targets.

### Pass 49 (2026-06-26) — the slope of the inverse `ψ`

**Mathematics; ledger delta 0 / 0.** Proved the derivative of `ψ = φ⁻¹` (Serre IV §3), the symmetric
counterpart of Pass 47's `φ` slope. `Anabelian/HerbrandPsiSlope.lean`, 8 declarations, all
standard-axioms-only.

## Scope choice (concavity blocked, so the `ψ` slope)

Re-confirmed the transitivity wall. Of the two clean fallbacks, **concavity is blocked**: Mathlib's
`concaveOn_of_deriv`/`Differentiable...concaveOn` need `DifferentiableOn ℝ φ (interior)`, which `φ`
fails at its integer breakpoints — concavity would need a from-scratch piecewise/gluing argument. The
**`ψ` slope** is clean (the inverse function theorem applies directly), so I took it.

## What was proved + the method

Where `ψ(v) ∈ (n, n+1)`, `ψ'(v) = |G_0|/|G_{n+1}| = (G_0 : G_{ψ(v)})` (`herbrandPsi_hasDerivAt`) — the
ramification *index*, exactly inverting `φ' = 1/(G_0 : G_u)`. Via **`HasDerivAt.of_local_left_inverse`**
(the inverse function theorem), fed by:
- Pass 47's `φ` slope `herbrandPhiSeq_hasDerivAt_Ioo` at the point `ψ(v) ∈ (n,n+1)`;
- Pass 45's `ψ` continuity (`herbrandPsiSeq_continuous`);
- the inverse identity `φ(ψ y) = y` (`herbrandPhiSeq_psiSeq`, here as an `∀ᶠ`);
- `f' = g_{n+1}/g_0 ≠ 0`; and `(g_{n+1}/g_0)⁻¹ = g_0/g_{n+1}` by `inv_div`.

Plus the negative side `herbrandPsi_hasDerivAt_neg` (`ψ' = 1` for `v < 0`, since `ψ = id` there —
`herbrandPsiSeq_eq_id` ⟹ `ψ =ᶠ id` near `v` ⟹ `hasDerivAt_id.congr_of_eventuallyEq`), the two `deriv`
forms, and the instantiations. Probe-verified with `lake env lean`; both abstract slope and the
negative side compiled first try.

## Mathlib API that did the real work

`HasDerivAt.of_local_left_inverse` (inverse function theorem for `𝕜 → 𝕜`); `inv_div`;
`HasDerivAt.congr_of_eventuallyEq` + `hasDerivAt_id`; Pass 47's `herbrandPhiSeq_hasDerivAt_Ioo` and
Pass 45's `herbrandPsiSeq_continuous`/`herbrandPhiSeq_psiSeq`/`herbrandPsiSeq_eq_id`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN
(51 files chain-checked, 8527 jobs, zero warnings). All 8 `#print axioms` standard-only; zero `axiom`
declarations project-wide. **HEADLINE: the inverse Herbrand function's slope `ψ'(v) = (G_0 : G_{ψ(v)})`
— proved axiom-free by the inverse function theorem, completing the `φ`/`ψ` derivative picture.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation. The
  `[Finite (A.decompositionSubgroup K)]` hypothesis is automatic at the finite level (gives
  `|G_i| ≥ 1`, so `φ` is a bijection and `ψ` exists) — a standing finiteness, **no owed witness**.
  D1 N/A; D2 N/A. R1–R3 untouched.

## Scope: still NOT transitivity (Pass 50+)

The Herbrand pair `φ`/`ψ` now has its full analytic theory (monotonicity, continuity, slopes,
`φ`'s closed form). `φ`-transitivity still needs the **quotient relationship**
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` (Serre Lemma 5), the multi-pass wall (absent from Mathlib — would
need a project-built quotient-ramification theory: how `i_{K'/K}(σ̄)` relates to the `i_{L/K}` of
lifts). **Pass 50 options:** (a) begin that quotient theory (a multi-pass project of its own — and
the honest next big step); or (b) the last clean deepening — the `φ`/`ψ` **closed-form equivalences**
or **concavity** (the latter needs the piecewise argument). R1–R3 remain the distant, must-be-earned
targets.

### Pass 50 (2026-07-02) — the quotient-restriction skeleton (toward Serre Lemma 5)

**Mathematics; ledger delta 0 / 0.** Opened the quotient-ramification theory — the wall between the
completed `φ`/`ψ` analytic theory and `φ`-transitivity/Herbrand's theorem — with its
group-theoretic skeleton, complete and axiom-free. `Anabelian/RamificationQuotient.lean`,
11 declarations, all standard-axioms-only.

## Scope choice (the HANDOFF's option (a), first brick)

The analytic side of Herbrand is saturated (P44–49); everything left is gated on the quotient
relationship `(G/H)_{φ_{L/K'}(u)} = G_u H/H` (Serre IV §3 Lemma 5), whose core is ramification
*arithmetic* (`i_{K'/K}(σ̄)` vs the `i_{L/K}` of the lifts). Per the clean-partial-over-
half-discharge rule, this pass built the skeleton that arithmetic will stand on — and nothing of
the arithmetic itself.

## What was proved + the method

For a tower `K ⊆ K' ⊆ L` with `K'/K` **normal**, `A : ValuationSubring L`, and
`A ∩ K' := A.comap (algebraMap K' L)` (= `𝒪_{K'}` when `A = 𝒪_L`, unambiguous by P43 canonicity):

- `restrictNormalHom_smul_comap` — `σ̄ • (A ∩ K') = (σ • A) ∩ K'`: restriction intertwines the
  pointwise actions (engine: `AlgEquiv.restrictNormal_commutes` applied to `σ⁻¹` through
  `map_inv`).
- **`decompositionQuotient : D(A) →* D(A ∩ K')`** — the quotient restriction on decomposition
  groups along `Gal(L/K) ↠ Gal(K'/K)` (Mathlib's `AlgEquiv.restrictNormalHom`), the quotient
  counterpart of P46's `decompositionRestrict`. Action compatibility
  `algebraMap K' L (σ̄ • b) = σ (algebraMap K' L b)` is `restrictNormal_commutes` — *not* `rfl`,
  which is exactly why the quotient half is harder than P46's subgroup half (there the action
  agreement was definitional).
- `decompositionQuotient_comp_decompositionRestrict = 1` — the composite
  `D(A)|_{Gal(L/K')} → D(A) → D(A ∩ K')` is trivial (`AlgEquiv.commutes` + injectivity of
  `algebraMap K' L`).
- **`decompositionQuotient_ker` (HEADLINE)** — **exactness at the decomposition level**:
  `ker (decompositionQuotient) = range (decompositionRestrict)`. Forward: a `σ` restricting to `1`
  fixes `algebraMap K' L` pointwise (via `restrictNormal_commutes`), hence *is* a `K'`-algebra
  automorphism (`AlgEquiv.ofRingEquiv` on `σ.toRingEquiv`) with the same underlying map, so it
  stabilizes `A` and maps back to `σ` (`rfl` after `Subtype.ext`/`AlgEquiv.ext`). The
  decomposition groups inherit the exactness of `1 → Gal(L/K') → Gal(L/K) → Gal(K'/K)`.
- `comapRingHom : A ∩ K' →+* A` + `mem_maximalIdeal_of_comapRingHom` — the inclusion reflects the
  maximal ideal (`mem_maximalIdeal`/`mem_nonunits_iff`: a unit maps to a unit by `IsUnit.map`).
- **`decompositionQuotient_mem_ramificationGroup_zero`** (+ `ramificationGroup_zero_map_le`,
  `inertiaSubgroup_map_le` via P23's `ramificationGroup_zero`) — **the quotient map preserves
  inertia**: `σ ∈ G_0(L/K) ⟹ σ̄ ∈ G_0(K'/K)`. For `b ∈ A ∩ K'`, `σ̄b − b` maps to `σb − b ∈ 𝔪_A`
  under `comapRingHom` (action compatibility), and the inclusion reflects `𝔪`. The first genuinely
  ramification-flavored quotient fact — the `i = 0` base case of Lemma 5, renumbering-free because
  `φ_{L/K'}(0) = 0`.

Probe-verified with `lake env lean` before touching the project tree; the probe compiled with only
three mechanical fixes (a `rw`→`calc` where `restrictNormalHom` vs `restrictNormal` blocked the
syntactic match; explicit iff-chaining where a double `mem_pointwise_smul` rewrite misfired; and
`comapRingHom` not binding the unused `K` variable).

## Mathlib API that did the real work

`AlgEquiv.restrictNormalHom` + `AlgEquiv.restrictNormal_commutes` (the entire quotient direction);
`AlgEquiv.ofRingEquiv` (kernel converse); `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`;
`mem_maximalIdeal` + `_root_.mem_nonunits_iff` + `IsUnit.map`. (Note the `_root_.` — the
`ValuationSubring` open shadows `mem_nonunits_iff` with an unrelated valuation lemma.)

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN. All
11 `#print axioms` standard-only; zero `axiom` declarations project-wide. Housekeeping: untracked
`claude.last` (session-tooling scratch, found at session start per the clean-tree rule) added to
`.gitignore`. **HEADLINE: the quotient-restriction skeleton — `decompositionQuotient`, exactness
of `Gal(L/K') → Gal(L/K) → Gal(K'/K)` at the decomposition level, and inertia preservation
`G_0 → G_0` — all axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (`decompositionQuotient`/`comapRingHom`
  are `def`s of a `MonoidHom`/`RingHom`) ⟹ no rule-2 obligation. `[Normal K K']` is a
  *definitional prerequisite* (without normality `Gal(K'/K)` receives no restriction map and the
  skeleton does not exist), not a removable theorem hypothesis — **no owed witness**. D1 N/A;
  D2 N/A. R1–R3 untouched.

## Scope: the skeleton, NOT the arithmetic (Pass 51+)

Deliberately unbuilt (clean partial > half-discharge): **surjectivity** of `decompositionQuotient`
(needs transitivity of the Galois action on the valuation subrings above a given one — real
arithmetic content) and the **higher-`i` image**, which *is* Lemma 5
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` with its `φ`-renumbering — the `i_{K'/K}` vs `i_{L/K}` arithmetic,
the genuine multi-pass wall. **Pass 51 options:** (a) begin that arithmetic — e.g. the `i_{L/K}`
function itself (`i(σ) = v_L(σπ − π)` / `inf_a v(σa − a)`) as a project object with its basic
theory, the currency Lemma 5 is stated in; or (b) surjectivity of `decompositionQuotient` in the
finite/local setting. R1–R3 remain the distant, must-be-earned targets.

### Pass 51 (2026-07-03) — Serre's `i_G` function (`lowerIndex`), IV §1 Lemma 1 abstract form

**Mathematics; ledger delta 0 / 0.** Minted the currency of the quotient-ramification arithmetic:
Serre's `i_G`, generator-free, with its filtration characterization and calculus, plus the second
half of IV §1 Prop. 2. `Anabelian/RamificationIndex.lean`, 13 declarations, all
standard-axioms-only.

## Scope choice (HANDOFF option (a): the first arithmetic brick)

Pass 50 built the quotient skeleton; everything toward Lemma 5 now runs through Serre's
`i_G(σ)` (IV §1: `i_G(σ) = v_L(σx − x)`, `σ ∈ G_i ⇔ i_G(σ) ≥ i + 1`; Prop. 3 states the
`i_{K'/K}` sum formula in it). This pass defines `i_G` **generator-free** — as the `ℕ∞`-valued
sup `lowerIndex K A σ = sup {n | ∀ a ∈ A, σa − a ∈ 𝔪_A^n}` — so no monogenicity is needed yet;
Lemma 1's generator-free half becomes provable now, and the `v_L(σx − x)` identification is
deferred to the monogenic setting (Prop. 3) that actually needs it.

## What was proved + the method

- **`mem_ramificationGroup_iff_lt_lowerIndex` (HEADLINE**, Serre IV §1 Lemma 1 abstract form**)**:
  `σ ∈ G_i ↔ (i : ℕ∞) < i_G(σ)`. Forward: `i + 1` is in the defining set, `le_biSup`. Backward:
  `lt_biSup_iff` produces `n > i` in the set, and the set is downward closed
  (`Ideal.pow_le_pow_right`). Serre's inequality form `↔ i + 1 ≤ i_G(σ)` via
  `ENat.add_one_le_iff`.
- **The calculus, each a one-liner from Lemma 1 + subgroup structure**: `lowerIndex_inv`
  (`inv_mem_iff`), `min_lowerIndex_le_lowerIndex_mul` (`mul_mem`), `lowerIndex_conj` (class
  function — P23's `ramificationGroup_normal`), `lowerIndex_one` (= `⊤`),
  `lowerIndex_eq_top_iff_forall`, and `lowerIndex_eq_top_iff` (`= ⊤ ↔ σ = 1` under Krull
  separation, via P23's `iInf_ramificationGroup_eq_bot`).
- **`lowerIndex_decompositionRestrict`** — `i_H = i_G` on `H` (IV §1 Prop. 2's second half; P46
  proved the subgroup half `H_u = H ∩ G_u`): **`rfl`**. The defining condition is intrinsic to
  `A` and P46's `decompositionRestrict_smul` action agreement is definitional — the probe
  confirmed `rfl` closes it on the first try.
- **The `ℕ∞` interface**: two small public lemmas — `enat_le_of_forall_natCast_lt` (naturals are
  cofinal below any `x : ℕ∞`: to prove `x ≤ y` check every natural below `x`) and
  `enat_eq_of_forall_natCast_lt_iff` — kept public for the coming Prop.-3 arithmetic; everything
  else runs on `lt_biSup_iff`/`le_biSup`/`ENat.eq_top_iff_forall_gt`.

Probe-verified with `lake env lean`; the probe compiled **first try** (only fix: Mathlib has
deprecated `push_neg` → `push Not`).

## Mathlib API that did the real work

`lt_biSup_iff` + `le_biSup` (the entire sup layer); `ENat.add_one_le_iff` +
`ENat.eq_top_iff_forall_gt` + `lift ... using ne_top`; `Ideal.pow_le_pow_right`;
`Subgroup.Normal.conj_mem`; `inv_mem_iff`/`mul_mem`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN. All
13 `#print axioms` standard-only; zero `axiom` declarations project-wide. **HEADLINE: Serre's
`i_G` function, generator-free (`lowerIndex : D(A) → ℕ∞`), with IV §1 Lemma 1
`σ ∈ G_i ↔ i < i_G(σ)`, its calculus, and `i_H = i_G` on subextensions (Prop. 2's second half,
by `rfl`) — all axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (`lowerIndex` is a `def` into `ℕ∞`) ⟹ no
  rule-2 obligation. The separation hypothesis in `lowerIndex_eq_top_iff` is inherited from P23's
  `iInf_ramificationGroup_eq_bot` under the same governance (finite level: holds; `𝒪[K̄]`:
  provably fails — both witnessed in P22/P23; as there, no irremovability claim for this
  conclusion) — **no owed witness**. D1 N/A; D2 N/A. R1–R3 untouched.

## Scope: the currency, NOT the sum formula (Pass 52+)

Deliberately absent: **Serre IV §1 Prop. 3** `i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)` — the
real arithmetic wall. Its needs: the concrete `i_G(σ) = v_L(σx − x)` (monogenicity — the
project's `ExtensionMonogenic*` arc from the descent), the lift analysis over
`decompositionQuotient` (P50), and `e' = e_{L/K'}`. **Pass 52 options:** (a) the concrete
identification `i_G(σ) = v(σx − x)` in the monogenic setting — the bridge between `lowerIndex`
and the generator arithmetic, Prop. 3's precondition; (b) surjectivity of
`decompositionQuotient` at the finite/local level (also on Prop. 3's critical path — the sum
ranges over the lifts of `σ̄`, which must exist); or (c) the `ψ` closed form (last clean analytic
deepening). R1–R3 remain the distant, must-be-earned targets.

### Pass 52 (2026-07-03) — surjectivity of the quotient restriction; `D(A) ⧸ H ≃* D(A ∩ K')`

**Mathematics; ledger delta 0 / 0.** Discharged one of Pass 50's two named gaps — surjectivity
of `decompositionQuotient` — and packaged the quotient theory into the first isomorphism
`D(A) ⧸ H ≃* D(A ∩ K')`. `Anabelian/RamificationQuotientSurjective.lean`, 7 declarations, all
standard-axioms-only.

## Scope choice (HANDOFF option (b), taken because it was short — and it was)

The HANDOFF flagged that surjectivity might be nearly free if the canonical valuation subring is
stable under the whole Galois group. It is, for a structural reason cleaner than valuation
uniqueness: **`extensionIntegers K L` is the integral closure of `𝒪_K` in `L` (P29,
membership `= IsIntegral` by `Iff.rfl`), and integral closure is Galois-stable.** The probe
compiled first try (the only fix: an unused-section-variable warning — `[Normal K L]` moved from
the section `variable` block to the declarations that use it).

## What was proved + the method

- **`smul_extensionIntegers`**: `σ • 𝒪_L = 𝒪_L` for every `σ ∈ Gal(L/K)` —
  `mem_pointwise_smul_iff_inv_smul_mem` + `mem_extensionIntegers_iff` reduces it to
  `IsIntegral 𝒪_K (σ⁻¹ x) ↔ IsIntegral 𝒪_K x`, which is `IsIntegral.map` along
  `(σ.restrictScalars ↥𝒪[K]).toAlgHom` (both directions via `σ`/`σ⁻¹`; the
  `Algebra ↥𝒪[K] L` + `IsScalarTower` instances all fire automatically).
- **`decompositionSubgroup_extensionIntegers_eq_top`**: `D(𝒪_L) = ⊤` — every automorphism
  decomposes at the canonical subring. The integral-closure form of Serre's "complete ⟹ unique
  valuation extension ⟹ D = G" (IV §1).
- **`decompositionQuotient_surjective`** (abstract): `[Normal K L]`, `[Normal K K']`, and full
  stability `∀ σ, σ • A = A` ⟹ surjective. Lift `τ̄` by
  `AlgEquiv.restrictNormalHom_surjective`; stability puts the lift in `D(A)`; `Subtype.ext`
  finishes (the P50 `decompositionQuotient` literally applies `restrictNormalHom`). Stability is
  a *sufficient* hypothesis discharged at `𝒪_L`; no necessity claim (rule-2: no owed witness).
- **`decompositionRestrict_range_normal`**: `H = range (decompositionRestrict)` is normal in
  `D(A)` — it *is* a kernel by P50's exactness (`rw [← decompositionQuotient_ker];
  infer_instance`).
- **`decompositionQuotientEquiv`** (+ `_extensionIntegers` instantiation):
  `D(A) ⧸ range (decompositionRestrict) ≃* D(A ∩ K')` via `quotientMulEquivOfEq` (ker = range)
  + `quotientKerEquivOfSurjective`. **The `(G/H)` of Herbrand's theorem `(G/H)^v = G^v H/H` now
  exists as an honest quotient isomorphic to the subextension's decomposition group.**

## Mathlib API that did the real work

`AlgEquiv.restrictNormalHom_surjective` (via `liftNormal`); `IsIntegral.map` +
`AlgEquiv.restrictScalars` (stability); `QuotientGroup.quotientKerEquivOfSurjective` +
`QuotientGroup.quotientMulEquivOfEq`; `Subgroup.eq_top_iff'`;
`MulAction.mem_stabilizer_iff`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN. All
7 `#print axioms` standard-only; zero `axiom` declarations project-wide. **HEADLINE: the quotient
restriction `D(𝒪_L) → D(𝒪_L ∩ K')` is surjective (𝒪_L is Galois-stable, D(𝒪_L) = ⊤), and
`D(A) ⧸ H ≃* D(A ∩ K')` — the (G/H) of Herbrand's theorem, realized axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** (`decompositionQuotientEquiv` is a `def`
  of a `MulEquiv`) ⟹ no rule-2 obligation. The abstract surjectivity's stability hypothesis is
  discharged at the instantiation — presented as sufficient, no necessity/irremovability claim
  ⟹ **no owed witness**. D1 N/A; D2 remains localized inside P29's `extensionIntegers` proof
  (this file uses only the `IsIntegral` membership). R1–R3 untouched.

## Scope: the lifts exist; the sum over them is the wall (Pass 53+)

Both P50 gaps are now closed except the one that *is* the wall: Serre IV §1 **Prop. 3**
`i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)`. Its remaining prerequisite is the **concrete
`i_G`**: `i_G(σ) = v(σx − x)` for a monogenic generator `x` of `𝒪_L/𝒪_K` — the bridge from
P51's `lowerIndex` sup to generator arithmetic (Serre's one-generator reduction:
`∀ a, σa − a ∈ 𝔪^n ↔ σx − x ∈ 𝔪^n`, using that `a` is a polynomial in `x`). **Pass 53:**
check what the `ExtensionMonogenic*` arc (P29–37 descent) provides as the generator statement,
then prove the one-generator reduction and `lowerIndex = (𝔪-adic order of) σx − x`. After that:
Prop. 3 itself, then Lemma 5 → `φ`-transitivity (Prop. 15) → Herbrand (Prop. 14). R1–R3 remain
the distant, must-be-earned targets.

### Pass 53 (2026-07-03) — the concrete `i_G`: `lowerIndex = v_L(σx − x)`

**Mathematics; ledger delta 0 / 0.** The concrete half of Serre IV §1 Lemma 1: under the
monogenicity package, Pass 51's generator-free `lowerIndex` is the `addVal` of the generator
displacement. `Anabelian/RamificationIndexGenerator.lean`, 5 declarations, all
standard-axioms-only.

## Scope choice (HANDOFF first task; the inventory paid off)

The HANDOFF's first step was an inventory of the `ExtensionMonogenic*` arc, and it changed the
shape of the pass: **the reduction engine already existed**. Pass 25 (`TameInjectivity.lean`)
proved `smul_sub_dvd_of_mem_closure` — `σ` fixes `A₀` pointwise ⟹ `(σx − x) ∣ (σa − a)` for all
`a ∈ closure (A₀ ∪ {x})`, by `Subring.closure_induction` with the telescoping multiplicative
step — and the one-directional detection `mem_ramificationGroup_of_smul_uniformizer_sub_mem`.
(Note: P25's `π` is *any* ring generator — no `hspan` in these two lemmas — so they apply
verbatim to a non-uniformizer generator `x`.) What was missing: the iff, the `lowerIndex`
identification, and the `addVal` form. That is this pass.

## What was proved + the method

- **`mem_maximalIdeal_pow_iff_le_addVal`** (DVR bridge, stated for any DVR domain):
  `x ∈ 𝔪^n ↔ (n : ℕ∞) ≤ addVal R x`. Three rewrites: `Irreducible.maximalIdeal_eq` +
  `Ideal.span_singleton_pow` + `Ideal.mem_span_singleton`, then `addVal_le_iff_dvd` +
  `Irreducible.addVal_pow`. Mathlib has the ingredients, not the statement — a reusable brick.
- **`forall_smul_sub_mem_iff_generator`**: `(∀ a, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n` under
  (`hgen`, `hfix`). `⟹` is instantiation at `a := x`; `⟸` splits on `n` (`n = 0`: `𝔪^0 = ⊤`;
  `n = i+1`: P25's detection + `mem_ramificationGroup_iff`).
- **`mem_ramificationGroup_iff_smul_generator_sub_mem`** (Lemma 1, generator form):
  `σ ∈ G_i ↔ σx − x ∈ 𝔪^(i+1)`.
- **`lowerIndex_eq_addVal`** (HEADLINE): `i_G(σ) = addVal (σ • x − x)` on a DVR valuation
  subring under the package — by P51's `enat_eq_of_forall_natCast_lt_iff`: for each `n`,
  `n < lowerIndex ↔ σ ∈ G_n ↔ σx − x ∈ 𝔪^(n+1) ↔ n+1 ≤ addVal ↔ n < addVal`
  (`ENat.add_one_le_iff` + `norm_cast`). Exactly the currency Prop. 3 computes with.
- **`lowerIndex_extensionIntegers_eq_addVal`**: at `𝒪_L`, `hfix` is free (P32's
  `smul_extensionAlgebraMap_range_eq`), the DVR instance is P35's
  (`isDiscreteValuationRing_extensionIntegers`, `[Algebra.IsSeparable K L]`); **only `hgen`
  remains a named binder**.

Probe-verified with `lake env lean`; one mechanical fix (P25's lemma takes `A` implicitly —
call is `mem_ramificationGroup_of_smul_uniformizer_sub_mem K hgen hfix h`, no `A`).

## The monogenicity hypothesis, honestly (the P25 discipline, restated)

`hgen : Subring.closure (↑A₀ ∪ {x}) = ⊤` is a **named hypothesis binder** — NOT an `axiom`
(kernel untouched; all `#print axioms` standard-only), NOT claimed discharged, NOT claimed
necessary. Its discharge — Serre III §6 Prop. 12 (complete DVR, separable residue extension ⟹
monogenic), instantiable here since `𝓀_L/𝓀_K` is an extension of finite fields — is named
future work (ROADMAP L2). The P32–34 engine (`closure_subring_union_uniformizer_eq_top`)
discharges a *different* generation statement (over `inertiaFixedIntegers`, two generators) and
is not conflated with `hgen`.

## Mathlib API that did the real work

`IsDiscreteValuationRing.addVal` (`addVal_le_iff_dvd`, `Irreducible.addVal_pow`,
`Irreducible.maximalIdeal_eq`); `Ideal.span_singleton_pow`/`mem_span_singleton`; P25's
`Subring.closure_induction` engine (reused, not re-proved); P51's `ℕ∞` cofinality lemma;
`ENat.add_one_le_iff`; `norm_cast`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN.
All 5 `#print axioms` standard-only; zero `axiom` declarations project-wide. **HEADLINE: the
concrete `i_G` — `lowerIndex K A σ = v_L(σx − x)` (`addVal`) under the monogenicity package,
with Lemma 1 in generator form `σ ∈ G_i ↔ σx − x ∈ 𝔪^(i+1)` — all axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 structure obligation.
  `hgen`/`hfix` are sufficient-condition binders with **no necessity claim** ⟹ no owed witness
  (the exact P25/27/28 precedent, restated in the file's Honesty section). D1 N/A; D2 stays
  inside P29's proofs. R1–R3 untouched.

## Scope: the currency is concrete; the sum is the wall (Pass 54+)

Prop. 3's inputs are now: lifts exist (P52), `i_G` concrete (P53). **Pass 54 options:** (a)
**Prop. 3 itself** — `i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)`; Serre's proof compares
`σ̄y − y` (`y` generating `𝒪_{K'}`) with `∏_s (sx − x)` (`x` generating `𝒪_L` over `𝒪_{K'}`)
via divisibility both ways — multi-step, may itself split into the two divisibilities; (b)
**discharge `hgen`** (Serre III §6 Prop. 12) — finite residue fields are simple extensions
(`𝓀_L^×` cyclic), lift a generator of `𝓀_L/𝓀_K` and correct by a uniformizer; the project has
the residue-finiteness (P36 arc) and uniformizer packages; a self-contained pass that would
convert P53's conditional statements into unconditional ones at `𝒪_L`. (b) first is the
recommended order — it de-conditionalizes before the wall. R1–R3 remain the distant,
must-be-earned targets.

### Pass 54 (2026-07-03) — the monogenicity discharge: `𝒪_L = 𝒪_K[x]`

**Mathematics; ledger delta 0 / 0 — and P53's one named hypothesis became a theorem.** Serre
III §6 Prop. 12 in the finite-residue case: `𝒪_L` is monogenic over `𝒪_K` for every finite
separable extension of a nonarchimedean local field; hence the concrete `i_G` is
**unconditional**. `Anabelian/ExtensionMonogenicDischarge.lean`, 5 declarations, all
standard-axioms-only.

## Scope choice (HANDOFF option (a), the recommended de-conditionalization)

P53 left exactly one named binder in the `i_G` theory: `hgen`. The classical proof of Prop. 12
runs through the minimal polynomial of a residue generator, its separability, a monic lift,
and a Taylor expansion. **None of that was needed**: with residue fields *finite* (P36), the
explicit polynomial `X^n − 1` (`n = |𝓀_L^×|`) does everything the minpoly does.

## The route (no minpoly, no Taylor)

1. `g` := cyclic generator of `𝓀_L^×` (`IsCyclic.exists_generator`); `x₀` a lift. Every
   residue is `0` or `g^k` (`isOfFinOrder_of_finite` + `mem_powers_iff_mem_zpowers` to convert
   `ℤ`-powers to `ℕ`-powers), so `𝒪_K[x₀]` covers residues — the engine's `hres` for free.
2. `y₀ := x₀^n − 1 ∈ 𝔪` (Lagrange `g^n = 1`). The "derivative" is the explicit unit `n·x₀^n`:
   `(n : 𝓀_L) = |𝓀_L| − 1 = −1 ≠ 0` (`Nat.card_units` + `FiniteField.cast_card_eq_zero` —
   the cardinality vanishes in its own characteristic; works uniformly in equal and mixed
   characteristic).
3. If `y₀ ∈ 𝔪²`: correct `x := x₀(1 + π₀)`. The **binomial tail**
   `(1+t)^m = 1 + mt + t²a` (`exists_pow_one_add_eq`, 8-line induction, `propext`-only) gives
   `x^n − 1 = y₀ + (x₀^n·n)·π₀ + (x₀^n·a)·π₀²`; first and third terms in `𝔪²`, middle term
   `unit · π₀ ∉ 𝔪²` — so `x^n − 1 ∈ 𝔪 ∖ 𝔪²`. (Serre's `x + π` correction in multiplicative
   form; the unit-cancellation `π₀ = v⁻¹(v·π₀) ∈ 𝔪²`-contradiction replaces the valuation
   count.)
4. `𝔪 ∖ 𝔪²` spans `𝔪` (`maximalIdeal_eq_span_of_mem_of_notMem_sq` — new reusable DVR brick,
   via P53's `addVal` bridge: `addVal = 1` exactly). So `x^n − 1` is a uniformizer **inside**
   `𝒪_K[x]`, and P32's engine (`closure_subring_union_uniformizer_eq_top`, `he` from P33's
   `exists_pow_maximalIdeal_le_map`) gives `closure(𝒪_K[x] ∪ {x^n−1}) = ⊤`; the union
   collapses (`Set.union_eq_self_of_subset_right` + `Subring.closure_eq`). Assembly factored
   as `closure_union_singleton_eq_top`.

**Payoff:** `exists_generator_lowerIndex_eq_addVal` — `∃ x, ∀ σ, i_G(σ) = v_L(σx − x)`,
no hypotheses. The P51–54 `i_G` theory is now hypothesis-free at `𝒪_L`.

## What this does NOT discharge (no conflation)

The P25/27/28 character theorems' package needs an *inertia-fixed* generating subring
(`hfix` over `G_0`); `𝒪_K[x]` is not inertia-fixed (`x` moves under inertia — that movement
IS `i_G`). That route was closed separately by P32–34 via `inertiaFixedIntegers`.

## Probe experience (2 mechanical rounds)

`ℕ∞` numerals vs `((k:ℕ):ℕ∞)` casts blocked two `rw`s (restated the `have`s with explicit
casts and used `.mp`/`.mpr` term-style); `residue` vs `Ideal.Quotient.mk` is defeq but not
syntactic — `rw` on a `residue`-form fails against an `mk`-form goal; route the fact through a
`have hres0 : residue … = 0` and apply `Ideal.Quotient.eq_zero_iff_mem.mp` (term-level defeq is
fine). `Nat.card_units` takes `α` **explicitly**. `Fintype.card_units` was avoided entirely
(instance-mismatch between `Fintype.ofFinite` and the `DecidableEq`-derived instance) — the
`Nat.card` API (`pow_card_eq_one'`, `Nat.card_units`, `Nat.card_pos`) is instance-agnostic and
strictly cleaner here.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN.
All 5 `#print axioms` standard-only (the binomial tail is `propext`-only); zero `axiom`
declarations project-wide. **HEADLINE: `𝒪_L` is monogenic over `𝒪_K` (Serre III §6 Prop. 12,
finite-residue case), proved axiom-free — and with it the concrete `i_G` is unconditional:
`∃ x, ∀ σ, i_G(σ) = v_L(σx − x)`.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. The named-binder discipline of P25–P53
  paid out exactly as designed: the hypothesis was carried honestly, then **proved**, and every
  downstream statement de-conditionalizes by substitution. D1 N/A; D2 untouched. R1–R3
  untouched.

## Scope: Prop. 3 is now the entire remaining wall (Pass 55+)

Everything Prop. 3 needs is in place: lifts exist (P52), `i_G = v_L(σx − x)` with a real `x`
(P53–54), `i_H = i_G` (P51), `𝔪_B` reflection (P50). **Pass 55: begin Prop. 3** —
`i_{K'/K}(σ̄) = (1/e') Σ_{s ↦ σ̄} i_{L/K}(s)`. Serre's proof: `y` generates `𝒪_{K'}/𝒪_K`,
`x` generates `𝒪_L/𝒪_{K'}` (both now theorems — note the second needs `K'` as a local field:
the P38–41 assembly + P43 canonicity provide exactly that); compare `a := σ̄y − y` with
`b := ∏_{s ↦ σ̄} (sx − x)` via **two divisibilities** (`a ∣ b` from `y ∈ 𝒪_{K'}[x]`-side
arithmetic, `b ∣ a` from the product over the coset); then `addVal` both sides. Scope ONE
divisibility direction per pass if needed; clean partial > half-discharge. R1–R3 remain the
distant, must-be-earned targets.

### Pass 55 (2026-07-03) — the subextension characteristic polynomial (Prop. 3's substrate)

**Mathematics; ledger delta 0 / 0.** Built the polynomial both divisibility directions of
Serre IV §1 Prop. 3 run through — `f = ∏_{h ∈ Gal(L/K')} (X − h·x)` with coefficients
descending to `𝒪_L ∩ K'` — hypothesis-free at `𝒪_L`.
`Anabelian/SubextensionCharPoly.lean`, 11 declarations, all standard-axioms-only.

## Scope choice (Prop. 3's architecture, fixed here)

Serre proves Prop. 3 by comparing `a := σ̄y − y` and `b := ∏_{s ↦ σ̄} (sx − x)` through
`f(X) = ∏_{h ∈ H} (X − hx) ∈ 𝒪_{K'}[X]`: **(i)** `a ∣ b` since `σ̄f − f` has coefficients
`σ̄c − c` divisible by `a` (P25 telescoping in `𝒪_{K'} = 𝒪_K[y]`) and `(σ̄f)(x) = ±b`;
**(ii)** `b ∣ a` via the monic division `g(X) − y = f·q` (where `y = g(x)`, `g ∈ 𝒪_K[X]`,
from P54's monogenicity over `𝒪_K`) transported along `σ̄` and evaluated at `x`. This pass
builds `f` and its descent; the divisibilities are next.

## What was proved + the method

- **`fullProdXSubSMul G R x := ∏ g : G, (X − C (g • x))`** — the inventory found Mathlib's
  `prodXSubSMul`, but it ranges over the **orbit** `G ⧸ stabilizer G x` — the wrong primitive
  (Prop. 3's lift-set product counts multiplicities; for a generator the two coincide, but the
  full product is what transports to `∏_{s ↦ σ̄}`). Defined the `Finset.univ` version with the
  same four properties by the same techniques: `_monic` (`monic_prod_of_monic`),
  `_natDegree = |G|` (`natDegree_prod_of_monic`), `_eval x = 0` (`prod_eq_zero` at `g = 1`),
  and `_smul` — `G`-invariance by left-translation reindexing (`Finset.smul_prod'` +
  `Equiv.prod_comp (Equiv.mulLeft g)`), hence `_coeff` (`G`-fixed coefficients via
  `coeff_smul`).
- **`exists_comapRingHom_eq_of_forall_smul_eq`** — the fixed-points descent: `a ∈ 𝒪_L` fixed
  by every `σ : L ≃ₐ[K'] L` lies in `range (algebraMap K' L)`
  (`IsGalois.mem_range_algebraMap_iff_fixed` — Mathlib had exactly the field-level statement)
  and the preimage is integral (its image is `a ∈ A`), so it lifts along P50's
  `comapRingHom K' A`.
- **`exists_fullProdXSubSMul_lift`** (HEADLINE) — under `hD : D_{K'}(A) = ⊤`: every
  coefficient is fixed by every field automorphism (convert via `hD`; the subgroup action is
  the field action definitionally), descends by the above, and
  `Polynomial.lifts_iff_coeff_lifts` + `lifts_and_degree_eq_and_monic` produce a **monic** `F`
  over `A ∩ K'` with `F.map (comapRingHom K' A) = f` and equal degree.
- **`decompositionSubgroup_extensionIntegers_restrict_eq_top`** — `D_{K'}(𝒪_L) = ⊤` for ANY
  intermediate `K'`: `σ • 𝒪_L = (σ.restrictScalars K) • 𝒪_L` (P46's
  `restrictScalars_smul_valuationSubring`) `= 𝒪_L` (P52's `smul_extensionIntegers`). Hence
  the hypothesis-free instantiation `exists_fullProdXSubSMul_lift_extensionIntegers`.
- **`extensionIntegers_comap_algebraMap`** — `𝒪_L ∩ K = (valuation K).valuationSubring`
  (same base), 4 lines from P35's `algebraMap_mem_extensionIntegers_iff` (note: `𝒪[K]` the
  notation is a `Subring`, so the `ValuationSubring`-level statement goes through
  `Valuation.mem_valuationSubring_iff`/`mem_integer_iff`, both `Iff.rfl`).

Probe: 2 rounds (unknown-namespace fix `IsGalois.mem_range_algebraMap_iff_fixed`, and the
`𝒪[K]`-is-a-`Subring` type mismatch).

## Mathlib API that did the real work

`prodXSubSMul`'s own proof kit (`Finset.smul_prod'`, `Polynomial.smul_X/smul_C/coeff_smul`);
`Equiv.prod_comp` + `Equiv.mulLeft`; `IsGalois.mem_range_algebraMap_iff_fixed`;
`Polynomial.lifts_iff_coeff_lifts`, `Polynomial.lifts_and_degree_eq_and_monic`;
`monic_prod_of_monic`, `natDegree_prod_of_monic`, `eval_prod`, `Finset.prod_eq_zero`.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN.
All 11 `#print axioms` standard-only; zero `axiom` declarations project-wide. **HEADLINE:
Serre's polynomial `∏_{h ∈ Gal(L/K')} (X − h·x)` descends to a monic polynomial over
`𝒪_L ∩ K'` of the same degree — hypothesis-free at `𝒪_L` (`D_{K'}(𝒪_L) = ⊤` for any
intermediate field) — the substrate of IV §1 Prop. 3, axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. D1 N/A; D2 stays inside P29's proofs
  (`IsIntegral`-level only). R1–R3 untouched.

## Scope: the polynomial exists; the divisibilities are next (Pass 56+)

**Pass 56 options** (Prop. 3's two directions, one per pass if needed):
- **(i) `a ∣ b`**: for a lift `s` of `σ̄`, `(σ̄F − F)` (coefficients `σ̄c − c` in `𝒪_{K'}`,
  each divisible by `a = σ̄y − y` via P25's telescoping applied in `𝒪_{K'} = 𝒪_K[y]` — P54's
  monogenicity at `(K, K')`), evaluated at `x`: `(σ̄f)(x) − f(x) = (σ̄f)(x) = ± b`. Needs: the
  transport of `F` along `σ̄` (map by the `D(B)`-action on `𝒪_L ∩ K'`) and the identity
  `(map (σ̄) f).eval x = ∏_{s ↦ σ̄} (x − s•x)` — the lift-set reindexing (P50 exactness: the
  fiber over `σ̄` is a coset of `range decompositionRestrict`).
- **(ii) `b ∣ a`**: the monic division `g(X) − y = f·q` in `(𝒪_L ∩ K')[X]` (`Monic.divModByMonic`
  machinery or `modByMonic` + degree argument), transported along `σ̄`, evaluated at `x`.
R1–R3 remain the distant, must-be-earned targets.

### Pass 56 (2026-07-03) — the lift-set identity (Prop. 3's reindexing layer)

**Mathematics; ledger delta 0 / 0.** The fiber of `decompositionQuotient` over `σ̄` is the
coset `s₀·H` as an explicit bijection, and Serre's polynomial transported along a lift is the
fiber product — Prop. 3's `∏_{s ↦ σ̄}` is now computable in `H`-parametrized form.
`Anabelian/RamificationLiftSet.lean`, 6 declarations, all standard-axioms-only.

## Scope choice (HANDOFF option (A) — the hinge of direction (i))

Prop. 3's direction (i) evaluates `σ̄f − f` at `x`; since `f(x) = 0` (P55), the value is
`(σ̄f)(x)`, and the whole game is knowing that `σ̄f` — the polynomial with `σ̄`-transported
coefficients — is `∏_{s ↦ σ̄} (X − s·x)`. That identity plus the fiber parametrization is
this pass; it is pure bookkeeping over P46/P50/P55, and the probe compiled essentially first
try (one dead tactic block removed — see below).

## What was proved + the method

- **`map_fullProdXSubSMul` (HEADLINE)**: `(∏_{h ∈ H} (X − C (h•x))).map (toRingAut s₀)
  = ∏_{h ∈ H} (X − C ((s₀ * decompositionRestrict h) • x))`. `Polynomial.map_prod` +
  `map_sub/map_X/map_C`, then `congr 1` closes the per-factor goal — **the identity
  `s₀ • (h • x) = (s₀ * dr h) • x` is definitional** (P46's `decompositionRestrict_smul` is
  `rfl`, and the subgroup-product action unfolds to composition). The probe's prepared
  `mul_smul`-rewrite block was dead code; `congr 1` alone finishes.
- **`map_fullProdXSubSMul_eval`**: at `x`, the transported polynomial is
  `∏_{h} (x − (s₀ * dr h) • x)` (`Polynomial.eval_prod`) — up to the sign `(−1)^{|H|}`,
  Prop. 3's `∏_{s ↦ σ̄} (s·x − x)`, parametrized by `H`.
- **`decompositionFiberEquiv`**: `h ↦ s₀ * dr h` is a bijection `H ≃ fiber(σ̄)`
  (`Equiv.ofBijective`): injective by P46's `decompositionRestrict_injective` +
  `mul_left_cancel`; surjective by P50's exactness — `s₀⁻¹s ∈ ker (decompositionQuotient)
  = range (decompositionRestrict)`. With `_apply_coe` (`rfl`) as the transport hook: any
  `∑`/`∏` over the lifts of `σ̄` becomes a `∑`/`∏` over `H` by `Equiv.prod_comp`-style
  reindexing. (This is the *explicit* form of P52's first-isomorphism packaging — the
  bijection itself, which the abstract `MulEquiv` does not directly give.)
- Supporting: `decompositionQuotient_decompositionRestrict` (`= 1`, pointwise composite
  triviality via `DFunLike.congr_fun`) and `decompositionQuotient_mul_decompositionRestrict`.

## Mathlib API that did the real work

`Polynomial.map_prod` + `map_sub`/`map_X`/`map_C` + `eval_prod`; `Equiv.ofBijective`;
`MonoidHom.mem_ker`, `mul_inv_cancel_left`, `mul_left_cancel`;
`MulSemiringAction.toRingAut` (P23's ring-automorphism device, here transporting
polynomials). House note: the style linter rejects goal-changing `show` — use `change`
(bit this pass once).

## Build + headline

Host `lake build` green (zero warnings after the `show`→`change` fix); new file imported in
`Anabelian.lean`; `scripts/preflight.sh` CLEAN. All 6 `#print axioms` standard-only; zero
`axiom` declarations project-wide. **HEADLINE: the lift-set identity — the fiber of
`decompositionQuotient` is the coset `s₀·H` as an explicit bijection, and
`f.map s₀ = ∏_{h ∈ H} (X − (s₀·dr h)·x)` — Prop. 3's product over the lifts is computable,
axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. D1 N/A; D2 untouched. R1–R3 untouched.

## Scope: the reindexing exists; the divisibilities are next (Pass 57+)

**Pass 57 options** (Prop. 3's two directions):
- **(i) `a ∣ b`**: coefficients of `σ̄F − F` (over `B = 𝒪_L ∩ K'`) are `σ̄c − c`, each
  divisible by `a = σ̄y − y` — P25's `smul_sub_dvd_of_mem_closure` in the `D(B)`-action,
  needing `B = 𝒪_K[y]`-form generation: P54's `exists_generator_extensionIntegers` at
  `(K, K')` gives `𝒪_{K'} = 𝒪_K[y]`; the transport `𝒪_{K'} ≅ B` (P43-flavor: `𝒪_L ∩ K' =
  𝒪_{K'}` for the tower — the base-independence of the integral closure) may need its own
  brick — check `ExtensionCanonical.lean` first. Then evaluate at `x` via P55 descent + P56
  transport: `(σ̄F − F).map (comapRingHom)` evaluated at `x` = `(σ̄f)(x) − 0` = `±b`.
- **(ii) `b ∣ a`**: monic division `g(X) − ι y = F·q` over `B` (F monic by P55; remainder
  vanishes by the degree/root argument), transported along `σ̄`, evaluated at `x`.
R1–R3 remain the distant, must-be-earned targets.

### Pass 57 (2026-07-03) — `𝒪_L ∩ K' = 𝒪_{K'}`, and the coefficient telescoping at `B`

**Mathematics; ledger delta 0 / 0.** The transport gap between the quotient theory (stated on
`B = 𝒪_L ∩ K'`) and the generator technology (stated on `𝒪_{K'}`) is closed by a 4-line
identification; on top of it, the arithmetic half of Prop. 3's direction (i) and the concrete
left side of the sum formula. `Anabelian/ExtensionComapIntegers.lean`, 9 declarations, all
standard-axioms-only.

## Scope choice (HANDOFF option (A), extended to the telescoping)

The planned brick was the `𝒪_{K'} ≅ B` transport; the inventory showed the identification is
a *one-lemma* affair (`isIntegral_algebraMap_iff` — integrality doesn't care whether a
`K'`-element is tested in `K'` or in `L`), so the pass carried through to what the transport
unblocks: P54's generator on `B`, and with it P25's telescoping and P53's `addVal`
identification, both of whose hypothesis packages become theorems at `B`.

## What was proved + the method

- **`extensionIntegers_comap_eq`**: `(𝒪_L).comap (algebraMap K' L) = 𝒪_{K'}` — SetLike.ext +
  `mem_extensionIntegers_iff` twice + `isIntegral_algebraMap_iff ((algebraMap K' L).injective)`.
  (P43 proved the `L`-level base-independence; this is the `K'`-level comap form the P50–56
  files actually use. Note it needs no separability — pure integrality transfer.)
- **`comapIntegersEquiv`**: hand-rolled value-preserving iso (all fields `Subtype.ext rfl`;
  membership transported by `▸` on the identification) — deliberately NOT
  `RingEquiv.subringCongr`, avoiding `toSubring` coercion friction. **DVR on `B`** by
  `RingEquivClass.isDiscreteValuationRing` transport (house-idiom nested name, P35 source).
- **`baseToComapRingHom`** + `coe_…` (`rfl`) + `comapIntegersEquiv_comp_extensionAlgebraMap`
  (the iso matches the two base maps — `Subtype.ext` + `coe_extensionAlgebraMap`).
- **`exists_generator_comap`**: P54 at `(K, K')` transported: `RingHom.map_closure` turns the
  closure of the generating set into the closure of its image; `Set.image_union`/`_singleton`
  + `Set.range_comp` + the base-map matching identify the image set; `map e ⊤ = ⊤` by
  surjectivity.
- **`exists_generator_comap_spec` (HEADLINE)**: one `y` with (1) `B = 𝒪_K[y]`; (2)
  `(σ̄y − y) ∣ (σ̄c − c)` for all `σ̄ ∈ D(B)`, `c ∈ B` — P25's `smul_sub_dvd_of_mem_closure`
  with `hfix` = `AlgEquiv.commutes` (decomposition elements fix `algebraMap K K'`-images,
  `smul_baseToComapRingHom_range_eq`) and `hc` trivial from generation; (3)
  `lowerIndex K B σ̄ = addVal_B (σ̄y − y)` — P53's `lowerIndex_eq_addVal` applied at `B`
  (DVR instance from this pass). **(2) is the arithmetic half of Prop. 3's `a ∣ b`; (3) is
  the sum formula's left side, concrete.**

Probe: 3 mechanical rounds (structure-field `push_cast` replaced by plain defeq `map_mul`
applications; `Subring.map_closure` is namespaced `RingHom.map_closure`; `⇑↑e` vs
`⇑e.toRingHom` display forms must match syntactically for `rw` — state `have`s in the
`toRingHom` form).

## Mathlib API that did the real work

`isIntegral_algebraMap_iff`; `IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing`;
`RingHom.map_closure`, `RingHom.coe_range`, `Set.image_union`/`image_singleton`/`range_comp`;
`AlgEquiv.commutes`; P25's telescoping engine + P53's `lowerIndex_eq_addVal` + P54's
`exists_generator_extensionIntegers` as black boxes.

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN.
All 9 `#print axioms` standard-only; zero `axiom` declarations project-wide. **HEADLINE:
`𝒪_L ∩ K' = 𝒪_{K'}` (the comap-level canonicity), and at `B = 𝒪_L ∩ K'` a single generator
`y` with the coefficient telescoping `(σ̄y − y) ∣ (σ̄c − c)` and the concrete
`i_{K'/K}(σ̄) = addVal_B (σ̄y − y)` — Prop. 3's direction-(i) arithmetic and its left side,
axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. D1 N/A; D2 stays inside P29's proofs.
  R1–R3 untouched.

## Scope: direction (i)'s evaluation half is next (Pass 58+)

**Pass 58: finish `a ∣ b`.** Assemble: P55's descent (`F` over `B` with `F.map (comapRingHom)
= f`), P57's telescoping (`a ∣ σ̄c − c` for every coefficient `c` of `F`), and P56's lift-set
identity (`(σ̄f)(x) = ∏_h (x − (s₀·dr h)·x)`). Shape: `σ̄F − F` has all coefficients divisible
by `a` ⟹ `a ∣ (σ̄F − F).eval₂/(map) at anything integral` — in particular at `x` (through
`comapRingHom : B →+* 𝒪_L`, which needs `σ̄`-equivariance of the map `B[X] → 𝒪_L[X]` against
the two actions: the D(B)-action downstairs vs the lift `s₀`-action upstairs — the
compatibility `comapRingHom (σ̄ • c) = s₀ • (comapRingHom c)` for `s₀ ↦ σ̄` is the one
missing small lemma; it is P50's `algebraMap_decompositionQuotient_smul` read backwards).
Then `(σ̄f)(x) − f(x) = (σ̄f)(x) = ±b` gives `a ∣ b` (with `a` viewed in `𝒪_L` via
`comapRingHom` — note `addVal_L (ι a)` vs `addVal_B a` is the `e'`-dilation, NOT needed for
bare divisibility). After that: direction (ii) (monic division), then the bookkeeping.
R1–R3 remain the distant, must-be-earned targets.

### Pass 58 (2026-07-03) — Prop. 3 direction (i): `a ∣ b`, proved

**Mathematics; ledger delta 0 / 0.** The first of Serre IV §1 Prop. 3's two divisibilities:
`ι(σ̄y − y) ∣ ∏_{s ↦ σ̄} (x − s·x)` in `𝒪_L`, abstract and hypothesis-free at `𝒪_L`.
`Anabelian/RamificationLiftDvd.lean`, 5 declarations, all standard-axioms-only.

## Scope (HANDOFF's Pass-58 task, exactly)

The three pieces the handoff named, then the assembly:

- **`comapRingHom_decompositionQuotient_smul`** — `ι(σ̄ • c) = s₀ • ι(c)`: literally
  `Subtype.ext` of P50's `algebraMap_decompositionQuotient_smul` (the handoff's "P50 read
  backwards" was right — one line). Polynomial level (`map_comapRingHom_smul`):
  `(σ̄ • F).map ι = (F.map ι).map (toRingAut s₀)` by `Polynomial.ext` + `coeff_map`/
  `coeff_smul` + the element lemma (note: `ext` on polynomials over `↥A` descends to
  `L`-level coercions — wrap the element lemma in `congrArg Subtype.val`; bit this pass
  once).
- **`dvd_eval_of_dvd_coeff`** — `(∀ n, d ∣ P.coeff n) → d ∣ P.eval z`:
  `eval_eq_sum_range` + `Finset.dvd_sum`, 3 lines, generic (verified absent from Mathlib in
  this form).
- **`comapRingHom_smul_sub_dvd_liftProd`** (abstract headline): `a = σ̄y − y` divides every
  coefficient of `σ̄F − F` (P57's telescoping + `coeff_sub`/`coeff_smul`); `map_dvd` pushes
  along `ι`; `dvd_eval_of_dvd_coeff` at `x`; and the evaluation computes —
  `map_sub`/`eval_sub`, the polynomial equivariance, P55's `hF`, **P56's
  `map_fullProdXSubSMul_eval`** and **P55's `fullProdXSubSMul_eval` (`f(x) = 0`)** — to
  `∏_h (x − (s₀ · dr h)·x) − 0`. Exactly Serre's five-line argument, with every line a named
  brick from P50–57.
- **`exists_generator_dvd_liftProd`** (the `𝒪_L` form): `exists_generator_comap_spec` (P57)
  provides `y` with the telescoping and the `i_{K'/K} = addVal` identification;
  `exists_fullProdXSubSMul_lift_extensionIntegers` (P55) provides `F` per `x`; the abstract
  headline assembles. One `y`, both conclusions, no hypotheses beyond the ambient
  tower/Galois/finiteness instances.

## Probe experience

Compiled on the second try (the single fix: the `congrArg Subtype.val` wrap noted above).
**Build note:** the project file elaborates slowly (~15 min; the `𝒪_L` instantiation's
instance context is expensive) — clean within default heartbeats, but expect the cost when
rebuilding; consider isolating further Prop.-3 instantiations in their own files so
incremental builds stay cheap.

## Mathlib API that did the real work

`Polynomial.coeff_smul`/`coeff_sub`/`coeff_map`/`map_sub`/`eval_sub`/`eval_eq_sum_range`;
`Finset.dvd_sum`, `Dvd.Dvd.mul_right`, `map_dvd`; P50's action-compatibility, P55's descent +
`eval = 0`, P56's lift-set identity, P57's telescoping — all as black boxes (the pass adds
~40 lines of glue to ~8 passes of substrate).

## Build + headline

Host `lake build` green; new file imported in `Anabelian.lean`; `scripts/preflight.sh` CLEAN.
All 5 `#print axioms` standard-only; zero `axiom` declarations project-wide. **HEADLINE:
Serre IV §1 Prop. 3, direction (i) — `ι(σ̄y − y) ∣ ∏_{s ↦ σ̄} (x − s·x)` in `𝒪_L`, proved
axiom-free, hypothesis-free at `𝒪_L`, with the same `y` carrying the concrete
`i_{K'/K}(σ̄) = addVal_B(σ̄y − y)`.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. D1 N/A; D2 stays inside P29's proofs.
  R1–R3 untouched.

## Scope: direction (ii) is next (Pass 59+)

**Pass 59: `b ∣ a`** — Serre's converse. Ingredients: `y = g(x)` for `g` over `𝒪_K` (P54's
generation of `𝒪_L` over `𝒪_K` at the same `x` — extract the polynomial from
`Subring.closure`-membership, or work with `Algebra.adjoin`-style representation); the monic
division `g(X) − C (ι y) = f·q + r` in `𝒪_L[X]`... — better per Serre: divide in `B[X]` by
P55's monic `F`: `G := (g's image in B[X]) − C y = F·q + r` with `natDegree r < natDegree F`;
evaluate the `ι`-image at `x`: `r`'s image kills `x`... the remainder-vanishing needs the
`K'`-independence of `1, x, …, x^{d−1}` (`d = [L:K']` — from `L = K'(x)`, which follows from
`𝒪_L = 𝒪_K[x] ⊆ K'[x]`); then apply `σ̄` to the division identity (coefficients in `B`),
map along `ι`, evaluate at `x`: `g(x) − ι(σ̄y) = (σ̄f)(x)·(σ̄q-image)(x) = ±b·(…)`, and
`g(x) = ι y`… wait — `g(x) = y`'s image: `ι y = g(x)` by choice of `g`. LHS
`= ι y − ι (σ̄ y) = −ι(a)`. Hence `b ∣ ι(a)`. Scope tightly: the polynomial-representation
brick (`∃ g over 𝒪_K-image, eval x g = ι y`) + the division + remainder-vanishing may
each be their own pass; clean partial > half-discharge. After (ii): the `addVal` bookkeeping
((iii): `addVal` of the fiber product = `Σ_h i_G(s₀·dr h)` via P53–54 + P56; the
`e'`-dilation `addVal_L ∘ ι = e' · addVal_B`), then the Prop. 3 assembly. R1–R3 remain the
distant, must-be-earned targets.

### Pass 59 (2026-07-03) — the `addVal` bookkeeping (Prop. 3's measuring layer)

**Mathematics; ledger delta 0 / 0.** Both sides of Serre IV §1 Prop. 3's sum formula are now
readable through `addVal`: the left side via the `e'`-dilation along the tower inclusion, the
right side via the fiber sum. `Anabelian/RamificationAddVal.lean`, 5 declarations, all
standard-axioms-only.

## Scope choice (HANDOFF option (A) — self-contained DVR/`ℕ∞` arithmetic first)

As recommended: no new representation machinery, pure valuation bookkeeping; after this pass
the sum formula lacks only direction (ii) and the assembly.

## What was proved + the method

- **`isUnit_comapRingHom_iff`**: `IsUnit (ι c) ↔ IsUnit c` for `ι : B = A ∩ K' → A`. The
  nontrivial direction: from a unit `w` with `↑w = ι c`, the inverse `↑w⁻¹` has underlying
  `L`-value `(algebraMap K' L c)⁻¹ = algebraMap K' L (c⁻¹)` (`map_inv₀` + uniqueness of
  inverses in `L`), and it lies in `A` (it is `↑w⁻¹`!), so `(c : K')⁻¹ ∈ B` (`mem_comap`)
  and `c` is a unit (`mul_inv_cancel₀`). The multiplicative sibling of P50's `𝔪`-reflection.
- **`addVal_comapRingHom`** (the `e'`-dilation): `addVal_A (ι c) = addVal_B c ·
  addVal_A (ι π_B)` for `π_B` irreducible. `c = u·π^n` ⟹ `ι c = ι u · (ι π)^n` with `ι u` a
  unit (`addVal_eq_zero_iff`), so `addVal = n • e' = ↑n · e'` (`nsmul_eq_mul`); the `c = 0`
  case is `⊤ = ⊤ · e'` via `ENat.top_mul` and `e' ≠ 0` (from the unit transfer:
  `ι π_B` is a non-unit). Stated abstractly for any DVR pair `(A, B)` — at `𝒪_L` the
  instances are P35 + P57.
- **`addVal_liftProd`** (the fiber sum): at `𝒪_L`, generator `x`,
  `addVal (∏_h (x − (s₀·dr h)·x)) = Σ_h i_{L/K}(s₀·dr h)` — `addVal_prod` (generic, 6-line
  `Finset.induction_on`), then per factor P53's `lowerIndex_eq_addVal` (with `hgen` the
  explicit hypothesis — the assembly pass will feed P54's generator once, shared with P58's
  divisibility) and `addVal_neg` for `x − s·x = −(s·x − x)`.
- Generic bricks: `addVal_neg` (mutual divisibility + `addVal_le_iff_dvd` — no unit
  juggling), `addVal_prod`.

Probe: 2 mechanical rounds (`Irreducible.not_unit` → `not_isUnit`; in the dilation, rewrite
with `addVal_def' u hπ n` directly instead of a pre-substituted `have` — `rw [hu]`
substitutes `c` everywhere and stales any `have` phrased in terms of `c`).

## Mathlib API that did the real work

`addVal_le_iff_dvd`, `addVal_eq_zero_iff`, `addVal_def'`, `addVal_mul`/`addVal_pow`,
`eq_unit_mul_pow_irreducible`; `ENat.top_mul`; `map_inv₀`, `eq_inv_of_mul_eq_one_right`,
`mul_inv_cancel₀`, `isUnit_iff_exists_inv`; `Finset.induction_on`; `nsmul_eq_mul`.

## Build + headline

Host `lake build` green (2.8 s — fresh file, per the P58 build caution); imported in
`Anabelian.lean`; `scripts/preflight.sh` CLEAN. All 5 `#print axioms` standard-only; zero
`axiom` declarations project-wide. **HEADLINE: the `addVal` bookkeeping of Prop. 3 — the
`e'`-dilation `addVal_A(ι c) = addVal_B(c)·e'` (with the two-way unit transfer) and the fiber
sum `addVal(∏_{s ↦ σ̄}(x − s·x)) = Σ_{s ↦ σ̄} i_{L/K}(s)` — both sides of the sum formula
`addVal`-readable, axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. D1 N/A; D2 stays inside P29's proofs.
  R1–R3 untouched.

## Scope: direction (ii) is the last gap (Pass 60+)

**Pass 60 options:**
- **(B) The polynomial-representation brick** (unblocks (ii)): every element of
  `Subring.closure (↑(RingHom.range ι₀) ∪ {x})` is `(P.map ι₀).eval x` for some
  `P : Polynomial` over the base — `Subring.closure_induction` (mirror P25's engine), or an
  `Algebra.adjoin` recast. Then `y`'s image in `𝒪_L` is `g(x)` with `g` over `𝒪_K`.
- Then **(ii) itself**: the monic division `G := g_B − C y = F·q + r` in `B[X]` (`F` = P55's
  monic descent; `Polynomial.modByMonic` + degree), remainder-vanishing via the
  `K'`-independence of `1, x, …, x^{d−1}` (`d = natDegree F = |H|`, P55; independence from
  `L = K'(x)` ⟸ `𝒪_L = 𝒪_K[x]`), transport along `σ̄` (coefficients in `B`), map along
  `ι`, evaluate at `x` ⟹ `b ∣ ι(a)`.
- Then the **assembly**: `Associated (ι a) b` (`associated_of_dvd_dvd`, mind the
  `∏(x − s·x)` vs `∏(s·x − x)` sign — `(−1)^{|H|}`, a unit) ⟹ `addVal` equal ⟹ with P57(3),
  P59's dilation + fiber sum: **`e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)`** — Prop. 3.
R1–R3 remain the distant, must-be-earned targets.

### Pass 60 (2026-07-03) — polynomial representation + `L = K'(x)` (direction (ii)'s substrate)

**Mathematics; ledger delta 0 / 0.** Two closure inductions: membership in
`𝒪_K[x]`-closure is polynomial representation, and the same generator generates `L` as a
field over every intermediate `K'`. `Anabelian/ExtensionGeneratorRep.lean`, 4 declarations,
all standard-axioms-only.

## Scope choice (HANDOFF's Pass-60 task + one look-ahead brick)

The planned brick was the representation lemma; `adjoin_generator_eq_top` was added because
it needs no polynomial machinery at all (a second, direct closure induction — membership in
the intermediate field — beats routing through `eval₂`/`aeval` plumbing) and it is exactly
what direction (ii)'s remainder-vanishing will consume.

## What was proved + the method

- **`exists_polynomial_map_eval_eq`** (generic, any `f : R →+* S`):
  `z ∈ Subring.closure (range f ∪ {x}) → ∃ P, (P.map f).eval x = z` —
  `Subring.closure_induction` with `C r`/`X`/`0`/`1`/`P+Q`/`−P`/`P·Q`. At `𝒪_L`
  (`exists_polynomial_generator_rep`): every integer is `(g.map (extensionAlgebraMap)).eval
  x` — the element-by-element `𝒪_L = 𝒪_K[x]`.
- **`comapRingHom_comp_baseToComapRingHom`** — `ι ∘ (𝒪_K → B) = extensionAlgebraMap K L`
  (`Subtype.ext` + the scalar tower). Moves `g`'s coefficients between the `B`-route and the
  direct route in the coming division.
- **`adjoin_generator_eq_top`** — `IntermediateField.adjoin K' {(x:L)} = ⊤`: inner closure
  induction shows every integer's value lies in the adjoin (base case: `coe_extensionAlgebraMap`
  + `IsScalarTower.algebraMap_apply K K' L` + `algebraMap_mem`; generator: `subset_adjoin`;
  ops: `add_mem`/`neg_mem`/`mul_mem` with `simpa` handling the subtype-value pushes); outer:
  `mem_or_inv_mem` + `inv_mem` + `inv_inv` extends from `𝒪_L` to `L`.

Probe: compiled clean once run correctly — one environment lesson (below), plus the usual
`_root_.eq_top_iff` disambiguation and two `simpa`→`simp` lints.

## House/environment notes

- **Do not `cd` into the scratchpad to run probes**: `lake env lean` outside the project
  root loses the project search path and (worse) `elan` may download a fresh toolchain from
  the scratchpad's absence of a pinned `lean-toolchain`. Run `lake env lean <abs-path>` from
  the project root — as all previous passes did (bit this pass once; a stray v4.31.0
  toolchain was downloaded to elan's cache, harmless but wasteful).
- P57's `ExtensionComapIntegers` does NOT import `RamificationQuotient` (its telescoping is
  internal to `B`); anything using `comapRingHom` must import `RamificationQuotient`
  explicitly.

## Mathlib API that did the real work

`Subring.closure_induction`; `Polynomial.map_C/map_X/map_add/map_neg/map_mul` + `eval_*`;
`IntermediateField.algebraMap_mem`, `subset_adjoin`, `inv_mem`;
`IsScalarTower.algebraMap_apply`; `ValuationSubring.mem_or_inv_mem`.

## Build + headline

Host `lake build` green (2.7 s, fresh file); imported in `Anabelian.lean`;
`scripts/preflight.sh` CLEAN. All 4 `#print axioms` standard-only; zero `axiom` declarations
project-wide. **HEADLINE: closure membership is polynomial representation (every integer of
`L` is `g(x)` for `g` over `𝒪_K`), and `L = K'(x)` for every intermediate `K'` — direction
(ii)'s substrate, axiom-free.**

## Ledger delta + rule-2

- **0 / 0.** Axiom-free. **No new `structure`/`class`** ⟹ no rule-2 obligation; no
  load-bearing-hypothesis claims ⟹ no owed witness. D1 N/A; D2 stays inside P29's proofs.
  R1–R3 untouched.

## Scope: direction (ii)'s core is next (Pass 61+)

**Pass 61: the remainder-vanishing brick** — for `r : Polynomial ↥B` with
`(r.map ι).eval x = 0` and `r.natDegree < Fintype.card (D_{K'}(𝒪_L))`: `r = 0`. Route:
(a) move `r` to `K'[X]` along `B.subtype` (nonzero preserved — `Polynomial.map_injective` of
the subtype injection); (b) its `aeval` at `(x:L)` vanishes (value-level: `Polynomial.eval_map`
/ `hom_eval₂` chains — the coercion `𝒪_L → L` is a ring hom); (c) `minpoly K' x` has degree
`= finrank K' K'⟮x⟯` (`IntermediateField.adjoin.finrank`, `x` integral) `= finrank K' L`
(P60's `adjoin_generator_eq_top`) `= Fintype.card Gal(L/K')` (`IsGalois.card_aut_eq_finrank`)
`= Fintype.card (D_{K'}(𝒪_L))` (P55's `decompositionSubgroup_extensionIntegers_restrict_eq_top`
+ card-of-⊤); (d) `minpoly.degree_le_of_ne_zero` contradicts (b)+(c) unless `r = 0`. Then
**Pass 62: the division + `b ∣ a`**; **Pass 63: the Prop. 3 assembly**. R1–R3 remain the
distant, must-be-earned targets.

### Pass 61 (2026-07-03) — the remainder-vanishing brick

**Mathematics; ledger delta 0 / 0.** A polynomial over `B` of degree `< [L:K']` whose
`ι`-image kills `x` is zero — the minimal-polynomial degree count that will kill the
remainder in direction (ii)'s division. `Anabelian/RamificationMinpolyBound.lean`,
1 declaration, standard-axioms-only.

## Method (exactly the HANDOFF route)

(a) `r ≠ 0 ⟹ r.map B.subtype ≠ 0` (`Polynomial.map_injective`); (b) the `K'`-form kills
`x`: apply `(𝒪_L).subtype` to `hr`, reassociate the eval₂ homs (`Polynomial.eval_map` +
`hom_eval₂` upstairs, `aeval_def` + `eval₂_map` downstairs; the two composite homs
`B → 𝒪_L → L` and `B → K' → L` are equal by `RingHom.ext fun b => rfl`); (c) the count:
`adjoin.finrank` + P60's `adjoin_generator_eq_top` + `finrank_top'` +
`IsGalois.card_aut_eq_finrank` (**Nat.card-valued** in current Mathlib — the one probe fix)
+ P55's `D = ⊤` + `Subgroup.card_top`; (d) `minpoly.degree_le_of_ne_zero` +
`natDegree_map_eq_of_injective` + `omega`.

## Build + headline

`lake build` green (2.7 s, fresh file); preflight CLEAN. **HEADLINE: the
remainder-vanishing brick — deg `< [L:K']` + kills `x` ⟹ zero — proved axiom-free; the last
new mathematics before Prop. 3.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next: Pass 62 — the division ⟹ `b ∣ a`; Pass 63 — the assembly.

### Pass 62 (2026-07-03) — Prop. 3 direction (ii): `b ∣ a`, proved

**Mathematics; ledger delta 0 / 0.** `∏_{s ↦ σ̄} (x − s·x) ∣ ι(σ̄y − y)` for every `y ∈ B`
— Serre's monic-division argument, assembled entirely from P55–P61 bricks.
`Anabelian/RamificationDivision.lean`, 1 declaration, standard-axioms-only.

## Method (the HANDOFF (2) route, exactly)

Representation (P60) → commuting square (P60) → `G := g_B − C y` kills `x` after `ι` →
division by P55's monic `F` (note: `Polynomial.modByMonic_add_div (p q)` is now
hypothesis-free in Mathlib — the identity is trivially true for non-monic `q`) → the
remainder kills `x` with degree `< natDegree F = |H|` (`degree_modByMonic_lt` needs the monic
✓; `natDegree_lt_natDegree`; the `r = 0` case handled by `Fintype.card_pos`) → **P61 kills
it** → exact identity `G = F·(G /ₘ F)` → `σ̄`-transport (`smul_sub`/`smul_mul'`/
`Polynomial.smul_C`; `σ̄ • g_B = g_B` coefficient-wise by P57's hfix — with the
`congrArg Subtype.val` wrap under polynomial `ext`, the P58 idiom) → map along `ι`, evaluate
at `x` (P58's `map_comapRingHom_smul`, P55's `hF`, P56's `map_fullProdXSubSMul_eval`) →
`−ι(a) = ∏·c` → `dvd_neg`. **Notably the statement is uniform in `y`** — no generator
property of `y` is used, so the assembly can feed it P57's `y` directly.

Probe: 2 mechanical rounds (`modByMonic_add_div` signature change; the `congrArg
Subtype.val` wrap — both already-catalogued idioms).

## Build + headline

`lake build` green (3.7 s, fresh file); preflight CLEAN. **HEADLINE: Serre IV §1 Prop. 3,
direction (ii) — the lift-set product divides `ι(σ̄y − y)`, for every `y ∈ B` — proved
axiom-free. Both divisibilities of Prop. 3 now hold; only the assembly remains.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next: Pass 63 — the assembly: obtain `x` (P54) and `y` (P57) once; P58's `a ∣ b` + P62's
`b ∣ a` ⟹ mutual divisibility ⟹ `addVal` equal (`addVal_le_iff_dvd` both ways); read LHS
by P57(3) + P59's dilation, RHS by P59's fiber sum ⟹
**`e'·i_{K'/K}(σ̄) = Σ_h i_{L/K}(s₀·dr h)`** — Prop. 3.

### Pass 63 (2026-07-03) — SERRE IV §1 PROP. 3, proved (the sum formula)

**Mathematics; ledger delta 0 / 0 — a MILESTONE.** The sum formula
`i_{K'/K}(σ̄) · e' = Σ_{h} i_{L/K}(s₀·dr h)` — Serre IV §1 Prop. 3, the arithmetic engine of
Lemma 5 / `φ`-transitivity / Herbrand's theorem, and the wall first named at Pass 47 — is
proved, axiom-free. `Anabelian/RamificationSumFormula.lean`, 1 declaration,
standard-axioms-only; **the probe compiled on the first try** (all fourteen feeding bricks
fit exactly).

## The statement (and two design wins)

`lowerIndex_decompositionQuotient_mul_eq_sum`: for every `s₀` and every irreducible `π` of
`B`, `lowerIndex K B (dq s₀) * addVal_{𝒪_L}(ι π) = Σ_h lowerIndex K 𝒪_L (s₀ * dr h)`.
- **Generator-free**: `lowerIndex` is intrinsic (P51's design decision paying out at the
  finish line) — `x`, `y`, `F`, `g` all disappear from the statement.
- **Uniform in `σ̄`**: no `σ̄ ≠ 1` hypothesis. At `σ̄ = 1` the LHS is `⊤·e' = ⊤` and the RHS
  sum contains `lowerIndex 1 = ⊤` — the `ℕ∞` design (P51) absorbs Serre's "both sides are
  `+∞`" convention silently.

## The proof (eight lines)

`x` from P54; `y` from P57's spec; `F` from P55; **h1** `= ι(σ̄y−y) ∣ ∏` (P58's abstract
telescoping direction, fed by P55's descent + P57's telescoping); **h2** `= ∏ ∣ ι(σ̄y−y)`
(P62's division direction); mutual divisibility ⟹ `addVal` equal (`addVal_le_iff_dvd` both
ways + `le_antisymm`); rewrite the left by P59's `addVal_comapRingHom` (the `e'`-dilation)
and P57(3) (`i_{K'/K} = addVal_B(σ̄y−y)`), the right by P59's `addVal_liftProd` (the fiber
sum). Done.

## The arc, in retrospect (P50–63, fourteen passes, `0/0` throughout)

Skeleton (50) → currency `i_G` (51) → surjectivity (52) → concrete `i_G` (53) →
monogenicity discharge (54) → Serre's polynomial + descent (55) → lift-set identity (56) →
`𝒪_L ∩ K' = 𝒪_{K'}` + telescoping (57) → direction (i) (58) → `addVal` bookkeeping (59) →
representation + `L = K'(x)` (60) → remainder-vanishing (61) → direction (ii) (62) →
**assembly (63)**. Every pass one rung, nothing half-built, zero axioms at every step — the
discipline the ledger exists to enforce, applied to a fourteen-pass wall.

## Build + headline

`lake build` green (2.7 s, fresh file); preflight CLEAN. `#print axioms`:
`[propext, Classical.choice, Quot.sound]` — nothing else. **HEADLINE: SERRE IV §1 PROP. 3 —
`e' · i_{K'/K}(σ̄) = Σ_{s ↦ σ̄} i_{L/K}(s)` — proved in Lean 4 from the standard axioms,
with zero project axioms.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched — this
is structure of a *given* tower, recovering nothing from an abstract group.

## Next (Pass 64+): Serre IV §3 Lemma 5

Convert the `i`-sum into the `φ`-renumbering statement `(G/H)_{φ_{L/K'}(u)} = G_u H/H`:
Serre's proof takes `σ̄ ≠ 1`, sets `j(σ̄) := max_{s ↦ σ̄} i_G(s)` and shows
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j(σ̄) − 1)` by comparing the sum formula with `φ`'s explicit
form (P48's piecewise formula / P44's integral; the `H_u = H ∩ G_u` of P46 and the Lemma-1
membership forms of P51/P53 mediate). Sub-bricks to scope: the `max` over the fiber; the
sum-vs-`φ` computation (`Σ_h min(i_H-ish…)` — Serre's Lemma 4-flavored counting); then
Lemma 5, Prop. 15 (`φ`-transitivity), Prop. 14 (Herbrand). R1–R3 remain the distant,
must-be-earned targets.

### Pass 64 (2026-07-03) — governance: the flat→folders refactor

**Infrastructure; ledger delta 0 / 0; no mathematical content changed.** The restructure
deferred since Pass 42 ran as its own dedicated pass, per the rule that created it.

- `scripts/refactor.sh`: table extended from the Pass-40 snapshot (44 entries) to all 64
  files. New folders for the two post-P42 arcs: **`Herbrand/`** (Function, UpperNumbering,
  Slope, Formula, PsiSlope — P44–49) and **`Quotient/`** (Basic, Surjective, CharPoly,
  LiftSet, ComapIntegers, LiftDvd, AddVal, GeneratorRep, MinpolyBound, Division, SumFormula
  — P50–63); P41/P43 → `LocalField/Instance`/`Canonical`; P46/P51/P53 →
  `Ramification/Subgroup`/`LowerIndex`/`LowerIndexGenerator`; P54 →
  `Extension/MonogenicDischarge`.
- Executed as git-tracked renames (`git mv`); imports rewritten by exact-line-anchored sed
  (no substring hazards); root `Anabelian.lean` regenerated sorted. **Declaration names
  unchanged** — only module paths moved.
- Tooling made folder-aware: `preflight.sh` clause 1 (`glob` → recursive) and clause 2
  (`grep` → `-r --include`), `chain_check.py` (`os.listdir` → `os.walk`). The
  module-name→path mapping in `chain_check.py`'s `chain_of` already handled dots→slashes.
- Full rebuild verified (every module re-elaborated under its new name — including the
  ~15-min `Quotient/LiftDvd`); `scripts/preflight.sh` CLEAN; every `#print axioms` audit
  re-ran standard-only.

**HEADLINE: the source tree is now nine content folders; zero mathematical drift (renames
only, declaration names stable, audits re-verified).**

### Pass 65 (2026-07-03) — the fiber index profile (Lemma 5, brick A)

**Mathematics; ledger delta 0 / 0.** Serre IV §3, the counting inside Lemma 5's proof: for
a fiber maximizer `s₁`, `i_{L/K}(s₁·h) = min(i_H(h), j)` for every `h ∈ H` — hence
`Σ_{s ↦ σ̄} i(s) = Σ_h min(i_H(h), j)`, the shape the Herbrand `φ` counts.
`Anabelian/Quotient/IndexProfile.lean`, 4 declarations, all standard-axioms-only.

## Method

Everything is P51 calculus; no new ramification input. The heart
(`lowerIndex_mul_decompositionRestrict_eq_min`, abstract + `Normal`-free, stated on the
coset `s₁·drH`): `≥ min` is the subgroup inequality (`min_lowerIndex_le_lowerIndex_mul`)
with `i(dr h) = i_H(h)` (P51's `rfl` lemma). For `≤`: if `i(s₁) ≤ i_H(h)`, maximality gives
`i(s₁h) ≤ i(s₁) = min`; if `i_H(h) < i(s₁)`, suppose `i_H(h) < i(s₁h)` — then
`i_H(h) = i(dr h) = i(s₁⁻¹·(s₁·dr h)) ≥ min(i(s₁), i(s₁h)) > i_H(h)` (`lowerIndex_inv` +
`inv_mul_cancel_left`), absurd. Maximizers exist by `Finset.exists_max_image` (the coset
reparametrizes to itself under `h ↦ h₀h`, so the coset max IS a profile hypothesis);
fiber packaging via P56's `decompositionQuotient_mul_decompositionRestrict`; the `Σ min`
form by `Finset.sum_congr`.

House note: the `unusedFintypeInType` linter rejects `[Fintype …]` hypotheses not appearing
in the statement — use `[Finite …]` + `Fintype.ofFinite` in the proof (bit this pass once;
the sum lemma keeps `[Fintype]` since `∑ h : _` needs it in the type).

## Build + headline

`lake build` green, warning-free; preflight CLEAN. **HEADLINE: the fiber index profile —
`i(s₁·h) = min(i_H(h), j)` for a fiber maximizer, with the `Σ min` sum form — Lemma 5's
brick (A), axiom-free.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 66): the double-count `Σ_{h ∈ H} min(i_H(h), m) = Σ_{k<m} |H_k|` (level sets via
P51's `mem_ramificationGroup_iff_lt_lowerIndex`), then the P48 `φ`-identification, toward
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)` and Lemma 5.

### Pass 66 (2026-07-03) — the double count (Lemma 5, brick B1)

**Mathematics; ledger delta 0 / 0.** `Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|` — the level-set
double count that evaluates Pass 65's `Σ min`.
`Anabelian/Ramification/LowerIndexCount.lean`, 2 declarations, standard-axioms-only; the
probe compiled first try.

## Method

`enat_min_coe_eq_sum` (generic): `min x (m:ℕ∞) = Σ_{k ∈ range m} (if (k:ℕ∞) < x then 1
else 0)` by induction (`Finset.sum_range_succ`; the `n < x` case bumps the min via
`ENat.add_one_le_iff`, the `x ≤ n` case freezes it). Then `sum_min_lowerIndex_eq`:
`simp_rw` the decomposition, `Finset.sum_comm`, and per level `k` rewrite the indicator
predicate along **P51's Lemma 1** (`mem_ramificationGroup_iff_lt_lowerIndex`), finish with
`Finset.sum_boole` + `Fintype.card_subtype` + `Nat.card_eq_fintype_card`. Stated for ANY
`(K, A)` with `[Fintype D]` — at the assembly it applies to `H = D_{K'}(𝒪_L)`.

**Where the arc now stands:** P63 (sum formula) + P65 (profile) + P66 (double count) give,
for a fiber maximizer with finite `j`: `e'·i_{K'/K}(σ̄) = Σ_{k<j} (Nat.card H_k : ℕ∞)`.

## Build + headline

`lake build` green (2.6 s); preflight CLEAN. **HEADLINE: the double count
`Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|`, axiom-free — Pass 63's sum formula now reads
`e'·i_{K'/K}(σ̄) = Σ_{k<j} |H_k|`.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 67): the `φ`-bridge — `(Σ_{k<m} Nat.card H_k : ℝ) = |H_0|·(φ_{L/K'}(m−1)+1)`
via P48's `herbrandPhi_natCast` (check `ramificationOrders`' def) — and, separately, the
`e' = |H_0|` identification (inventory the descent's `e` facts first). Then
`i_{K'/K}(σ̄) − 1 = φ_{L/K'}(j − 1)`, then set-level Lemma 5.

### Pass 67 (2026-07-03) — the `φ`-bridge (Lemma 5, brick B2)

**Mathematics; ledger delta 0 / 0.** `Σ_{k ≤ n} |G_k| = |G_0|·(φ(n) + 1)` + the two cast
forms connecting Pass 66's `ℕ∞` count to Pass 48's `ℝ`-valued `φ`.
`Anabelian/Herbrand/SumBridge.lean`, 3 declarations, standard-axioms-only; probe compiled
first try (one `omit [Finite …] in` for the cast-only lemma — the unused-section-variable
gate again).

## Method

`Finset.sum_range_succ'` splits off the `k = 0` term; `herbrandPhi_natCast` (P48) gives the
`k ≥ 1` sum as `|G_0|·φ(n)`; `mul_div_cancel₀` absorbs. The `Nat.card`-`ℝ` form is
term-by-term `rfl` (`ramificationOrders` IS the cast); the `ℕ∞`-`ℕ` form is
`Nat.cast_sum`.

**The Lemma-5 numerical chain, fully typed:** `e'·i_{K'/K}(σ̄) =_{ℕ∞} Σ_{k<j} |H_k|`
(P63+P65+P66) `=_{cast}` the `ℕ`-sum `=_{ℝ}` `|H_0|·(φ_{L/K'}(j−1)+1)` (this pass, at
`H = D_{K'}(𝒪_L)`, `j = n+1`). Missing input: `e' = |H_0|`.

## Build + headline

`lake build` green (2.4 s); preflight CLEAN. **HEADLINE: the `φ`-bridge
`Σ_{k≤n} |G_k| = |G_0|·(φ(n)+1)`, axiom-free — the Lemma-5 numerical chain is fully typed,
pending only `e' = |H_0|`.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 68): `e' = |H_0|` — inventory the descent's `e`-facts (`Extension/
RamificationData`, `Extension/TotallyRamified`, P28–37) before designing; possibly
multi-pass.

### Pass 68 (2026-07-03) — `e'` in ideal form (the `e' = |H_0|` identification, left half)

**Mathematics; ledger delta 0 / 0 — and a decisive inventory find.** Mathlib's
`Mathlib/NumberTheory/RamificationInertia/` tree (Basic/Ramification/Inertia/Galois/
HilbertTheory/Unramified) contains **`Ideal.card_inertia_eq_ramificationIdxIn`** —
`Nat.card (P.inertia G) = ramificationIdxIn p S` for a Galois group action over Dedekind
domains with separable residue extension. Residue fields here are finite (P36), so
**`e' = |H_0|` reduces to identifying the project's objects with Mathlib's** — no
fundamental-identity machinery needs building. `Anabelian/Quotient/RamificationIdx.lean`,
4 declarations, standard-axioms-only.

## What was proved

- **`comapAlgebra`**: `Algebra ↥B ↥(𝒪_L)` := `(comapRingHom K' A).toAlgebra` — Mathlib's
  `Ideal.ramificationIdx` is now Algebra-based (`ramificationIdx (p : Ideal R) (P : Ideal
  S)` with `algebraMap R S` implicit — a signature change from the older RingHom form; bit
  the probe once). No canonical instance exists between these subtypes (different ambient
  fields) ⟹ no diamond. `algebraMap_comapAlgebra : algebraMap ↥B ↥A = comapRingHom K' A`
  is `rfl`.
- **`map_maximalIdeal_comapRingHom`**: `Ideal.map ι 𝔪_B = 𝔪_L^n` where
  `(n:ℕ∞) = addVal(ι π_B)`: `Irreducible.maximalIdeal_eq` + `Ideal.map_span` +
  `eq_unit_mul_pow_irreducible` + `span_singleton_eq_span_singleton` (associates) +
  `span_singleton_pow` (rewrite ORDER matters: expose `span{ϖ}^n` before folding to `𝔪^n`).
- **`ramificationIdx_comapRingHom`**: `Ideal.ramificationIdx 𝔪_B 𝔪_L = n` via
  `ramificationIdx_spec`; the non-inclusion `𝔪^n ⊄ 𝔪^{n+1}` by evaluating `ϖ^n` through
  P53's `mem_maximalIdeal_pow_iff_le_addVal`.

## Build + headline

`lake build` green (2.7 s); preflight CLEAN. **HEADLINE: Pass 59's `addVal`-form `e'` IS
Mathlib's `Ideal.ramificationIdx 𝔪_B 𝔪_L` (on the new `comapAlgebra` scaffold) — the left
half of the `e' = |H_0|` identification, axiom-free; Mathlib's
`card_inertia_eq_ramificationIdxIn` supplies `|inertia| = e` once the right half (instance
package + inertia matching) lands.**

## Ledger delta + rule-2

**0 / 0.** `comapAlgebra` instantiates the existing `Algebra` class — no new
`structure`/`class`, no rule-2 obligation; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 69): the instance package (Dedekind/finite/torsion-free/LiesOver/separable-residue
/IsGaloisGroup-invariance — note the invariance is P55's fixed-points descent in instance
form) and the inertia matching (`Ideal.inertia` vs `ramificationGroup … 0` — kernel vs
kernel via P23's `ramificationGroup_zero`); then `e' = |H_0|`, the numerical Lemma 5, the
set-level Lemma 5, Prop. 15, Prop. 14.

### Pass 69 (2026-07-03) — the `IsGaloisGroup` package (the `e' = |H_0|` gateway)

**Mathematics; ledger delta 0 / 0.** `IsGaloisGroup (D_{K'}(𝒪_L)) ↥B ↥𝒪_L` — Mathlib's
gateway class for the `RamificationInertia` machinery — established as an instance, its
three components each an existing project brick repackaged.
`Anabelian/Quotient/GaloisGroup.lean`, 4 instances, standard-axioms-only; probe compiled
first try.

## Method

Mathlib's `IsGaloisGroup G A B` = `{ faithful : FaithfulSMul G B, commutes : SMulCommClass
G A B, isInvariant : Algebra.IsInvariant A B G }` (read from
`FieldTheory/Galois/IsGaloisGroup.lean`). For `G = D_{K'}(𝒪_L)`, `A = B = 𝒪_L ∩ K'`,
`B = 𝒪_L`:
- **faithful**: agree on `A` ⟹ agree on `L` by `mem_or_inv_mem` + `map_inv₀` +
  `inv_injective` — the exact argument that ends P23's `iInf_ramificationGroup_eq_bot`,
  stated abstractly for any `(K', A)`.
- **commutes**: `b • s = comapRingHom b * s` (P68's `comapAlgebra`, `Algebra.smul_def` +
  the `rfl` `algebraMap_comapAlgebra`), `smul_mul'`, and `g • ι(b) = ι(b)` by
  `AlgEquiv.commutes` (decomposition elements are `K'`-algebra maps). Abstract.
- **isInvariant**: exactly P55's fixed-points descent; `D_{K'}(𝒪_L) = ⊤` (P55) converts
  `∀ g : D, g • b = b` into `∀ σ : Gal(L/K'), σ b = b`. At `𝒪_L` (the instance needs the
  tower + `[FiniteDimensional K' L] [IsGalois K' L]`).

## Build + headline

`lake build` green (2.9 s); preflight CLEAN. **HEADLINE: `D_{K'}(𝒪_L)` is a Galois group
for `B ⊆ 𝒪_L` in Mathlib's sense (faithful + commuting + invariant), axiom-free — the
gateway to `card_inertia_eq_ramificationIdxIn` is open.**

## Ledger delta + rule-2

**0 / 0.** All four declarations instantiate existing Mathlib classes — no new
`structure`/`class`, no rule-2 obligation; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 70): the remaining instances (`IsDedekindDomain` likely automatic;
`Module.Finite ↥B ↥𝒪_L` via P32 + restrictScalars along the P60 tower; torsion-free;
`𝔪_L.LiesOver 𝔪_B` from P50+P59; separable residue via finite-fields-perfect) and the
inertia matching (`Ideal.inertia` vs `ramificationGroup K' 𝒪_L 0`).

### Pass 70 (2026-07-03) — remaining instances + the inertia matching

**Mathematics; ledger delta 0 / 0.** The full hypothesis package for
`card_inertia_eq_ramificationIdxIn`, and a pleasant surprise: **the inertia matching is
definitional**. `Anabelian/Quotient/InertiaSetup.lean`, 7 declarations,
standard-axioms-only.

## The definitional dividend

Mathlib's `Ideal.inertia G I` (found in `RingTheory/Ideal/Defs.lean`, an `abbrev` for
`AddSubgroup.inertia`) is `{g | ∀ x, g•x − x ∈ I}` — and Pass 23 defined
`ramificationGroup K A i := (𝔪^(i+1)).inertia (D)` from exactly this device. So
`ramificationGroup K' A 0 = (𝔪_A).inertia (D_{K'}(A))` is `rw [ramificationGroup];
norm_num` (`pow_one`). The HANDOFF's anticipated "kernel-vs-kernel comparison" evaporated.

## The instances

- `isTorsionFree_comap` (`Module.IsTorsionFree ↥B ↥𝒪_L`): domains + injective inclusion;
  `isRegular_iff_ne_zero` + `mul_left_cancel₀` (note the current `IsTorsionFree` is the
  `IsRegular → IsSMulRegular` formulation).
- `liesOver_maximalIdeal` (`𝔪_L.LiesOver 𝔪_B`, generic `(K', A)`): `le_antisymm` of P50's
  `mem_maximalIdeal_of_comapRingHom` and P59's `isUnit_comapRingHom_iff` (the `LiesOver`
  field is `over : p = P.under A`; anonymous-constructor form — the `where over :=` form
  hit a parse quirk).
- `baseComapAlgebra` (`Algebra ↥𝒪[K] ↥B` via `baseToComapRingHom.toAlgebra`) +
  `isScalarTower_baseComap` (`IsScalarTower.of_algebraMap_eq'` fed by P60's commuting
  square — verbatim) + `moduleFinite_comap` (`Module.Finite.of_restrictScalars_finite` on
  P32's `Module.Finite ↥𝒪[K] ↥𝒪_L`).
- `isSeparable_residue`: `letI := Ideal.Quotient.field` on both quotients; `Finite` of
  `𝒪_L`'s residue (P36, defeq `ResidueField`), `Finite` of `B`'s via `Finite.of_injective`
  along the (automatic, LiesOver-derived) `algebraMap` of quotients (fields ⟹ injective);
  `Module.Finite.of_finite` ⟹ algebraic ⟹ Mathlib's finite-field separability chain closes
  by `infer_instance`.

Probe-verified as automatic: `IsDedekindDomain` for both rings (DVR ⟹ PIR ⟹ Dedekind; note
`Quotient.ComapIntegers` must be in the import chain for `B`'s DVR instance to be found —
the P60 import-visibility idiom again).

## Build + headline

`lake build` green (3.2 s); preflight CLEAN. **HEADLINE: every hypothesis of Mathlib's
`|inertia| = e` is in place, and the project's `G₀` IS Mathlib's `Ideal.inertia` —
definitionally. The application (`e' = |H₀|`) is next.**

## Ledger delta + rule-2

**0 / 0.** All declarations instantiate existing classes or match existing definitions — no
new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 71): apply `card_inertia_eq_ramificationIdxIn` +
`ramificationIdxIn_eq_ramificationIdx` + P68 ⟹ `e' = |H₀|`; then the numerical Lemma 5.

### Pass 71 (2026-07-03) — `e' = |H₀|`, proved (the identification closes)

**Mathematics; ledger delta 0 / 0.** The classical `e = |inertia|` for the Galois extension
`L/K'`: `(|H₀| : ℕ∞) = addVal_{𝒪_L}(ι π_B)` for any irreducible `π_B`.
`Anabelian/Quotient/InertiaCard.lean`, 2 declarations, standard-axioms-only.

## Method (four rewrites over the P68–70 package)

`ramificationGroup_zero_eq_inertia` (P70, definitional) →
`Ideal.card_inertia_eq_ramificationIdxIn` (Mathlib — every hypothesis from P68's
`comapAlgebra`, P69's `IsGaloisGroup`, P70's instances; `𝔪_B ≠ ⊥` =
`IsDiscreteValuationRing.not_a_field'`) → `ramificationIdxIn_eq_ramificationIdx`
(single-prime, `G` explicit) → P68's `ramificationIdx_comapRingHom`. The `ℕ∞` form handles
`addVal ≠ ⊤` via `addVal_eq_top_iff` + `WithTop.ne_top_iff_exists`. Two probe rounds
(unused-`Fintype` lint — `Finite D` is automatic from finite-dimensionality — and a
`mod_cast` that preferred `congrArg`).

## The four-pass identification, in retrospect (P68–71)

`e'`-in-ideal-form (68) → `IsGaloisGroup` (69) → instances + definitional inertia matching
(70) → application (71). Mathlib's `RamificationInertia` tree did the heavy lifting
(`|inertia| = e` itself); the project supplied the objects and the bridges — zero axioms
throughout, and two design decisions (P23's `Ideal.inertia`-based filtration, P51's
generator-free `lowerIndex`) made the matchings definitional or one-line.

## Build + headline

`lake build` green (2.7 s); preflight CLEAN. **HEADLINE: `e' = |H₀|` — the ramification
index of `L/K'` is the cardinality of its inertia group, proved axiom-free. Every input to
Lemma 5's numerical heart is now on the board.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 72): assemble the numerical Lemma 5 — the `ℕ∞`-level
`i_{K'/K}(σ̄)·e' = Σ_{k<j}|H_k|` (P63+P65+P66, with `j` finite for `σ̄ ≠ 1`), then the
`ℝ`-level readout via P67 + P71 ⟹ `i_{K'/K}(σ̄) = φ_{L/K'}(j−1) + 1`.

### Pass 72 (2026-07-03) — THE NUMERICAL LEMMA 5, proved (the assembly)

**Mathematics; ledger delta 0 / 0 — a MILESTONE.** Serre IV §3's numerical identity
`i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1` for every `σ̄ ≠ 1` — the identity from which
Lemma 5, `φ`-transitivity (Prop. 15), and Herbrand's theorem (Prop. 14) all follow.
`Anabelian/Quotient/NumericalLemmaFive.lean`, 1 declaration, standard-axioms-only.

## The statement (designed for its consumer)

`exists_lowerIndex_eq_herbrandPhi`: for `σ̄ = dq s₀ ≠ 1`, there exist `s₁` (same fiber),
`m, a : ℕ` with: the fiber-maximizer profile `∀ h, i(s₁·dr h) = min(i_H(h), m)`;
`(m : ℕ∞) = i_{L/K}(s₁)` (Serre's `j(σ̄)`); `(a : ℕ∞) = i_{K'/K}(σ̄)`; and
`(a : ℝ) = φ_{L/K'}(m − 1) + 1`. The profile and the two finiteness certificates are
exactly what the set-level Lemma 5 will consume. No `Fintype` hypothesis — `Finite D` is
automatic and `Fintype.ofFinite` supplies the proof-internal sums.

## The assembly (every link a named pass)

P65's maximizer + profile → `s₁ ≠ 1` (else `σ̄ = 1`) → `j ≠ ⊤` and `i(σ̄) ≠ ⊤` (P51's
`lowerIndex_eq_top_iff`; separation from `Ideal.iInf_pow_eq_bot_of_isLocalRing` — 𝒪_L
Noetherian by P29, `B` by DVR) → P63 at `s₁` (any irreducible `π_B`) → P65 profile sums →
P66 double count → P71 (`addVal(ι π) = (|H₀| : ℕ∞)`) → P67 (`sum_natCard_enat_eq` down to
`ℕ`, `natCast_sum_natCard_eq` up to `ℝ`) → cancel `|H₀| ≠ 0` → case `m = 0` via
`herbrandPhi_eq_id` (`φ(−1) = −1`), case `m = n+1` via the cast-argument identity.

## Probe experience (cast-plumbing lessons, now catalogued)

Four rounds, all cast/plumbing: (1) `WithTop.ne_top_iff_exists` produces WithTop-coe, the
statements use `Nat.cast` — defeq but NOT syntactic; normalize the obtained equation with
`exact_mod_cast` into a `Nat.cast`-form `have` immediately. (2) `rw` direction on the
normalized equation. (3) `Nat.pos_iff` doesn't exist (use `.ne'` on the `<` directly /
`Nat.card_pos`). (4) keep `ramificationOrders` as a single ATOM in the `ℝ`-endgame — no
`field_simp`/`linarith` across the def; a `push_cast; rfl` step identifies
`↑(a·card) = ↑a · ramificationOrders` and `mul_right_cancel₀` finishes.

## Build + headline

`lake build` green, warning-free; preflight CLEAN. **HEADLINE: THE NUMERICAL LEMMA 5 —
`i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1` for every `σ̄ ≠ 1` — proved axiom-free, assembled
from nine named passes (P63–P71) with zero new mathematics in the assembly itself.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 73+): **the set-level Lemma 5** `(G/H)_{φ_{L/K'}(u)} = G_u H/H` — membership
form: `σ̄ ∈ (G/H)_v ↔ v < i(σ̄)` (P51's Lemma 1 at `B`) `↔ v < φ(j−1)+1` (P72) `↔
ψ(v)-side bound on j` (P44–48 `φ`/`ψ` monotonicity/inverse) `↔ ∃ lift s ∈ G_{⌈·⌉}` (P51 at
`𝒪_L` + the maximizer); design the indexing carefully (the project's filtration is
ℕ-indexed, Serre's statement is ℝ-indexed via P45's `⌈·⌉` conventions). Then Prop. 15 and
Prop. 14.

### Pass 73 (2026-07-03) — SERRE IV §3 LEMMA 5, proved (Herbrand's renumbering lemma)

**Mathematics; ledger delta 0 / 0 — a MILESTONE.** The set-level Lemma 5:
`(G_u).map (decompositionQuotient) = ramificationGroup K B ⌈φ_{L/K'}(u)⌉₊` for every
`u : ℕ` — Serre's `(G/H)_{φ_{L/K'}(u)} = G_u H/H`, the statement that makes the upper
numbering quotient-compatible. `Anabelian/Quotient/LemmaFive.lean`, 4 declarations,
standard-axioms-only.

## Design

ℕ-indexed with `⌈·⌉₊` on the `φ`-side (the P45 convention: Serre's real-indexed lower
numbering is `G_v = G_{⌈v⌉}`). Both memberships go through P51's Lemma 1:
- LHS: `σ̄ ∈ (G_u).map dq ↔ u < j(σ̄)` (`decompositionQuotient_mem_map_iff`) — `⟸` the
  maximizer `s₁ ∈ G_u`; `⟹` any lift's index is `≤ j` (`lowerIndex_le_of_profile`: every
  fiber element is `s₁·dr h` by P56's bijection, and the P72 profile caps it at `m`).
- RHS: `σ̄ ∈ B-filtration at ⌈φ(u)⌉ ↔ ⌈φ(u)⌉ < i_{K'/K}(σ̄) = a`, and the **ceiling
  bridge** `⌈φ(u)⌉ < a ↔ u < m` (`ceil_herbrandPhi_lt_iff`): `u ≤ m−1 ⟹ φ(u) ≤ φ(m−1) =
  a−1 ⟹ ⌈φ(u)⌉ ≤ a−1` (`Nat.ceil_le`); `u ≥ m ⟹ φ(u) ≥ φ(m) > φ(m−1) = a−1 ⟹ ⌈φ(u)⌉ > a−1`
  (`Nat.lt_ceil`) — P44's strict monotonicity; `m = 0` via `φ(−1) = −1` (both sides
  false/`a = 0`).
- Glue: P52's surjectivity produces the lift; `σ̄ = 1` is `Subgroup.one_mem` on both sides.

Probe: 3 mechanical rounds (`Subgroup.mem_map.mpr` for the set-coe membership; `hapos`
scoping for the final `omega`; `σ̄` with a combining macron is not a valid identifier —
use plain names in binders).

## Build + headline

`lake build` green (2.8 s); preflight CLEAN. **HEADLINE: SERRE IV §3 LEMMA 5 —
`(G/H)_{φ_{L/K'}(u)} = G_u H/H` — proved in Lean 4, axiom-free, for every finite tower over
a nonarchimedean local field. The renumbering that Herbrand's theorem is made of.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 74+): Prop. 15 (`φ`-transitivity — recommended first brick: the
index-multiplicativity `(G_0:G_u) = ((G/H)_0:(G/H)_{⌈φ(u)⌉})·(H_0:H_u)` from Lemma 5 + P46,
pure group theory) and Prop. 14 (**Herbrand's theorem** — Lemma 5 read through P45's upper
numbering, gated on the `ψ`-composition form of transitivity).

### Pass 74 (2026-07-03) — the card multiplicativity (Prop. 15's arithmetic heart)

**Mathematics; ledger delta 0 / 0.** `|G_u| = |(G/H)_{⌈φ_{L/K'}(u)⌉}| · |H_u|` for every
`u : ℕ` — the counting half of `φ`-transitivity, and at `u = 0` the inertia-level
`e_{L/K} = e_{K'/K} · e_{L/K'}`. `Anabelian/Quotient/CardMultiplicativity.lean`,
3 declarations, standard-axioms-only; probe compiled FIRST TRY.

## Method

One generic count + three identifications. `card_subgroup_eq_card_map_mul` (`|S| =
|S.map f| · |ker f ⊓ S|`): Lagrange on the restricted hom `f|_S` + first isomorphism
(`QuotientGroup.quotientKerEquivRange`), with `MonoidHom.restrict_range`/`ker_restrict` and
the `subgroupOf` card bookkeeping (`Subgroup.inf_subgroupOf_right` +
`subgroupOfEquivOfLe inf_le_right`). Then `dq|_{G_u}`: the image is Lemma 5 (P73), the
kernel is `ker dq = range dr` (P50) intersected down to `(H_u).map dr` (P46's
`ramificationGroup_map_eq`), and `dr`'s injectivity (P46) reads off the card. The `u = 0`
base needs only `⌈φ(0)⌉₊ = 0` (P44's `herbrandPhi_zero`).

## Why this is the heart of Prop. 15

P47: `φ_{L/K}'(u) = 1/(G_0 : G_u)` off breakpoints. The multiplicativity says exactly
`1/(G_0:G_u) = 1/((G/H)_0:(G/H)_{⌈φ(u)⌉}) · 1/(H_0:H_u)` — the chain-rule slope of
`φ_{K'/K} ∘ φ_{L/K'}`. What remains for Prop. 15 is the ANALYTIC GLUING: two continuous
piecewise-linear functions, equal at `0`, with matching (right-)slopes, agree. The
HANDOFF maps the candidate routes (right-derivative via `eq_of_has_deriv_right_eq`, or
ℕ-induction on P48's explicit formula) and flags the hard step: the no-interior-jump
alignment `(G/H)_{⌊φ(n)⌋+1} = (G/H)_{⌈φ(n+1)⌉}` — design on paper first.

## Build + headline

`lake build` green (2.5 s); preflight CLEAN. **HEADLINE: the index-multiplicativity
`(G_0:G_u) = ((G/H)_0:(G/H)_{⌈φ(u)⌉})·(H_0:H_u)` — Serre's Prop. 15 counting — proved in
card form, axiom-free; `e`-multiplicativity in towers falls out at `u = 0`.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 75): Prop. 15's analytic gluing — inventory P47–49's exact derivative statements,
design the breakpoint-alignment lemma on paper, scope one brick.

### Pass 75 (2026-07-03) — the alignment lemma (the quotient filtration jumps only at φ-images)

**Mathematics; ledger delta 0 / 0.** The step flagged at Pass 74 as "design on paper
first": the `B`-filtration is constant on integer indices in
`(φ_{L/K'}(n), ⌈φ_{L/K'}(n+1)⌉]` — hence the composite `φ_{K'/K} ∘ φ_{L/K'}` has constant
right-slope on each `[n, n+1)`. `Anabelian/Quotient/Alignment.lean`, 2 declarations,
standard-axioms-only.

## The design (P72's integrality is the whole game)

The worry was that this needed interval integrals or measure-zero arguments. It needs
neither: the jump values of the quotient filtration are `i_{K'/K}(σ̄) = a ∈ ℕ` with
`a − 1 = φ_{L/K'}(j(σ̄) − 1)` (P72 — note `φ(j−1)` is an INTEGER, being `a − 1`). If
`σ̄ ∈ (G/H)_w` for an integer `w > φ(n)`: `w < a` (P51's Lemma 1 + P72's `ha`), so
`w ≤ a − 1 = φ(j−1)`, so `φ(n) < φ(j−1)`, so `n < j−1` (P44 strict mono, contrapositive),
so `φ(j−1) ≥ φ(n+1)`, so `a ≥ φ(n+1)+1 > ⌈φ(n+1)⌉` (`Nat.ceil_lt_add_one`) — membership
persists to `⌈φ(n+1)⌉`. Antitonicity gives the reverse. The `m = 0` degenerate case is
vacuous (`a = 0` contradicts `w < a`). The real-`u` corollary is floor/ceil bookkeeping
(`Nat.lt_floor_add_one`, `Nat.le_ceil`, `Nat.floor_le`).

Two probe rounds (one `linarith` needed its hypotheses un-rewritten — keep `φ`-argument
forms syntactically stable; the `rw [hφ]; push_cast` detour created `↑k.succ − 1` vs `↑k`).

## Build + headline

`lake build` green (2.9 s); preflight CLEAN. **HEADLINE: the alignment lemma — the quotient
filtration jumps only at `φ_{L/K'}`-images of integers — proved axiom-free with no measure
theory; P72's integrality was the entire content. Prop. 15's remaining work is pure
calculus.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 76): the right-derivative bricks — `HasDerivWithinAt φ (|G_{⌊u⌋+1}|/|G_0|)
(Ici u) u` from P48's affine formula, the chain rule along the monotone inner `φ`, the
P74+P75 slope match, and `eq_of_has_deriv_right_eq` — the four-step plan is in HANDOFF.

### Pass 76 (2026-07-04) — PROP. 15: φ-transitivity, proved (the four-step plan, whole)

**Mathematics; ledger delta 0 / 0 — a MILESTONE.** Serre IV §3 Prop. 15:
`φ_{L/K}(u) = φ_{K'/K}(φ_{L/K'}(u))` for every real `u`.
`Anabelian/Herbrand/Transitivity.lean`, 3 declarations, standard-axioms-only.

## The proof (right-derivative gluing)

- `herbrandPhi_hasDerivWithinAt_Ici` (generic `(K, A)`): `φ` has right derivative
  `|G_{⌊u⌋+1}|/|G_0|` at every `u ≥ 0` — INCLUDING integer breakpoints, where P47's
  two-sided derivative fails. Build the affine model `c + (x−n)s` (`hasDerivAt_id`
  arithmetic), transfer by `congr_of_eventuallyEq`: `Iio (n+1) ∈ 𝓝[Ici u] u` (via
  `nhdsWithin_le_nhds`) + `self_mem_nhdsWithin` + `filter_upwards` puts the agreement set
  `[u, n+1)` in the filter; agreement is P48's affine formula.
- `slope_match`: the chain-rule product `(|(G/H)_{⌊φ(u)⌋+1}|/|(G/H)_0|)·(|H_{⌊u⌋+1}|/|H_0|)`
  equals `|G_{⌊u⌋+1}|/|G_0|`: P75's `ramificationGroup_comap_floor_add_one_eq` aligns the
  outer index to `⌈φ(⌊u⌋+1)⌉`, then P74 at `⌊u⌋+1` and at `0` + `field_simp` (which even
  closed the ring identity itself).
- `herbrandPhi_comp`: `u ≤ 0` by three `herbrandPhi_eq_id`s; `u > 0` by
  `eq_of_has_deriv_right_eq` on `[0, u]` with the common slope function
  `fun x => |G_{⌊x⌋+1}|/|G_0|`, continuity from P44 (`Continuous.comp` for the composite),
  `φ(0) = 0` three times at `0`.

## Probe experience

Two rounds. House notes: beta-redexes `(fun x => …) x` block `rw` — `change` to the
reduced form first (`show` trips the style linter); a `field_simp` can close goals `ring`
was queued for (drop the dead tactic, not the pipeline).

## The Prop. 15 arc in retrospect (P63–P76)

Prop. 3 (P50–63) → profile/count/φ-bridge (P65–67) → `e' = |H₀|` (P68–71) → numerical
Lemma 5 (P72) → set-level Lemma 5 (P73) → card multiplicativity (P74) → alignment (P75) →
transitivity (P76). Fourteen passes, zero axioms, and the two flagged "walls" (index
multiplicativity, breakpoint alignment) each fell to a design dividend (P23's
`Ideal.inertia`; P72's integrality).

## Build + headline

`lake build` green, warning-free; preflight CLEAN. **HEADLINE: SERRE IV §3 PROP. 15 —
`φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` on all of ℝ — PROVED in Lean 4, axiom-free. The road to
Herbrand's theorem (Prop. 14) is one pass wide: Lemma 5 + upper numbering + the
ψ-composition corollary.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 77): HERBRAND'S THEOREM — `(G/H)^v = G^v H/H`: read
`Herbrand/UpperNumbering.lean` first; bricks (a) `herbrandPsi_comp`, (b) the
Lipschitz-1/ceil-collapse lemma, (c) assembly — see HANDOFF.

### Pass 77 (2026-07-04) — HERBRAND'S THEOREM (the quotient arc closes)

**Mathematics; ledger delta 0 / 0 — THE MILESTONE OF THE ARC.** Serre IV §3 Prop. 14:
`(G^v).map (decompositionQuotient) = (G/H)^v` for every real `v` — **the upper numbering
is compatible with quotients**, the theorem the entire P50–77 arc was aimed at, and the
property that makes `G^v` glue across the infinite tower toward `Gal(K̄/K)`.
`Anabelian/Herbrand/HerbrandTheorem.lean`, 3 declarations, standard-axioms-only.

## The proof (three bricks, two probe rounds)

- `herbrandPhi_herbrandPsi_eq`: `φ_{L/K'}(ψ_{L/K}(v)) = ψ_{K'/K}(v)` — P76 at `ψ_{L/K}(v)`
  (whose LHS collapses by `herbrandPhi_psi`), then `congrArg ψ_{K'/K}` + `herbrandPsi_phi`.
- `ramificationGroup_comap_ceil_collapse`: `(G/H)_{⌈φ(⌈x⌉)⌉} = (G/H)_{⌈φ(x)⌉}`. THE key
  observation: this is FALSE as an integer identity (`⌈φ(⌈x⌉)⌉` can exceed `⌈φ(x)⌉`) but
  TRUE as a group equality — for non-integral `x > 0`, both indices lie in the alignment
  window `(φ(⌊x⌋), ⌈φ(⌊x⌋+1)⌉]` (lower end: `⌈φ(x)⌉ ≥ φ(x) > φ(⌊x⌋)` by strict
  monotonicity; upper end: ceil-monotone), so P75 collapses both to `⌈φ(⌊x⌋+1)⌉`. The
  HANDOFF's Lipschitz-1 sketch was never needed. `x ≤ 0` and `x ∈ ℕ` are trivial cases.
- `map_upperRamificationGroup_eq`: `unfold upperRamificationGroup`, P73 at
  `u = ⌈ψ_{L/K}(v)⌉`, `rw [← ψ-composition]`, `exact` the collapse.

## The quotient arc, in full (P50–77)

Prop. 2 restriction (P46) → quotient objects + Prop. 3 (P50–63) → profile/count/bridge
(P65–67) → `e' = |H₀|` (P68–71) → numerical Lemma 5 (P72) → set Lemma 5 (P73) → card
multiplicativity (P74) → alignment (P75) → Prop. 15 (P76) → **Herbrand (P77)**.
Twenty-eight passes, ZERO axioms end to end, every wall felled by an earlier design
dividend rather than a stub. This is the calibration standard for the next arc.

## Build + headline

`lake build` green (2.7 s); preflight CLEAN. **HEADLINE: HERBRAND'S THEOREM — the
compatibility of the upper ramification numbering with quotients, Serre IV §3 Prop. 14 —
PROVED in Lean 4, axiom-free, for every finite tower over a nonarchimedean local field.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 78): choose the next arc — consolidation (recommended first), then the L3
gateway design (upper numbering on `Gal(K̄/K)` via inverse limit), or Hasse–Arf. See
HANDOFF.

### Pass 78 (2026-07-04) — consolidation: the Herbrand package (`Herbrand/Main.lean`)

**Consolidation; ledger delta 0 / 0.** The quotient arc (P50–77) made citable: one file,
one audit block, one new corollary. `Anabelian/Herbrand/Main.lean`.

## Contents

- **The chain documented**: Prop. 2 (P46) → Prop. 3 (P63) → `e' = |H₀|` (P71) → numerical
  Lemma 5 (P72) → Lemma 5 (P73) → card multiplicativity / e-multiplicativity (P74) →
  Prop. 15 (P76) → Herbrand (P77), each with its named theorem, in the module docstring;
  `#print axioms` for all nine in one block (all `[propext, Classical.choice,
  Quot.sound]`).
- **`map_upperRamificationGroup_eq_extensionIntegers`** (the one new theorem): Herbrand on
  the canonical carrier. The arc's `B = (𝒪_L).comap (K' ↪ L)` and the canonical
  `𝒪_{K'} = extensionIntegers K K'` are EQUAL subrings (P57), but their decomposition
  subgroups are different TYPES — the clean statement compares `.subtype`-images in the
  common ambient `Gal(K'/K)`, where `Subgroup.map`-composition makes both sides live in
  `Subgroup (K' ≃ₐ[K] K')`. Proof: two rewrites (P77, then P57's equality — the rw motive
  across the dependent occurrences is fine because the goal type is non-dependent).
  Probe compiled FIRST TRY.

## Design note (for future carrier disputes)

When two propositionally-equal subobjects induce different subtype carriers, don't
transport along `▸` in statements — push both sides into the common ambient via
`.subtype`-maps and let `rw` on the subobject equality close it. Two lines, no `Eq.mpr`
residue.

## Build + headline

`lake build` green (2.4 s); preflight CLEAN. **HEADLINE: the Herbrand package — Serre IV
§1 + §3 for towers over a nonarchimedean local field, nine theorems from `H_u = H ∩ G_u`
to `(G^v).map = (G/H)^v` — consolidated, canonical-carrier form included, one audit block,
zero axioms.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 79): the L3 gateway DESIGN pass — upper numbering on `Gal(K̄/K)`: Mathlib
absolute-Galois inventory, the carrier decision (inverse limit vs preimage-intersection),
the functorial-P77 gap analysis, the local-field-inheritance check — see HANDOFF.

### Pass 79 (2026-07-04) — the L2-capstone design pass (G^v on Gal(K^sep/K))

**Design; ledger delta 0 / 0; no code.** Triggered in part by a user governance challenge:
"why does README say L2 is in progress if we're designing the L3 gateway?" — the answer
became the pass. The extension of the upper numbering to the absolute group is CHAPTER-IV
material (its raison d'être: Herbrand-compatibility is exactly what makes `G^v`
well-defined on the profinite limit) — **L2's capstone rung**, not L3. The "L3 gateway"
label named the consumer, not the stratum; retired across the governance files.

## The design (recorded in ROADMAP's status header)

1. **Carrier**: `Gal(K^sep/K)` on Mathlib's `separableClosure` (`separableClosure.isGalois`
   gives the InfiniteGalois stack). NOT `Field.absoluteGaloisGroup`: it is defined on
   `AlgebraicClosure K`, which in char `p` (the `𝔽_q((t))` local fields) is INSEPARABLE
   over `K` — the wrong automorphism group. Char-0 users lose nothing.
2. **Definition**: preimage-intersection `⨅_L proj_L⁻¹ (G^v(L/K))` over
   `FiniteGaloisIntermediateField K K^sep`, rather than an inverse limit of subgroups —
   cheapest formal move; the limit form is recovered by B5.
3. **Soundness check that de-risks the ladder**: re-reading P77's variable context, the
   entire finite-tower arc needs `IsNonarchimedeanLocalField` at the BASE only; towers
   `(K, ↥L₁, ↥L₂)` of intermediate fields never re-base. The P38–41 assembly theorem
   (a `theorem`, not an instance — `letI`-chain via `extensionValuativeRel`) is NOT on
   this path.
4. **The ladder**: B1 (full-group form: transport `G_u`/`G^v`/Herbrand from
   `D(𝒪_L) = ⊤` to `L ≃ₐ[K] L`, restate along `AlgEquiv.restrictNormalHom` — P50's `dq`
   is literally `restrictNormalHom` conjugated by subtype inclusions, and P78's
   common-ambient `.map subtype` idiom is the definition template); B2 (instance plumbing
   for `L₁ ≤ L₂` intermediate); B3 (the `⨅` definition + closedness via
   `restrictNormalHom_continuous` + `isOpen_iff_finite`); B4 (functorial P77 = B1 at
   `(K, ↥L₁, ↥L₂)` + `restrictNormalHom` composition coherence); B5 (projection
   surjectivity `proj_L (G^v) = G^v(L/K)` — compactness/compatible-system, the theorem
   that makes the definition right; 1–2 passes); B6+ (jumps, Hasse–Arf, abelian
   filtration → L3). New folder `Anabelian/Absolute/` for the stratum.

## Governance

Stratum language reconciled across ROADMAP/README/HANDOFF (current-state text only;
historical entries untouched, per the immutability rule). **HEADLINE: the map from
Herbrand's theorem to `G^v(K^sep/K)` is five bricks, none a wall, with the one real
theorem (B5) clearly identified — and it is all still L2.**

## Ledger delta + rule-2

**0 / 0.** No declarations added; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 80): brick B1 — the full-group form of the arc.

### Pass 80 (2026-07-04) — B1: the full-group form (the capstone ladder opens)

**Mathematics; ledger delta 0 / 0.** The finite arc translated to the language the
profinite stack speaks: filtrations on the full `L ≃ₐ[K] L`, transitions along
`AlgEquiv.restrictNormalHom`. New folder `Anabelian/Absolute/` (the capstone stratum's
home); `FullGroup.lean`, 5 declarations, standard-axioms-only.

## Method

- `fullRamificationGroup K L u` / `fullUpperRamificationGroup K L v` :=
  `.map D.subtype` of the decomposition-level objects — P78's common-ambient idiom
  promoted to THE definition (decision recorded at P79; `D = ⊤` under normality by P52).
- `subtype_comp_decompositionQuotient`: the square `subtype ∘ dq = restrictNormalHom ∘
  subtype` is `MonoidHom.ext fun _ => rfl` — P50's def was literally built from
  `restrictNormalHom`; this is the receipt.
- The transports: `map_fullRamificationGroup_eq` (Lemma 5) and
  `map_fullUpperRamificationGroup_eq` (**Herbrand**) — each a single `rw` chain:
  `Subgroup.map_map`, `← square`, `← map_map`, finite-arc theorem (P73/P77), P57's
  `extensionIntegers_comap_eq`. Three probe rounds, all instance-context plumbing
  (`extensionIntegers` needs the full local-field context at `K`; unused-variable lint).

## Build + headline

`lake build` green (2.6 s); preflight CLEAN. **HEADLINE: Herbrand's theorem in full-group
form — `(G^v(L/K)).map (restrictNormalHom K') = G^v(K'/K)` — the transition maps of the
profinite Galois system carry the upper filtration to the upper filtration exactly. The
absolute `G^v` is now a definition away (B3) plus one real theorem (B5).**

## Ledger delta + rule-2

**0 / 0.** Definitions are images under a fixed hom — no new constraint content, no rule-2
obligation beyond P23's; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 81): B2 — intermediate-field plumbing (`FiniteGaloisIntermediateField K K^sep`
carriers; MATCH `Galois/Profinite.lean`'s conventions for the transition maps so B4
composes with Mathlib's functor on the nose — see HANDOFF).

### Pass 81 (2026-07-04) — B2 + B4's heart: the profinite tower plumbing

**Mathematics; ledger delta 0 / 0.** The `≤`-pair plumbing for
`FiniteGaloisIntermediateField`, in EXACTLY Mathlib's `finGaloisGroupMap` conventions, and
— ahead of the B-ladder schedule — **Herbrand along the profinite transitions**.
`Anabelian/Absolute/Tower.lean`, 5 declarations, standard-axioms-only.

## Method

- Read `Galois/Profinite.lean` first (per the P80 handoff): `finGaloisGroupMap` uses
  `RingHom.toAlgebra (Subsemiring.inclusion le)` + `IsScalarTower.of_algebraMap_eq'` +
  `AlgEquiv.restrictNormalHom` — the SAME `restrictNormalHom` as B1. `leAlgebra` copies
  the convention verbatim (as an `abbrev` — the class-type-def linter's requirement), so
  every later composition with `finGaloisGroupFunctor` is definitional.
- `leAlgebra_finiteDimensional`: from `FiniteDimensional K ↥L₂` (the FGIF structure), NOT
  the ambient (`K^sep` is infinite — the first probe error was exactly that wrong
  hypothesis). `leAlgebra_isGalois`: `tower_top`. Separability of intermediate fields:
  already an instance (probe-verified, no declaration).
- **`map_fullUpperRamificationGroup_le`**: statement carries the pair package by anonymous
  statement-level `letI/haveI` (house-legal); proof is `letI`/`haveI` the four pieces and
  `exact` B1's transport at `(K, ↥L₁, ↥L₂)`. Notably GENERAL: any separable ambient `E`,
  not just `K^sep`.

## Build + headline

`lake build` green (3.2 s); preflight CLEAN. **HEADLINE: Herbrand's theorem along the
transition maps of Mathlib's profinite Galois system — `(G^v(L₂/K)).map (restrictNormalHom
↥L₁) = G^v(L₁/K)` for any nested pair of finite Galois subextensions — proved axiom-free.
B3's `⨅`-definition of `G^v(K^sep/K)` now has its compatible system.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class` (an `abbrev` of a Mathlib construction); no owed
witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 82): B3 — `absoluteUpperRamificationGroup K v := ⨅_L (G^v(L/K)).comap
(restrictNormalHom ↥L)` on `Gal(K^sep/K)`, `mem_iff`, and closedness; B5's candidate tool
flagged: `nonempty_sections_of_finite_inverse_system` — see HANDOFF.

### Pass 82 (2026-07-04) — B3: the absolute `G^v` defined (the capstone's object exists)

**Mathematics; ledger delta 0 / 0.** The upper ramification filtration on the Galois group
of an arbitrary (possibly infinite) extension of a nonarchimedean local field — at
`E = K^sep`, the absolute `G^v` whose group-theoretic recoverability is the entry point of
the anabelian program. `Anabelian/Absolute/UpperNumbering.lean`, 4 declarations,
standard-axioms-only.

## Method

- The def needs LESS context than planned: no separability, no `[IsGalois K E]` — just
  the local base and `[Algebra K E]` (the `⨅` ranges over FGIF, each level supplying its
  own instances). The hypotheses will enter at B5 where the mathematics does.
- `mem_iff`: one `simp` (`mem_iInf` + `mem_comap`). Closedness: `coe_iInf` + `coe_comap`
  under the intersection (the one probe fix), then `isClosed_discrete.preimage
  (InfiniteGalois.restrictNormalHom_continuous …)` per factor + `isClosed_iInter` — the
  target levels are finite hence discrete (`KrullTopology` instance). Easy half of B5:
  `map_le_iff_le_comap.mpr (iInf_le _ L)` — one line.
- Convention note: the comap is along `AlgEquiv.restrictNormalHom (F := K) (K₁ := E)
  L.toIntermediateField` — the exact form of `InfiniteGalois.restrictNormalHom_continuous`
  and `finGaloisGroupMap`, so B5 composes with Mathlib's machinery without adapters.

## Build + headline

`lake build` green (2.7 s); preflight CLEAN. **HEADLINE: `G^v` on the absolute Galois
group of a nonarchimedean local field — Serre IV's punchline object — is DEFINED,
axiom-free: closed in the Krull topology, compatible-from-above with every finite level.
One theorem (B5: projection surjectivity) stands between the definition and its
inverse-limit meaning.**

## Ledger delta + rule-2

**0 / 0.** A `def` + formal properties; no new `structure`/`class`; no owed witness;
D1/D2 N/A. R1–R3 untouched.
Next (Pass 83): B5 — projection surjectivity: Route A (compactness on directed closed
fibers; `CompactSpace Gal(E/k)` from InfiniteGalois; FGIF sups for directedness; P81 both
UP the tower for fiber-nonemptiness and DOWN for full-intersection membership) or Route B
(`nonempty_sections_of_finite_inverse_system`) — see HANDOFF for the sub-brick split.

### Pass 83 (2026-07-04) — B5: projection surjectivity (the capstone closes; L2 DONE)

**Mathematics; ledger delta 0 / 0 — THE STRATUM MILESTONE.** The absolute upper
ramification filtration `G^v(E/K)` projects onto `G^v(L/K)` at every finite level — the
`⨅`-definition is a genuine inverse limit, and with it the **L2 stratum (Serre ch. IV) is
DONE**, axiom-free end to end. `Anabelian/Absolute/Surjectivity.lean`, 3 declarations;
the capstone theorem's probe compiled FIRST TRY.

## The proof (Route A of the P82 handoff, exactly as designed)

Fibers `F_M := restrict_M⁻¹(G^v(M/K)) ∩ restrict_L⁻¹{τ}`:
- **Closed**: preimages of finite discrete levels (P82 idiom).
- **Nonempty**: lift `τ` into `G^v((L ⊔ M)/K)` by P81's Herbrand-along-transitions
  (up the tower `L ≤ L ⊔ M`), then to `Gal(E/K)` by `restrictNormalHom_surjective`; the
  composition coherence `restrictNormalHom_comp_of_le` (Mathlib's
  `restrictNormalHom_comp_apply` under the P81 pair package + the `rfl`-cheap `M ⊆ N ⊆ E`
  tower) reads both constraints off the lift.
- **Directed**: FGIF sups + the downward step `mem_fullUpper_of_le` (coherence + P81 as
  `⊆`).
- **Compact glue**: `CompactSpace Gal(E/K)` (InfiniteGalois) +
  `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`; `Nonempty` index
  from FGIF's `⊥`.
Any point of the intersection is the lift. Herbrand's theorem enters exactly where Serre
uses it: the compatible-system property of the finite levels.

## L2, closed (a stratum retrospective)

P22 (architecture) → P23–28 (finite-level theory) → P29–43 (descent + assembly +
canonicity) → P44–49 (φ/ψ/upper numbering) → P50–78 (the quotient arc: Prop. 2 → Prop. 3
→ Lemma 5 → Prop. 15 → HERBRAND + consolidation) → P79–83 (the capstone: design,
full-group form, plumbing, the absolute G^v, surjectivity). Sixty-two passes, ZERO axioms.
ROADMAP's L2 section header now reads DONE (Pass 83); Hasse–Arf is its own rung;
norm-compatibility belongs to L3.

## Build + headline

`lake build` green, warning-free (one `omit` header for the coherence lemma's unused
local-field variables — `omit` goes BEFORE the docstring); preflight CLEAN. **HEADLINE:
the upper ramification filtration of the absolute Galois group of a nonarchimedean local
field — closed in the Krull topology, the inverse limit of the finite levels — is
constructed and verified in Lean 4, axiom-free. L2 is done.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 84): choose the arc — (A) Absolute consolidation (+ `G^0` vs the L1-era
absolute inertia!), (B) Hasse–Arf (5–10 passes), (C) the L3 opening inventory. See
HANDOFF.

### Pass 84 (2026-07-04) — the Absolute consolidation + the separation theorem

**Consolidation + mathematics; ledger delta 0 / 0.** `Anabelian/Absolute/Main.lean`: the
B1–B5 chain documented, ONE audit block for the whole stratum (12 declarations), and four
structural dividends topped by **the separation theorem**.

## The separation theorem (the pass's real content)

`iInf_absoluteUpperRamificationGroup_eq_bot : ⨅ v : ℝ, G^v(E/K) = ⊥` for Galois `E/K`:
if `σ` lies in every `G^v`, then for every `x : E` the finite Galois subextension
`L := FiniteGaloisIntermediateField.adjoin K {x}` receives a restriction of `σ` lying in
every `G^v(L/K)`; P45's `upperRamificationGroup_eventually_bot` (fed by P29's
`isNoetherianRing_extensionIntegers` + `Ideal.iInf_pow_eq_bot_of_isLocalRing`) makes that
filtration eventually `⊥`, so the restriction is `1`, and `AlgEquiv.restrictNormal_commutes`
reads `σ x = x` off it. `ext` closes. With P82's closedness and P83's inverse-limit
property: the filtration of `Gal(K^sep/K)` is **defined, closed, an inverse limit,
antitone, normalized, separating** — chapter IV complete, wall to wall.

## Consolidation notes

- Antitone/nonpos at both levels are one-liners over P45 (`Subgroup.map_mono`/
  `comap_mono` + `iInf_mono`/`iInf_congr`; the `v ≤ 0` case is `herbrandPsi_eq_id` +
  `Nat.ceil_eq_zero` + `Nat.ceil_zero` — the last rewrite is the usual `⌈(0:ℝ)⌉₊` guard).
- The `G^0`-vs-L1-inertia identification (P20's reduction surjection) was scoped OUT: it
  needs the finite-level `G_0 = ker(residue action)` bridge at the absolute level — a real
  brick, deferred (noted here, not an owed witness: no claim made).
- Two probe rounds (the `⌈0⌉₊` guard; `h2.symm`).

## Build + headline

`lake build` green; preflight CLEAN. **HEADLINE: the upper ramification filtration of
`Gal(K^sep/K)` is a separating, closed, antitone inverse-limit filtration — the complete
Serre-IV package, consolidated in one audited file, 0 axioms across 84 passes.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 85): the L3 opening inventory (design pass — local CFT in Mathlib: cohomology
vs Lubin–Tate route decision; the ramification correspondence as the R1-relevant target;
`G^v(K^ab/K)` already live via P82's generality). See HANDOFF.

### Pass 85 (2026-07-04) — the L3 opening inventory (design pass)

**Design; ledger delta 0 / 0; no code.** Local class field theory scoped: the Mathlib
landscape surveyed, the route chosen, ROADMAP's L3 stub replaced by a five-stage ladder.

## Findings (Mathlib pin, July 2026)

Group cohomology is genuinely usable: `Homological/GroupCohomology/` has the standard
resolution (`Basic`), explicit low-degree `H⁰/H¹/H²` with cocycle APIs (`LowDegree`), the
long exact sequence, functoriality, Shapiro, **Hilbert 90** (multiplicative cocycle form +
the cyclic norm-one corollary), and **`FiniteCyclic`** — the even/odd periodicity isos
that ARE the Herbrand-quotient substrate. Group homology exists in parallel; continuous
(profinite) cohomology is one file old. Brauer group: CSA `Defs` only. Formal groups:
1-dim laws + `𝔾ₐ/𝔾ₘ` + base change, nothing more. No Tate cohomology, no
inflation–restriction, no cup products, no `Br ≃ H²`, no class formations, no Lubin–Tate,
no `K^ab`, no CFT. External Lean CFT developments exist but are not in this pin.

## The route decision (recorded in ROADMAP, revisit at the L3.3 gate)

**Neukirch-style abstract CFT.** Reasons: (i) its inputs are cyclic-level cohomology —
Herbrand quotients and Hilbert 90 — which Mathlib largely HAS, versus Tate's theorem
(needs `Ĥ` + cup products, both absent: a Mathlib-scale sub-project) or Lubin–Tate (needs
formal-group arithmetic from a one-file base); (ii) the project's own strengths (P24–27
residue characters, P38–43 completeness, P44–49+P72 Herbrand machinery) feed exactly the
L3.1/L3.2 verification of the class-formation axioms; (iii) the fallback (porting the
external LCFT development as an honestly-labeled `FOUNDATIONAL` boundary) stays available
at the gate without poisoning the ladder below it.

## The ladder (statuses live in ROADMAP)

L3.0 `K^ab` interface → L3.1 cyclic layer → L3.2 unramified cohomology → **L3.3
reciprocity (THE WALL)** → L3.4 the ramification correspondence `θ(U^n) = G^n(K^ab/K)` —
the R1-relevant piece, and the reason L2's `G^v(K^ab/K)` interface (P82's generality) was
built the way it was.

## Ledger delta + rule-2

**0 / 0.** No declarations; no stub; the wall named and gated, not crossed on paper.
R1–R3 untouched. Next (Pass 86): L3.0 — the `K^ab` object (fixed field of the closed
commutator subgroup via the infinite Galois correspondence), its `IsGalois`/abelian
structure, and the `G^v(K^ab/K)` sanity instantiation. See HANDOFF.

### Pass 86 (2026-07-04) — L3.0: K^ab (the stage of local class field theory)

**Mathematics; ledger delta 0 / 0.** The maximal abelian extension as an object, with its
structure theory — the L3 ladder's first rung, and the L3 stratum's first file
(`Anabelian/ClassField/MaximalAbelian.lean`, 7 declarations, standard-axioms-only).

## Method

- `commutatorClosure := (commutator Gal(E/K)).topologicalClosure` (normal: closure of
  normal; closed: closure). `maximalAbelianSubextension := fixedField commutatorClosure`.
- `IsGalois K K^ab`: `normal_iff_isGalois` needs the fixing subgroup normal;
  `fixingSubgroup_fixedField` (the ClosedSubgroup form) collapses it to the closure ✓.
- `maximalAbelianGalEquiv : Gal(E/K) ⧸ closure ≃* Gal(K^ab/K)`: Mathlib's
  `normalAutEquivQuotient`. Commutativity: quotient kills commutators
  (`QuotientGroup.eq` + `group`-normalization to a commutator element + membership).
- **Maximality** (`le_maximalAbelianSubextension`): for abelian normal `L`, every
  `restrictNormalHom L ⁅g₁,g₂⁆ = 1` (`map_commutatorElement` +
  `commutatorElement_eq_one_iff_mul_comm`), so `commutator ≤ ker = fixingSubgroup`
  (`restrictNormalHom_ker`), so the CLOSURE lands there (`topologicalClosure_minimal` +
  `InfiniteGalois.fixingSubgroup_isClosed`), and `IntermediateField.le_iff_le` flips.
- House notes: the element bracket `⁅g,h⁆` is a SCOPED instance — `open scoped
  commutatorElement`; `InfiniteGalois.fixingSubgroup_isClosed` is hypothesis-free while
  the `IntermediateField.`-namespaced one wants `FiniteDimensional`; `commutator G` needs
  a `change ⁅⊤,⊤⁆ ≤ _` before `Subgroup.commutator_le` fires.

## Build + headline

`lake build` green (3.1 s); preflight CLEAN. **HEADLINE: `K^ab` exists — Galois over `K`,
its group THE topological abelianization (proved abelian), its maximality a theorem, and
`G^v(K^ab/K)` already live through the L2 interface. Both sides of the ramification
correspondence (L3.4) now exist as objects; the map between them is the wall (L3.3).**

## Ledger delta + rule-2

**0 / 0.** The claiming name carries its justification theorem (maximality proved, not
stipulated); no new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 87): L3.1 — the cyclic/Herbrand-quotient layer: inventory Mathlib's
`FiniteCyclic`/`Rep` framework, then ONE brick (the Herbrand quotient def + finite-module
triviality, or the `Rep`-bridge for `Lˣ`). See HANDOFF.

### Pass 87 (2026-07-04) — L3.1 opens: the Herbrand quotient

**Mathematics; ledger delta 0 / 0.** The abstract two-endomorphism Herbrand quotient +
the finite-module triviality theorem — the cyclic layer's central device, absent from
Mathlib (verified). `Anabelian/ClassField/HerbrandQuotient.lean`, 6 declarations.

## Design

- **Two-endo form over `Rep`-category form**: `f g : M →* M` on a `CommGroup` with
  `f∘g = g∘f = 1` (Serre's `q_{f,g}`), multiplicative carrier (the consumers are `Lˣ`,
  `U^i`). No category theory; the bridge to Mathlib's
  `Rep.FiniteCyclicGroup.groupCohomologyIsoEven/Odd` (where `herbrandH (N) (σ/1) = Ĥ⁰ =
  H²`, swapped `= Ĥ¹ = H¹`) is deferred to the Hilbert-90-packaging brick.
- `herbrandQuotient : ℚ` with the `Nat.card = 0` convention on infinite carriers —
  harmless, theorems carry their own finiteness.
- **Triviality** (`q = 1` for finite `M`): the P74 idiom re-run — Lagrange
  (`card_eq_card_quotient_mul_card_subgroup`), first isomorphism
  (`quotientKerEquivRange`), `subgroupOfEquivOfLe` for `|im g|-inside-|ker f|`; the
  four-rewrite chain `← h1, ← h3, ← h2, ← h4` collapses both sides of the triple product
  to `|M|`; `ring_nf`-then-`exact` matches ℕ-product orders; `Nat.eq_of_mul_eq_mul_right`
  cancels.

## Build + headline

`lake build` green (2.9 s); preflight CLEAN. **HEADLINE: the Herbrand quotient — the
device that runs the cyclic layer of class field theory — defined with its triviality
theorem, axiom-free; the `q`-calculus (SES multiplicativity) is next.**

## Ledger delta + rule-2

**0 / 0.** Plain defs + theorems; pair hypotheses used visibly; no witness owed; D1/D2
N/A. R1–R3 untouched. Next (Pass 88): `q`-multiplicativity — recommended first sub-brick:
the 6-cycle alternating-card lemma (`|A₀||A₂||A₄| = |A₁||A₃||A₅|` for a periodic exact
sequence of finite groups), pure group theory, reusable. See HANDOFF.

### Pass 88 (2026-07-04) — the exact-cycle count + herbrandH functoriality

**Mathematics; ledger delta 0 / 0.** The counting engine of the Herbrand quotient's
SES-multiplicativity, plus the functorial arrows.
`Anabelian/ClassField/ExactCycle.lean`, 4 declarations.

## Method + lessons

- **`card_prod_eq_of_exact_cycle`**: first attempt indexed by `ZMod 6` — DEPENDENT-TYPE
  TRAP: `A (i−1+1)` and `A i` are only propositionally equal, so subgroup ascriptions
  across the index don't typecheck; six explicit groups with six homs and six exactness
  hypotheses is friction-free AND matches the eventual use site (the six-term Herbrand
  cycle is six named groups anyway). Proof: `|Aᵢ| = |ker dᵢ|·|im dᵢ|` (cross-hom first-iso
  count) + exactness (`ker dᵢ = im dᵢ₋₁`) ⟹ both triple products = ∏ all six `|im dᵢ|`;
  `ring`. The `Finite` hypotheses turned out UNUSED (linter caught it): with
  `Nat.card = 0` conventions the identity holds unconditionally — a stronger lemma than
  planned.
- **`herbrandHMap`**: `kerRestrict` (intertwining ⟹ kernels map to kernels) +
  `QuotientGroup.map` with the `subgroupOf` comap condition (P74's `mem_subgroupOf`
  idiom). `MonoidHom.mem_ker` is now argument-free (house catalogue).

## Build + headline

`lake build` green (2.6 s); preflight CLEAN. **HEADLINE: the alternating-card identity
for periodic exact cycles — the arithmetic heart of `q(M) = q(M')·q(M'')` — proved with
no finiteness at all; the six-term cycle's four functorial arrows exist. The two snake
maps are the remaining hard brick.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 89): the connecting maps δ (the snake — budget the whole pass for the two δs
if needed), then exactness + assembly. See HANDOFF.

### Pass 89 (2026-07-04) — the snake (the connecting homomorphism)

**Mathematics; ledger delta 0 / 0.** The hard brick, landed in one pass:
`snakeDelta : Ĥ⁰(M'') →* Ĥ¹(M')` for a pair-equivariant SES of commutative groups, with
its characterizing property. `Anabelian/ClassField/Snake.lean`, 7 declarations.

## The design (why this snake has no cocycle bookkeeping)

1. **The pullback is a homomorphism.** On `T = π⁻¹(ker f'') ≤ M`, the assignment
   `Y : x ↦ (unique y' with ι y' = f x)` is well-defined (exactness puts `f x` in
   `range ι`) and MULTIPLICATIVE — `ι`-injectivity transfers `f(xy) = f(x)f(y)` across.
   `snakeY : T →* ker g'` is a genuine hom; all choice happens inside `Exists.choose`
   with the spec lemma `ι_snakePull` as the only interface.
2. **One kernel condition.** Classically δ needs (a) lift-independence and (b)
   `im g''`-invariance; both ARE the containment `ker Φ ≤ ker ψ` where `Φ : T → Ĥ⁰(M'')`
   is project-and-quotient and `ψ = mk ∘ Y`. Proof: `π x = g'' w''` ⟹ pick a lift `w`,
   then `x·(g w)⁻¹ ∈ ker π = range ι` gives `x = (g w)·ι z'`, and
   `ι(Y x) = f(g w)·f(ι z') = ι(f' z')` (`f∘g = 1` on `M`), so `Y x ∈ im f'`.
3. `δ := (QuotientGroup.lift ker Φ ψ hker) ∘ (quotientKerEquivOfSurjective Φ hΦ).symm`;
   the computation rule `δ(Φ x) = ψ x` comes out by `MulEquiv.symm_apply_eq` + `rfl`.

## House notes (catalogued)

Coercions into quotient types must name the UNFOLDED `_ ⧸ _` type — a def-wrapper
(`herbrandH`) blocks coe elaboration; `have h' : (unfolded type) = 1 := hx` defeq-casts
cleanly. `group` does not use commutativity (`g w * x * (g w)⁻¹ = x` needs `mul_comm` +
`mul_inv_cancel_left` by hand). For hypothesis-heavy defs, pass everything positionally.

## Build + headline

`lake build` green (2.0 s); preflight CLEAN. **HEADLINE: the connecting homomorphism of
the Herbrand six-term cycle — built with zero cocycle bookkeeping via the
pullback-is-a-hom observation, axiom-free. Exactness (six nodes) and the assembly are all
that remain for `q(M) = q(M')·q(M'')`.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 90): the six exactness proofs + assembly. See HANDOFF.

### Pass 90 (2026-07-04) — the multiplicativity theorem (the q-calculus is operational)

**Mathematics; ledger delta 0 / 0.** The six-term Herbrand cycle is exact and
`q(M) = q(M')·q(M'')` follows — with P87's triviality, both moves of the classical
Herbrand-quotient calculus are now theorems.
`Anabelian/ClassField/Multiplicativity.lean`, 8 declarations.

## Method

- **Three proofs, six exactness facts**: the cycle's nodes pair up under the `(f,g)`-swap;
  `snake_exact_mid` (at `Ĥ⁰(M)`), `snake_exact_top` (at `Ĥ⁰(M'')`), `snake_exact_bot`
  (at `Ĥ¹(M')`) instantiate at swapped pairs for the other three. Each chase runs on
  P89's `snakeDelta_apply` + the lift trick (`mk x'' = Φ⟨x, hT⟩` for a chosen preimage).
- **Assembly**: P88's `card_prod_eq_of_exact_cycle` at the six carriers; division
  bookkeeping via `div_eq_div_iff` + a `ring_nf`-matched ℕ-identity. Only `Ĥ¹`-finiteness
  (×3) is hypothesized: infinite `Ĥ⁰`s zero both sides.

## House notes (the mk/coe friction, SOLVED as method)

Prove rfl computation lemmas FIRST (`herbrandHMap_mk`, `snakePhi_mk`, `snakePsi_mk`) and
never unfold defs mid-chase; term-mode `(QuotientGroup.eq_one_iff _).mp` beats `rw` on
mixed mk/coe goals; the defeq-cast `have h' : g'' w'' = π x.1 := hw''` converts
subtype-value equalities silently; quotient `1` is defeq `mk 1`, so `rfl` closes goals
where `mk_one` gets stuck against def-wrappers. Three probe rounds total for six chases +
assembly — the P89 catalogue paid for itself immediately.

## Build + headline

`lake build` green (2.9 s); preflight CLEAN. **HEADLINE: the Herbrand-quotient calculus —
triviality on finite modules (P87) + multiplicativity in short exact sequences (P90) — is
fully operational, axiom-free. The road to `q(Lˣ) = [L:K]` and the class-formation axioms
is open.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 91): the Galois-module pair (norm, σ/1) for a finite cyclic action ⟹
`q(G, A)` instantiated; then `q(ℤ) = |G|`, then the `q(Lˣ)` track. See HANDOFF.

### Pass 91 (2026-07-04) — the cyclic pair (q now speaks Galois modules)

**Mathematics; ledger delta 0 / 0.** `cyclicNorm`/`cyclicDiff` with the complex
conditions, and `cyclicHerbrandQuotient σ n` — the convention-pinning instantiation.
`Anabelian/ClassField/CyclicPair.lean`, 6 declarations + a sanity example.

## Method + convention

- Both maps built directly as `MonoidHom` structures (no hom-monoid instances):
  `cyclicNorm` multiplicative by `Finset.prod_mul_distrib`; `cyclicDiff` by the
  `mul_comm/mul_assoc/mul_left_comm` simp set (`group` cannot use commutativity — house
  catalogue).
- The index-shift lemma (`σ(N x) = N x`): `map_prod` + `pow_succ'` (MIND THE ORDER:
  `(σ * σ^i) x = σ(σⁱ x)` needs σ on the LEFT — `pow_succ` gives the wrong side) +
  `prod_range_succ'`/`prod_range_succ` + `σ^n = σ^0` + `mul_right_cancel`. Telescoping
  for `N∘D = 1` is the same shift at `σ x` (there `pow_succ` IS the right one).
- **THE CONVENTION** (pinned once): `cyclicHerbrandQuotient σ n := herbrandQuotient
  (cyclicDiff σ) (cyclicNorm σ n)` — diff FIRST, so `Ĥ⁰ = ker D/im N = A^σ/N(A)` and
  `q = |Ĥ⁰|/|Ĥ¹|` matches Serre VIII §4. Every downstream computation reads this file's
  header.

## Build + headline

`lake build` green (2.7 s); preflight CLEAN. **HEADLINE: the Herbrand quotient of a
cyclic Galois action — norm, twisted difference, complex conditions, `q(σ,A)` — is
defined and armed with the P87/P90 calculus, axiom-free. `q(ℤ) = n` and the
`q(Lˣ) = [L:K]` track are next.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; hypotheses used visibly; no witness owed; D1/D2
N/A. R1–R3 untouched. Next (Pass 92): `q(ℤ) = n` — the `Multiplicative ℤ` computation
(card plumbing inventoried in HANDOFF). See HANDOFF.

### Pass 92 (2026-07-04) — q(ℤ) = n (the fundamental computation)

**Mathematics; ledger delta 0 / 0.** The first nontrivial Herbrand-quotient value:
`cyclicHerbrandQuotient (1) n = n` on `Multiplicative ℤ`.
`Anabelian/ClassField/TrivialAction.lean`, 8 declarations.

## Method

- Generic layer (any `CommGroup A`): the trivial action degenerates the pair
  (`N = (·)ⁿ` by `prod_const`+`card_range`; `D = 1`), so `Ĥ⁰ = A/Aⁿ` — computed by the
  presentation `diffKerProj : A ↠ Ĥ⁰` (inclusion into the FULL `ker D` + projection;
  `ker θ = range N` by the eq_one_iff/mem_subgroupOf term-mode idiom) + first
  isomorphism: `|Ĥ⁰| = (range N).index`. `Ĥ¹ = 0` from `n`-torsion-freeness
  (Subsingleton transport through the kernel).
- ℤ-instantiation: `range ((·)ⁿ) = toSubgroup (zmultiples n)` — the bridge lemmas
  `Multiplicative.mem_toSubgroup` (a `rfl`!) and `Int.mem_zmultiples_iff` (DVD form —
  cleaner than the `∃ k • n` shape); then `AddSubgroup.index_toSubgroup` +
  `Int.index_zmultiples` + `natAbs_natCast` land `|Ĥ⁰| = n`. Torsion-freeness via
  `toAdd` + `mul_eq_zero`.
- Three probe rounds (Subtype.ext-elaboration in the surjectivity; the eq_one_iff mk/coe
  pattern — solved term-mode per the P90 catalogue; an over-eager push_cast).

## Build + headline

`lake build` green (2.7 s); preflight CLEAN. **HEADLINE: `q(ℤ) = n` — the computation
every `q(Lˣ) = [L:K]` proof reduces to — done axiom-free, with the generic
`|Ĥ⁰| = [A : Aⁿ]` machinery reusable for the unit-filtration track.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no witness owed; D1/D2 N/A. R1–R3 untouched.
Next (Pass 93): the `q(Lˣ)` track opens — the valuation SES as a pair-equivariant
sequence (Galois-invariance of the valuation from the P43-era canonicity; trivial action
downstairs = P92's case), so P90 fires: `q(Lˣ) = q(𝒪ˣ)·n`. See HANDOFF.

### Pass 93 (2026-07-04) — the valuation exact sequence (the q(Lˣ) track opens)

**Mathematics; ledger delta 0 / 0.** `1 → Rˣ → Kˣ →v Multiplicative ℤ → 1` for any DVR
fraction field — the units-valuation hom with surjectivity and kernel, fully abstract
(nothing tower-specific). `Anabelian/ClassField/UnitsValuation.lean`, 5 declarations.

## Method

- **Design**: rather than build a ℤ-valuation by hand, bundle Mathlib's machinery: the
  DVR's maximal ideal is a height-one prime (`dvrHeightOneSpectrum`), its adic
  `Valuation K ℤᵐ⁰` restricts to units, and `WithZero.unitsWithZeroEquiv` reads off
  `Multiplicative ℤ`. The `eq_iff` interface (via `coe_unitsWithZeroEquiv_eq_units_val`)
  makes every later computation a `ℤᵐ⁰`-level rewrite.
- **Kernel** (the real work): `x = alg a / alg b` (`IsFractionRing.div_surjective` —
  orientation `… = z`!), DVR-factorize both; the multiplicative structure forces equal
  `ϖ`-exponents once `intValuation ϖ = exp(−1)` is known for the GIVEN irreducible —
  proved en route: `γ = ↑g` nonzero, `γ < 1` (`ϖ ∈ 𝔪`), and `γ^k = exp(−1)` against
  Mathlib's `∃`-uniformizer give `k·toAdd g = −1` with `toAdd g < 0`, so `toAdd g = −1`
  by the ℤ-divisor argument. Units assemble by `field_simp`.
- House notes: `ℤᵐ⁰` is scoped notation — spell `WithZero (Multiplicative ℤ)`;
  `WithZero.exp z` is `↑(ofAdd z)` by `rfl`; `Multiplicative ℤ`'s order is
  definitionally ℤ's (a `g < 1` hypothesis IS `toAdd g < 0`).

## Build + headline

`lake build` green (3.7 s); preflight CLEAN. **HEADLINE: the valuation exact sequence of
a DVR fraction field — hom, surjectivity, kernel — complete and abstract, axiom-free.
Pair-equivariance and the P90 firing (`q(Kˣ) = q(Rˣ)·n`) are next.**

## Ledger delta + rule-2

**0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A. R1–R3 untouched.
Next (Pass 94): σ-invariance of the valuation (via the en-route irreducible-valuation
fact — σϖ is again irreducible!), the equivariant package, the P90 firing. See HANDOFF.


### Pass 94 (2026-09-25) — valuation equivariance and q(Kˣ) = q(Rˣ) · n

**Mathematics; ledger delta 0 / 0.** The DVR valuation sequence is now equivariant
under compatible ring automorphisms, and `cyclicHerbrandQuotient_units` proves the
conditional identity `q(Kˣ) = q(Rˣ) · n`. Thirteen new theorems across four files;
`UnitsValuationEquivariance.lean` is the new module, imported by `Anabelian.lean`.
The project now has 93 source files under `Anabelian/`.

## Statements and proof route

For a DVR `R`, its fraction field `K`, ring automorphisms `s`, `t`, and
`hst : ∀ r, t (algebraMap R K r) = algebraMap R K (s r)`, write
`σR := Units.mapEquiv s.toMulEquiv`, `σK := Units.mapEquiv t.toMulEquiv`,
`ι := Units.map (algebraMap R K)`, and `v := dvrUnitsValuation R K`.

- **Integral valuation:** `intValuation_irreducible` gives
  `Irreducible ϖ → (dvrHeightOneSpectrum R).intValuation ϖ = WithZero.exp (-1 : ℤ)`.
  Mathlib's `intValuation_eq_exp_neg_multiplicity`, `Irreducible.maximalIdeal_eq`,
  and `multiplicity_self` replace Pass 93's inline integer-divisor argument, and
  its kernel proof now uses the shared lemma. `intValuation_ringEquiv` factors a
  nonzero element as `u * ϖ^m`; `s` preserves units and irreducibles. Zero is separate.
- **Equivariant sequence:** `dvrUnitsInclusion_injective` uses
  `Units.map_injective (IsFractionRing.injective R K)`;
  `dvrUnitsInclusion_equivariant` is `hst` at the unit carrier. These two statements
  omit the unused DVR assumptions. `dvrUnitsValuation_equivariant` writes `x = a/b`
  using `IsFractionRing.div_surjective`, applies `hst`, and rewrites both integral
  valuations. Together with P93's kernel and surjectivity, this gives the SES with
  trivial value-group action.
- **Cyclic naturality:** `map_mulAut_pow`, `map_cyclicDiff`, and `map_cyclicNorm`
  hold for any equivariant hom of commutative groups, without periodicity. The
  proofs use induction with `pow_succ'`/`MulAut.mul_apply`, preservation of products
  and inverses, and `map_prod`. Specialization gives
  `dvrUnitsValuation_cyclicDiff : v (cyclicDiff σK x) = 1` and
  `dvrUnitsValuation_cyclicNorm : v (cyclicNorm σK n x) = (v x)^n`.
- **Assembly:** extract P92's integer torsion proof as
  `multiplicative_int_pow_eq_one`. `finite_herbrandH_norm_diff_int` applies
  `Nat.finite_of_card_ne_zero` to `card_herbrandH_norm_diff_eq_one`. Then
  `herbrandQuotient_mul` consumes the four naturality intertwinings and both
  complex conditions on `Kˣ`; `cyclicHerbrandQuotient_int` finishes the calculation.
  No separate periodicity hypothesis on `Rˣ` is supplied.

## Carried hypotheses and scope

The headline explicitly carries `hn : n ≠ 0`, `hσ : σK ^ n = 1`,
`[Finite (herbrandH (cyclicNorm σR n) (cyclicDiff σR))]`, and the corresponding
instance on `Kˣ`. The first supplies the integer computation and value-group
finiteness; the second supplies the middle complex conditions; the two instances
feed P90. **No necessity or sharpness claim is made for these hypotheses.** No
failure-when-dropped witness is claimed or newly owed. The existing cyclic-pair
source commentary also now uses this carried-hypothesis language.

This pass does not prove `q(Rˣ) = 1`, discharge the supplied unit-group finiteness,
or identify the abstract cyclic norm with a concrete field norm. Next is a design
pass for the local-field unit quotient, with those dependencies kept explicit.
No class field theory or reconstruction result is claimed; R1–R3 remain untouched.

## Verification and governance

`lake build`: **8569 jobs, success, zero warnings/errors**.
`scripts/preflight.sh`: **CLEAN**, including the 93-file import-chain check.
All thirteen new theorem audits are standard-only; the modified P92 integer-quotient
and P93 kernel proofs also retain standard-only audits. The exact new-theorem output
is recorded in the Pass-94 ledger entry and reproduced by the source audit blocks.
Project source scan: zero `axiom` declarations and zero `sorry`/`admit` proof holes.

README, HANDOFF (including the intro and queue), and ROADMAP now agree on Pass 94,
93 project files, L3.1 in progress, and the next unit-group design task. Their stale
current-state passages were replaced by concise current summaries. Historical NOTES
and ledger entries are unchanged; CLAUDE's constitution has no stale pass/count claim.

**Ledger delta: 0 / 0.** No new `structure`/`class`; no owed witness; D1/D2 N/A.

## Pass 94 documentation restoration (2026-09-25)

Correction to the governance account above: the initial Pass-94 commit removed the
README strata/frontier detail and ROADMAP pass summary beyond the authorized status
updates. These two sections are restored below, byte-for-byte from the Pass-93 base
commit `4b55a4e`, with pointers from README and ROADMAP. The archive includes their
then-current frontier claims and module paths; the Pass-94 headers and frontier
summaries in README and ROADMAP remain the current status. Existing NOTES entries
are unchanged.

<a id="pass-93-readme-detail"></a>

### Archived README strata and frontier through Pass 93

The project has earned, axiom-free, the following strata (detail in `NOTES.md` / `ROADMAP.md`):

- **L1 — Galois theory of local & finite fields (Passes 1–21).** `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` as a
  topological group (the first L1 "whole of depth", Pass 10); `Gal(ℚ̄/ℚ)` non-abelian (Pass 3); and
  — the project's **first `DEBT`-discharged-into-theorem** — the residue-reduction surjection
  `Gal(K̄/K) ↠ Gal(𝓀̄/𝓀)`: taken as a `FOUNDATIONAL` boundary at Pass 5, reclassified to `DEBT` at
  Pass 11, and **discharged into a proved `theorem` at Pass 20** (perfect case; the imperfect
  equal-characteristic case is a tracked owed generality, not an axiom).
- **L2 — Higher ramification (Serre, *Local Fields*, ch. IV), DONE (Pass 83).** The stratum closed with the capstone: `G^v` on the absolute Galois group `Gal(K^sep/K)`, a closed subgroup projecting onto every finite level (the inverse limit the upper numbering exists for). Hasse–Arf (ch. V) is deferred to its own rung. The arc, in order: The lower-numbering
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
  plus Herbrand on the canonical carrier `𝒪_{K'}` (Pass 78); the **L2-capstone
  design** — the extension of `G^v` to `Gal(K^sep/K)` (still chapter-IV/L2 material):
  carrier `separableClosure`, preimage-intersection definition, brick ladder B1–B5
  (Pass 79); **B1, the full-group form** — the filtrations on the full `L ≃ₐ[K] L`
  with **Herbrand's theorem along `restrictNormalHom`** (Pass 80); **B2 + B4's
  heart** — the `≤`-pair plumbing in Mathlib's `finGaloisGroupMap` conventions, and
  **Herbrand along the profinite transitions** (Pass 81); **B3 — the absolute `G^v`
  defined**: `⨅`-form on any `E/K`, closed in the Krull topology (Pass 82); and **B5 —
  PROJECTION SURJECTIVITY, the capstone**: the absolute filtration is a genuine inverse
  limit of the finite levels (Pass 83) — **with this, L2 is DONE**; and the **Absolute
  consolidation** — `Anabelian/Absolute/Main.lean` (one audit block for the stratum) plus
  antitonicity, `v ≤ 0` constancy, and **the separation theorem** `⨅_v G^v(E/K) = ⊥`
  (Pass 84).
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
recorded in `ROADMAP.md`; Passes 80–82 laid B1–B3: the full-group form, the profinite
plumbing with Herbrand along the transitions, and now **the absolute `G^v` itself** —
defined, closed in the Krull topology, compatible-from-above with every finite level.
Pass 83 closed B5 — and with it the L2 stratum — Pass 84 consolidated it (the filtration
of `Gal(K^sep/K)`: defined, closed, an inverse limit, antitone, normalized, separating),
and Pass 85 opened L3 with the design inventory: Mathlib's group cohomology is real
(H⁰/H¹/H², LES, Shapiro, Hilbert 90, finite-cyclic periodicity) but Tate cohomology, cup
products, Brauer-H², Lubin–Tate, and any `K^ab` object are absent; the route decision is
**Neukirch-style abstract CFT**, and `ROADMAP.md`'s L3 section is now a five-stage ladder
(L3.0 `K^ab` interface → L3.1 cyclic layer → L3.2 unramified cohomology → L3.3
reciprocity, the wall → L3.4 the ramification correspondence, the R1-relevant piece).
Pass 86 laid L3.0: **`K^ab` exists**
(`Anabelian/ClassField/MaximalAbelian.lean`) — the fixed field of the closed commutator
subgroup, Galois over `K`, with `Gal(K^ab/K)` the topological abelianization (abelian,
proved), maximality as a theorem, and `G^v(K^ab/K)` live via the Pass-82 interface. Pass 87 opened L3.1 with **the
Herbrand quotient** (`Anabelian/ClassField/HerbrandQuotient.lean`, not previously in
Mathlib): the abstract two-endomorphism form with the finite-module triviality theorem
`q(M) = 1` — the bookkeeping device of the cyclic layer. Pass 88 added the counting engine
for `q`-multiplicativity: the 6-cycle alternating-card lemma (finiteness-free) and
`herbrandH` functoriality. Pass 89 built the snake, and
Pass 90 closed the six-term cycle: three generic exactness lemmas (the other three nodes
by the `(f,g)`-swap) feed the alternating-card identity, giving **the multiplicativity
theorem `q(M) = q(M')·q(M'')`** — with Pass 87's triviality, the Herbrand-quotient
calculus is operational. Pass 91 instantiated it for Galois modules: the cyclic pair
(norm `∏σⁱ`, twisted difference `σ/1`, complex conditions) and `q(σ, A)` with the
`(diff, norm)` convention pinned. Pass 92 delivered the fundamental computation
**`q(ℤ) = n`** (`Ĥ⁰ = ℤ/nℤ`, `Ĥ¹ = 0`, with the generic `|Ĥ⁰| = [A : Aⁿ]` presentation
machinery). Pass 93 opened the `q(Lˣ)` track with the valuation exact sequence
`1 → Rˣ → Kˣ → ℤ → 1` for any DVR fraction field — the units-valuation hom, its
surjectivity, and its kernel, all abstract. Next: pair-equivariance + the P90 firing,
then the `q(𝒪ˣ) = 1` wall; or Hasse–Arf.

<a id="pass-93-roadmap-detail"></a>

### Archived ROADMAP pass summary through Pass 93

> **Passes 44–93 built the Herbrand machinery and opened the quotient theory** (ledger stays
> `0 / 0`), all **absent from Mathlib**,
> all axiom-free, on the lower-numbering filtration (Serre IV §§1, 3): **Pass 44** — the **Herbrand
> function** `φ(u) = ∫_0^u dt/(G_0 : G_t)` (`Anabelian/HerbrandFunction.lean`), strictly monotone,
> continuous, `φ(0)=0`, `φ=id` on `(-∞,0]`, `φ≤id` on `[0,∞)`; **Pass 45** — the inverse `ψ = φ⁻¹`
> and the **upper numbering** `G^v(L/K) = G_{⌈ψ(v)⌉}` (`Anabelian/UpperNumbering.lean`): `φ`
> surjective ⟹ `ψ` strictly monotone + continuous, `ψ(0)=0`, `ψ=id` on `(-∞,0]`; `G^v` with
> `G^0=G_0`, antitone, eventually `⊥`; **Pass 46** — the **subgroup compatibility** `H_u = H ∩ G_u`
> (Serre IV §1 Prop. 2, `Anabelian/RamificationSubgroup.lean`, `ramificationGroup_eq_comap`); **Pass
> 47** — the **slope** `φ'(u) = 1/(G_0 : G_u)` (`Anabelian/HerbrandSlope.lean`,
> `herbrandPhi_hasDerivAt_Ioo`, via FTC); **Pass 48** — the **explicit piecewise-linear formula**
> `φ(u) = (|G_1|+…+|G_n|+(u−n)|G_{n+1}|)/|G_0|` on `[n,n+1]` (`Anabelian/HerbrandFormula.lean`,
> `herbrandPhi_eq_affine_formula`); **Pass 49** — the **`ψ` slope** `ψ'(v) = (G_0 : G_{ψ(v)})`
> (`Anabelian/HerbrandPsiSlope.lean`, `herbrandPsi_hasDerivAt`, via the inverse function theorem),
> completing the `φ`/`ψ` derivative picture; **Pass 50** — the **quotient-restriction skeleton**
> (`Anabelian/RamificationQuotient.lean`): `decompositionQuotient : D(A) →* D(A ∩ K')` along
> `Gal(L/K) ↠ Gal(K'/K)` (`K'/K` normal), **exactness at the decomposition level**
> `ker (decompositionQuotient) = range (decompositionRestrict)`, and **inertia preservation**
> `G_0(L/K) → G_0(K'/K)` — the group-theoretic skeleton under Serre Lemma 5, deliberately without
> the `i_{K'/K}` arithmetic; **Pass 51** — **Serre's `i_G` function**
> (`Anabelian/RamificationIndex.lean`): `lowerIndex K A σ : ℕ∞` (generator-free sup form),
> **Lemma 1** `σ ∈ G_i ↔ i < i_G(σ)`, the calculus (`i(σ⁻¹) = i(σ)`,
> `i(στ) ≥ min`, class function, `= ⊤ ↔ σ = 1` under separation), and **`i_H = i_G` on `H`**
> (IV §1 Prop. 2's second half — by `rfl`) — the currency the quotient arithmetic is denominated
> in; **Pass 52** — **surjectivity of the quotient restriction**
> (`Anabelian/RamificationQuotientSurjective.lean`): `𝒪_L` is Galois-stable (integral closure),
> so `D(𝒪_L) = ⊤` and `decompositionQuotient` is **surjective** (via
> `restrictNormalHom_surjective`), giving the first-isomorphism packaging
> `D(A) ⧸ H ≃* D(A ∩ K')` — the `(G/H)` of Herbrand's theorem, realized; **Pass 53** — the
> **concrete `i_G`** (`Anabelian/RamificationIndexGenerator.lean`): the one-generator collapse
> `(∀ a, σa − a ∈ 𝔪^n) ↔ σx − x ∈ 𝔪^n` (Pass 25's telescoping engine upgraded to an iff),
> Lemma 1 in generator form `σ ∈ G_i ↔ σx − x ∈ 𝔪^(i+1)`, and
> **`i_G(σ) = v_L(σx − x)`** (`lowerIndex_eq_addVal`, via a new DVR bridge
> `x ∈ 𝔪^n ↔ n ≤ addVal x`) — under the monogenicity package as **named binders**
> (`hfix` free at `𝒪_L` by Pass 32; `hgen` = classical monogenicity, then a named boundary);
> **Pass 54** — **the monogenicity DISCHARGE** (`Anabelian/ExtensionMonogenicDischarge.lean`,
> Serre III §6 Prop. 12, finite-residue case): **`𝒪_L` is monogenic over `𝒪_K`**
> (`exists_generator_extensionIntegers` — lift a cyclic generator of `𝓀_L^×`; `x^n − 1`
> (`n = |𝓀_L^×|`) is a uniformizer in `𝒪_K[x]` after at most one correction `x ↦ x(1+π₀)`,
> controlled by the unit `n·x^n` since `(n : 𝓀_L) = −1`; Pass 32's engine finishes), so the
> **concrete `i_G` is now UNCONDITIONAL**: `∃ x, ∀ σ, i_G(σ) = v_L(σx − x)`
> (`exists_generator_lowerIndex_eq_addVal`) — no named hypotheses left in the `i_G` theory;
> **Pass 55** — **the subextension characteristic polynomial**
> (`Anabelian/SubextensionCharPoly.lean`, the substrate of Prop. 3): the full product
> `fullProdXSubSMul = ∏_{g ∈ G} (X − g·x)` (all of `G`, with multiplicity — Mathlib's
> `prodXSubSMul` ranges only over the orbit) with monic/degree-`|G|`/kills-`x`/`G`-invariant,
> the **fixed-points descent** (an `H`-fixed integer comes from `A ∩ K'`), and the headline:
> **Serre's polynomial descends** — a monic `F` over `𝒪_L ∩ K'` with
> `F.map (comapRingHom) = ∏_{h ∈ Gal(L/K')} (X − h·x)`, hypothesis-free at `𝒪_L`
> (`D_{K'}(𝒪_L) = ⊤` for any intermediate `K'`); plus the same-base identification
> `𝒪_L ∩ K = 𝒪_K`; **Pass 56** — **the lift-set identity**
> (`Anabelian/RamificationLiftSet.lean`): the fiber of `decompositionQuotient` over `σ̄` is
> the coset `s₀·H` **explicitly** (`decompositionFiberEquiv`, a bijection via P50 exactness +
> P46 injectivity — sums/products over the lifts transport to `H`), and **transporting
> Serre's polynomial along a lift is the fiber product**:
> `f.map s₀ = ∏_{h} (X − (s₀·dr h)·x)`, at `x` the Prop.-3 product `∏_{s ↦ σ̄} (x − s·x)`
> in `H`-parametrized form (per-factor step definitional — P46's `rfl` action agreement);
> **Pass 57** — **`𝒪_L ∩ K' = 𝒪_{K'}` and the coefficient telescoping**
> (`Anabelian/ExtensionComapIntegers.lean`): the identification
> `extensionIntegers_comap_eq` (integrality is insensitive to `K'`-vs-`L` testing — the
> `comap`-level form of P43's canonicity), the induced iso + DVR structure + base map on
> `B = 𝒪_L ∩ K'`, P54's generator **transported to `B`**, and the headline bundle
> `exists_generator_comap_spec`: one `y` with `B = 𝒪_K[y]`,
> **`(σ̄y − y) ∣ (σ̄c − c)` for all `σ̄ ∈ D(B)`, `c ∈ B`** (direction (i)'s arithmetic half),
> and **`i_{K'/K}(σ̄) = addVal_B (σ̄y − y)`** (the left side of the sum formula, concrete);
> **Pass 58** — **Prop. 3 direction (i): `a ∣ b`, PROVED**
> (`Anabelian/RamificationLiftDvd.lean`): the equivariance `ι(σ̄ • c) = s₀ • ι(c)` (P50's
> action-compatibility at the `comapRingHom` level, lifted to polynomials:
> `(σ̄ • F).map ι = (F.map ι).map s₀`), the generic divides-coefficients ⟹
> divides-evaluation lemma, and the assembly: **`ι(σ̄y − y) ∣ ∏_{s ↦ σ̄} (x − s·x)`** —
> abstract (`comapRingHom_smul_sub_dvd_liftProd`) and hypothesis-free at `𝒪_L`
> (`exists_generator_dvd_liftProd`: one `y` with the concrete `i_{K'/K}` AND the
> divisibility for every `x`, `s₀`); **Pass 59** — **the `addVal` bookkeeping**
> (`Anabelian/RamificationAddVal.lean`): the **`e'`-dilation**
> `addVal_A (ι c) = addVal_B c · addVal_A (ι π_B)` (behind it the unit-transfer
> `IsUnit (ι c) ↔ IsUnit c` — a field inverse of an integral `K'`-element is again in `B`),
> and the **fiber sum** `addVal (∏_h (x − (s₀·dr h)·x)) = Σ_h i_{L/K}(s₀·dr h)` (P53–54 per
> factor + generic `addVal_prod`/`addVal_neg`) — both sides of the sum formula are now
> `addVal`-readable; **Pass 60** — **the representation and field-generation layer**
> (`Anabelian/ExtensionGeneratorRep.lean`): closure membership IS polynomial representation
> (`exists_polynomial_map_eval_eq`, generic; at `𝒪_L`: every integer is
> `(g.map (extensionAlgebraMap)).eval x`), the commuting square
> `ι ∘ (𝒪_K → B) = extensionAlgebraMap K L`, and **`L = K'(x)`**
> (`adjoin_generator_eq_top` — the `𝒪_K`-ring generator generates `L` as a field over any
> intermediate `K'`, by closure induction + the valuation dichotomy) (records in
> `NOTES.md`/`AXIOM_LEDGER.md`); **Pass 61** — **the remainder-vanishing brick**
> (`Anabelian/RamificationMinpolyBound.lean`): a polynomial over `B` of degree
> `< |D_{K'}(𝒪_L)| = [L:K']` whose `ι`-image kills `x` is **zero**
> (`eq_zero_of_map_comapRingHom_eval_eq_zero` — over `K'` it would be a nonzero annihilator
> below `deg (minpoly K' x) = [K'(x):K'] = [L:K']`, by P60's `L = K'(x)` + Galois
> cardinality + P55's `D = ⊤`; minimality forbids it) — the last new mathematics before
> Prop. 3; **Pass 62** — **direction (ii) `b ∣ a`, PROVED**
> (`Anabelian/RamificationDivision.lean`, `liftProd_dvd_comapRingHom_smul_sub`): for EVERY
> `y ∈ B` and lift `s₀`, `∏_{s ↦ σ̄} (x − s·x) ∣ ι(σ̄y − y)` — Serre's monic division,
> every step a named brick (P60 representation, P55 descent, P61 remainder-vanishing, P57
> fixed base coefficients, P58 equivariance, P56 lift-set identity) (records in
> `NOTES.md`/`AXIOM_LEDGER.md`); **Pass 63** — **SERRE IV §1 PROP. 3, PROVED**
> (`Anabelian/RamificationSumFormula.lean`, `lowerIndex_decompositionQuotient_mul_eq_sum`):
> **`i_{K'/K}(σ̄) · e' = Σ_{h ∈ H} i_{L/K}(s₀ · dr h)`** for every `σ̄` and every
> irreducible `π_B` (`e' = addVal(ι π_B)`) — generator-free, no `σ̄ ≠ 1` needed (both sides
> `⊤` there), eight lines of assembly over the P50–62 substrate: mutual divisibility
> (P58 + P62) ⟹ equal `addVal` ⟹ the two P57/P59 readings. **The quotient-arithmetic wall
> — first named at Pass 47 as "the transitivity wall" — is DOWN, axiom-free** (records in
> `NOTES.md`/`AXIOM_LEDGER.md` Passes 44–63).
> **Pass 64** was governance/infrastructure: the long-deferred **flat→folders refactor**
> (`scripts/refactor.sh`, table extended to all 64 files, executed as git-tracked renames;
> nine content folders — `Galois`, `FiniteField`, `Reduction`, `Ramification`, `Herbrand`,
> `Extension`, `LocalField`, `Quotient`, `ForMathlib`; module paths changed, declaration
> names unchanged; `preflight.sh`/`chain_check.py` now recurse; full rebuild verified).
> **Pass 65** — **the fiber index profile** (`Anabelian/Quotient/IndexProfile.lean`, the
> first Lemma-5 brick): with a coset/fiber maximizer `s₁` (exists by finiteness),
> **`i_{L/K}(s₁·h) = min(i_H(h), j)` for every `h ∈ H`** (`j = i(s₁)` — Serre's `j(σ̄)`),
> `Normal`-free coset form + fiber form + the **`Σ min` sum form**
> `Σ_{s ↦ σ̄} i(s) = Σ_h min(i_H(h), j)` — all pure P51 calculus.
> **Pass 66** — **the double count** (`Anabelian/Ramification/LowerIndexCount.lean`):
> `Σ_σ min(i(σ), m) = Σ_{k<m} |G_k|` for ANY extension's decomposition group
> (`sum_min_lowerIndex_eq`) — decompose `min` into level-set indicators
> (`enat_min_coe_eq_sum`, generic `ℕ∞`), swap sums, and each level set IS a ramification
> group by P51's Lemma 1. With P63 + P65: `e'·i_{K'/K}(σ̄) = Σ_{k<j} |H_k|`.
> **Pass 67** — **the `φ`-bridge** (`Anabelian/Herbrand/SumBridge.lean`):
> `Σ_{k ≤ n} |G_k| = |G_0|·(φ(n) + 1)` (`sum_ramificationOrders_range_succ` — P48's
> `herbrandPhi_natCast` with the `k = 0` term absorbed) + the two cast forms connecting to
> P66's `ℕ∞` output (`natCast_sum_natCard_eq`, `sum_natCard_enat_eq`) — the Lemma-5
> numerical chain is fully typed.
> **Pass 68** — **`e'` in ideal form** (`Anabelian/Quotient/RamificationIdx.lean`): the
> inventory found Mathlib HAS `|inertia| = e` (`Ideal.card_inertia_eq_ramificationIdxIn`,
> Dedekind + separable residue ✓), so `e' = |H_0|` is an identification program; this pass
> is its left half — the `comapAlgebra` scaffold (`𝒪_L` as a `B`-algebra, no diamond),
> `𝔪_B·𝒪_L = 𝔪_L^n` with `(n : ℕ∞) = addVal(ι π_B)`, and
> **`Ideal.ramificationIdx 𝔪_B 𝔪_L = n`** — P59's `addVal`-form `e'` IS Mathlib's
> ramification index.
> **Pass 69** — **the `IsGaloisGroup` instance package**
> (`Anabelian/Quotient/GaloisGroup.lean`): `D_{K'}(𝒪_L)` is a Galois group for
> `B ⊆ 𝒪_L` in Mathlib's sense — **faithful** (valuation dichotomy), **commutes**
> (`AlgEquiv.commutes` on the `comapAlgebra` scalars), **isInvariant** (P55's fixed-points
> descent + `D = ⊤`) — the gateway hypothesis of `card_inertia_eq_ramificationIdxIn`.
> **Pass 70** — **the remaining instances + the inertia matching**
> (`Anabelian/Quotient/InertiaSetup.lean`): the project's `G₀` IS Mathlib's
> `Ideal.inertia 𝔪_L D` (P23 built the filtration from `Ideal.inertia` — the matching is
> `pow_one`/`norm_num`!), plus `Module.IsTorsionFree`, `𝔪_L.LiesOver 𝔪_B` (P50+P59), the
> tower `𝒪_K → B → 𝒪_L` as scalar algebras (P60's square as the tower axiom),
> `Module.Finite ↥B ↥𝒪_L` (P32 restricted), and separable residue (finite fields perfect);
> probe-verified: `IsDedekindDomain` automatic from the DVR instances. **Every hypothesis of
> `card_inertia_eq_ramificationIdxIn` is now available.**
> **Pass 71** — **`e' = |H₀|`, PROVED** (`Anabelian/Quotient/InertiaCard.lean`):
> `(Nat.card (ramificationGroup K' (𝒪_L) 0) : ℕ∞) = addVal_{𝒪_L}(ι π_B)` — the classical
> `e = |inertia|` for `L/K'`, closed by four rewrites over the P68–70 identification.
> **Every input to Lemma 5's numerical heart is now proved.**
> **Pass 72** — **THE NUMERICAL LEMMA 5, PROVED**
> (`Anabelian/Quotient/NumericalLemmaFive.lean`, `exists_lowerIndex_eq_herbrandPhi`): for
> every `σ̄ ≠ 1`, **`i_{K'/K}(σ̄) = φ_{L/K'}(j(σ̄) − 1) + 1`** — with the fiber maximizer
> `s₁`, its index profile, and `j(σ̄), i_{K'/K}(σ̄) ∈ ℕ` all exposed; pure assembly of
> P63+P65+P66+P67+P71 (finiteness of `j` for `σ̄ ≠ 1` via P51's `⊤`-criterion + DVR
> separation; `j = 0` rides on `φ(−1) = −1`); no `Fintype` hypothesis needed.
> **Pass 73** — **SERRE IV §3 LEMMA 5, PROVED** (`Anabelian/Quotient/LemmaFive.lean`,
> `map_ramificationGroup_eq_ceil`): for every `u : ℕ`,
> **`(G_u).map (decompositionQuotient) = ramificationGroup K B ⌈φ_{L/K'}(u)⌉₊`** —
> `(G/H)_{φ_{L/K'}(u)} = G_u H/H`, Herbrand's renumbering lemma. Membership on both sides
> through P51's Lemma 1, mediated by P72's numerical identity, the lift-membership
> characterization (profile bounds the fiber, maximizer realizes it), and the ceiling
> bridge through `φ`'s strict monotonicity (P44); surjectivity (P52) supplies the lift.
> **Pass 74** — **the card multiplicativity, PROVED**
> (`Anabelian/Quotient/CardMultiplicativity.lean`, `card_ramificationGroup_eq_mul`):
> **`|G_u| = |(G/H)_{⌈φ_{L/K'}(u)⌉}| · |H_u|`** for every `u : ℕ` — the arithmetic heart of
> Prop. 15: the generic count `|S| = |S.map f|·|ker f ⊓ S|` (Lagrange + first isomorphism)
> on `dq|_{G_u}`, image by Lemma 5 (P73), kernel by P50's `ker = range` + P46's
> `H_u = H ∩ G_u` + injectivity; `u = 0` gives `e_{L/K} = e_{K'/K}·e_{L/K'}` at inertia
> level. **Next: Prop. 15's analytic gluing** — `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}` as
> functions (both sides piecewise linear, equal at `0`, slopes matched by this
> multiplicativity read through P47–49), **then Herbrand's theorem** (Prop. 14 —
> `(G/H)^v = G^v H/H`, Lemma 5 through P45's upper numbering)
> `(G/H)_{φ_{L/K'}(u)} = G_u H/H`, then **`φ`-transitivity** `φ_{L/K} = φ_{K'/K} ∘ φ_{L/K'}`
> (Prop. 15) and **Herbrand's theorem** `(G/H)^v = G^v H/H` (Prop. 14), where Pass 43's
> canonicity and the tower theory earn their keep. This all built on **Pass 43's
> canonicity** (intermediate fields usable as base fields) and the **Pass 41 assembly**. (Pass 42 was
> governance: it discarded an unledgered 2-axiom orphan and added a mechanical clean-tree gate to
> `scripts/preflight.sh`; the R1-floor — axiomatizing L3 for a conditional R1 result — remains a
> permitted-but-deferred option, never to be entered via an untracked file.)

<!-- End of the verbatim Pass-93 excerpts. -->


<a id="pass-95"></a>

### Pass 95 (2026-09-26) — conditional unit reduction and the normal-lattice design

**Ledger delta: 0 / 0; active count: 0 FOUNDATIONAL / 0 DEBT.** The one new proved
result is `Anabelian.finite_acyclic_kernel_reduction`, in
`Anabelian/ClassField/FiniteAcyclic.lean`, imported by `Anabelian.lean`. The project
has 94 source files under `Anabelian/`. Everything else in this entry is a future
proof target or an inventory of existing inputs. No arithmetic theorem or proof
placeholder is added to the library. No new `structure`/`class`, no sharpness claim,
and no owed witness; D1/D2 N/A. All displayed hypotheses are carried.

The objective of the designed arc is `q(Rˣ) = 1`, for
`R = extensionIntegers K L` in a finite cyclic Galois extension `L/K` of a
nonarchimedean local field. The abstract DVR layer stays separate. The route works
in both characteristics: use a sufficiently small lattice generated by a field
normal basis, then the unit subgroups `V_i = 1 + π^i B`. Their layers are regular
modules over the **base** residue field. Exactness on those layers, adic
completeness, and separation give exactness on `V_0`; its finite index then permits
the proved conditional reduction. The field normal basis already exists in
Mathlib. Integral scaling, the lattice sandwich, and all the unit arithmetic still
require proofs. No Hilbert 90, reciprocity, or R1–R3 result is proved or assumed.

#### 1. The conditional reduction proved in this pass

In namespace `Anabelian`, with `import Anabelian.ClassField.Multiplicativity`, the
complete statement is:

```lean
theorem finite_acyclic_kernel_reduction
    {M' M M'' : Type*} [CommGroup M'] [CommGroup M] [CommGroup M''] [Finite M'']
    (ι : M' →* M) (π : M →* M'')
    (f' g' : M' →* M') (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hexact : ι.range = π.ker)
    (hfι : ∀ x, ι (f' x) = f (ι x)) (hgι : ∀ x, ι (g' x) = g (ι x))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x, f (g x) = 1) (hgf : ∀ x, g (f x) = 1)
    [Subsingleton (herbrandH f' g')] [Subsingleton (herbrandH g' f')] :
    Finite (herbrandH f g) ∧ Finite (herbrandH g f) ∧ herbrandQuotient f g = 1
```

The proof first uses `snake_exact_mid` and its `(f,g)` swap. The images from the
two subsingleton groups are trivial, so `MonoidHom.ker_eq_bot_iff` gives injections
from each middle cohomology group into the corresponding cohomology of `M''`.
Those target groups are finite as quotients of subgroups of a finite group;
`Finite.of_injective` supplies both middle instances. This step precedes
`herbrandQuotient_mul`, which needs the middle degree-one instance. The kernel
quotient is one by `Nat.card_eq_one_iff_unique`; the finite quotient's quotient is
one by `herbrandQuotient_eq_one_of_finite`. Surjectivity of `π` transports the two
complex conditions to `M''`. No finiteness of `M` is supplied.

Reproducible audit, also present in the source:

```text
'Anabelian.finite_acyclic_kernel_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

#### 2. Complete future statement catalogue: conventions

The Lean blocks between the signature markers below form one ordered catalogue.
All contexts, definitions, binders, and conclusions are written here; no parley
record or other worktree's scratch file is needed. The theorem signatures and the
definitions without bodies are **unproved targets**, not declarations imported by
the project. The concrete helper definitions merely fix their meaning. To test
elaboration, use the extraction recipe in section 10: it adds temporary proof
placeholders only under ignored `.lake/`. Elaboration checks types, not truth.
`import Anabelian` is a probe convenience; the committed theorem uses the narrower
import stated above.

`H0 σ n` means invariants modulo norms; `H1 σ n` means norm-one elements modulo
cyclic differences. The quotient convention is `q = |H0| / |H1|` in `ℚ`.

<!-- pass95-signatures-begin -->

```lean
import Anabelian
import Mathlib.FieldTheory.Galois.NormalBasis

open scoped ValuativeRel Pointwise
open IsLocalRing

namespace Anabelian.Pass95Design
noncomputable section

abbrev H0 {M : Type*} [CommGroup M] (σ : MulAut M) (n : ℕ) :=
  herbrandH (cyclicDiff σ) (cyclicNorm σ n)

abbrev H1 {M : Type*} [CommGroup M] (σ : MulAut M) (n : ℕ) :=
  herbrandH (cyclicNorm σ n) (cyclicDiff σ)
```

#### 3. Generic action, layer, and lifting targets (no fields)

`restrictAut` and `quotientAut` expose the inclusion and projection compatibility
needed by P94's `map_cyclicDiff` and `map_cyclicNorm`. `Layer` uses `subgroupOf`;
when the filtration is antitone, it is the usual successive quotient.

`ker_eq_range_of_filtration` is the adopted general `(f,g)` lifting lemma.
`layer_of_surjective` supplies its correction hypothesis from a surjective layer
map: an element killed by the induced `fW` lifts through `gW`, with the error in
the next subgroup. The cyclic lemma is the derived interface obtained by applying
the general lemma in both orders. It introduces no independent arithmetic input.

```lean
section Stable
variable {M : Type*} [CommGroup M]

def restrictAut (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) : MulAut S :=
  (σ.subgroupMap S).trans (MulEquiv.subgroupCongr h)

def quotientAut (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) : MulAut (M ⧸ S) :=
  QuotientGroup.congr S S σ h

theorem restrictAut_coe (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (x : S) :
    (restrictAut σ S h x : M) = σ x

theorem quotientAut_mk (σ : MulAut M) (S : Subgroup M)
    (h : S.map σ.toMonoidHom = S) (x : M) :
    quotientAut σ S h (QuotientGroup.mk' S x) =
      QuotientGroup.mk' S (σ x)

abbrev Layer (F : ℕ → Subgroup M) (i : ℕ) :=
  (F i) ⧸ ((F (i + 1)).subgroupOf (F i))

def layerAut (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i : ℕ) :
    MulAut (Layer F i)

theorem layerAut_mk (σ : MulAut M) (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i : ℕ) (x : F i) :
    layerAut σ F hF i
        (QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i)) x) =
      QuotientGroup.mk' ((F (i + 1)).subgroupOf (F i))
        (restrictAut σ (F i) (hF i) x)

theorem herbrandH_subsingleton_of_exact (f g : M →* M)
    (h : g.range = f.ker) : Subsingleton (herbrandH f g)

theorem ker_eq_range_of_filtration (f g : M →* M)
    (hfg : ∀ x, f (g x) = 1)
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ i, ∀ x ∈ F i, g x ∈ F i)
    (hlayer : ∀ i, ∀ x ∈ F i, f x ∈ F (i + 1) →
      ∃ y ∈ F i, x * (g y)⁻¹ ∈ F (i + 1))
    (hsep : ∀ x, (∀ i, x ∈ F i) → x = 1)
    (hcomplete : ∀ z : ℕ → M,
      (∀ i, z (i + 1) * (z i)⁻¹ ∈ F i) →
      ∃ y, ∀ i, y * (z i)⁻¹ ∈ F i) :
    f.ker = g.range

theorem layer_of_surjective {W : Type*} [CommGroup W]
    (f g : M →* M) (S T : Subgroup M)
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S)
    (θ : S →* W) (hθ : Function.Surjective θ)
    (hker : ∀ x : S, θ x = 1 ↔ (x : M) ∈ T)
    (fW gW : W →* W)
    (hfθ : ∀ x : S, θ ⟨f x, hfS x x.property⟩ = fW (θ x))
    (hgθ : ∀ x : S, θ ⟨g x, hgS x x.property⟩ = gW (θ x))
    (hW : fW.ker ≤ gW.range) :
    ∀ x ∈ S, f x ∈ T → ∃ y ∈ S, x * (g y)⁻¹ ∈ T

theorem cyclic_exact_of_complete_filtration
    (σ : MulAut M) (n : ℕ) (hσ : σ ^ n = 1)
    (F : ℕ → Subgroup M)
    (hF : ∀ i, (F i).map σ.toMonoidHom = F i)
    (hzero : F 0 = ⊤) (hanti : Antitone F) (hsep : (⨅ i, F i) = ⊥)
    (hcomplete : ∀ u : ℕ → M,
      (∀ i, u (i + 1) * (u i)⁻¹ ∈ F i) →
      ∃ x : M, ∀ i, x * (u i)⁻¹ ∈ F i)
    (hlayer : ∀ i,
      (cyclicNorm (layerAut σ F hF i) n).range =
        (cyclicDiff (layerAut σ F hF i)).ker ∧
      (cyclicDiff (layerAut σ F hF i)).range =
        (cyclicNorm (layerAut σ F hF i) n).ker) :
    (cyclicNorm σ n).range = (cyclicDiff σ).ker ∧
      (cyclicDiff σ).range = (cyclicNorm σ n).ker

end Stable
```

In the lifting proof to be written, start with the identity approximation; use
`hlayer` to correct at depth `i`; apply `hcomplete` to the partial products. The
stability of `g` puts the image of each remaining discrepancy in `F i`.
Separation kills the final error. In the cyclic application, periodicity supplies
both complex conditions, and subgroup stability makes both cyclic maps preserve
the filtration. Finite-layer quotient value one alone would not supply `hlayer`:
the construction uses both range/kernel equalities.

The regular action is indexed directly by the group. For a finite cyclic group,
constants are norms and product-one functions are cyclic differences. The future
proof enumerates the group by powers of a generator and telescopes; it requires
no division by its order.

```lean
section Regular
variable {G C : Type*} [Group G] [CommGroup C]

def regularShift (g : G) : MulAut (G → C) :=
  MulEquiv.arrowCongr (Equiv.mulLeft g) (MulEquiv.refl C)

theorem regularShift_apply (g : G) (f : G → C) (h : G) :
    regularShift g f h = f (g⁻¹ * h)

theorem regular_cyclic_exact [Finite G] (g : G)
    (hgen : Subgroup.zpowers g = ⊤) :
    (cyclicNorm (regularShift (C := C) g) (Nat.card G)).range =
      (cyclicDiff (regularShift g)).ker ∧
    (cyclicDiff (regularShift (C := C) g)).range =
      (cyclicNorm (regularShift g) (Nat.card G)).ker

end Regular
```

#### 4. Abstract DVR filtration, finite quotients, and the field finiteness bridge

These statements assume a DVR, with a finite residue field only where displayed.
They do not assume a local field or completeness. `U^0` is all units;
`U^m = {u | u - 1 ∈ 𝔪^m}`. Finite quotients follow from
`Ideal.finite_quotient_pow` and the unit map into the finite quotient ring.
The residue quotient at depth one uses surjectivity of the residue map on units.

For positive depth the coefficient map has kernel `U^(m+1)`. Its action formula
retains **both** the residue automorphism and the uniformizer factor: if
`s π = π*c`, the coefficient transforms by `residue(s a) * residue(c)^m`.
Consequently there is no unconditional graded exactness assertion for this
natural filtration. Divisibility of the extension degree by the residue
characteristic alone does not determine these layers' cohomology; the action
must also be specified. This is why the designed acyclicity proof uses regular
lattice layers instead.

```lean
section DVR
variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def unitFiltration (m : ℕ) : Subgroup Rˣ :=
  (Units.map (Ideal.Quotient.mk (maximalIdeal R ^ m)).toMonoidHom).ker

theorem mem_unitFiltration (m : ℕ) (u : Rˣ) :
    u ∈ unitFiltration R m ↔ (u : R) - 1 ∈ maximalIdeal R ^ m

theorem unitFiltration_zero : unitFiltration R 0 = ⊤

theorem unitFiltration_antitone : Antitone (unitFiltration R)

theorem unitFiltration_separated : (⨅ m, unitFiltration R m) = ⊥

theorem unitFiltration_stable (s : R ≃+* R) (m : ℕ) :
    (unitFiltration R m).map (Units.mapEquiv s.toMulEquiv).toMonoidHom =
      unitFiltration R m

theorem finite_unitQuotient [Finite (ResidueField R)] (m : ℕ) :
    Finite (Rˣ ⧸ unitFiltration R m)

theorem finite_units_quotient_of_le [Finite (ResidueField R)]
    (S : Subgroup Rˣ) (m : ℕ) (hS : unitFiltration R m ≤ S) :
    Finite (Rˣ ⧸ S)

def unitsResidueEquiv :
    (Rˣ ⧸ unitFiltration R 1) ≃* (ResidueField R)ˣ

def unitCoeff (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    unitFiltration R m →* Multiplicative (ResidueField R)

theorem unitCoeff_spec (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m)
    (u : unitFiltration R m) (a : R)
    (ha : (u.val : R) = 1 + π ^ m * a) :
    unitCoeff R π hπ m hm u = Multiplicative.ofAdd (residue R a)

theorem unitCoeff_exact (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (unitCoeff R π hπ m hm) ∧
    (unitCoeff R π hπ m hm).ker =
      (unitFiltration R (m + 1)).subgroupOf (unitFiltration R m)

theorem unitCoeff_action (π : R) (hπ : Irreducible π) (m : ℕ) (hm : 0 < m)
    (s : R ≃+* R) (c : Rˣ) (hc : s π = π * c)
    (u : unitFiltration R m) (a : R)
    (ha : (u.val : R) = 1 + π ^ m * a) :
    unitCoeff R π hπ m hm
        (restrictAut (Units.mapEquiv s.toMulEquiv) (unitFiltration R m)
          (unitFiltration_stable R s m) u) =
      Multiplicative.ofAdd (residue R (s a) * residue R (c : R) ^ m)
```

The second P94 finiteness input can be derived from its first input even in the
abstract DVR/fraction-field setting:

```lean
variable (L : Type*) [Field L] [Algebra R L] [IsFractionRing R L]

theorem finite_H1_fractionField (s : R ≃+* R) (t : L ≃+* L)
    (hst : ∀ r, t (algebraMap R L r) = algebraMap R L (s r))
    (n : ℕ) (hn : n ≠ 0) (hσ : Units.mapEquiv t.toMulEquiv ^ n = 1)
    [Finite (H1 (Units.mapEquiv s.toMulEquiv) n)] :
    Finite (H1 (Units.mapEquiv t.toMulEquiv) n)

end DVR
```

The planned proof makes `H1(Rˣ) → H1(Lˣ)` surjective. For `N x = 1`, P94's
`dvrUnitsValuation_cyclicNorm` gives `(v x)^n = 1`; P92/P94's
`multiplicative_int_pow_eq_one n hn` gives `v x = 1`. P93's kernel equality lifts
`x` to an integral unit. Inclusion naturality and injectivity reflect its
norm-one condition, and quotient projection supplies a representative of every
class. This proves finiteness without claiming `H1(Lˣ)` is trivial.

#### 5. Identifying the cyclic norm with the field norm

These two statements require only finite Galois field theory. The generator
hypothesis enumerates **all** automorphisms; periodicity alone is not used as an
enumeration hypothesis. Reindex `Algebra.norm_eq_prod_automorphisms` by the powers
of `g`, using `orderOf_eq_card_of_zpowers_eq_top`, `finEquivPowers`, and
`IsGalois.card_aut_eq_finrank`. The second equality is the bundled hom version of
the first. For integral units, P94 naturality and `integerAut_coe` below give the
same equality after inclusion into `Lˣ`.

```lean
section Galois
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

abbrev σL (g : Gal(L/K)) : MulAut Lˣ :=
  Units.mapEquiv g.toRingEquiv.toMulEquiv

variable [FiniteDimensional K L] [IsGalois K L]

theorem cyclicNorm_eq_fieldNorm (g : Gal(L/K))
    (hgen : Subgroup.zpowers g = ⊤) (x : Lˣ) :
    (cyclicNorm (σL K L g) (Module.finrank K L) x : L) =
      algebraMap K L (Algebra.norm K (x : L))

theorem cyclicNorm_eq_fieldNorm_units (g : Gal(L/K))
    (hgen : Subgroup.zpowers g = ⊤) :
    cyclicNorm (σL K L g) (Module.finrank K L) =
      (Units.map (algebraMap K L).toMonoidHom).comp
        (Units.map (Algebra.norm K))

end Galois
```

This comparison is parallel to the abstract quotient calculation. It does not
identify `H1(Lˣ)` with the trivial group or prove the norm-index theorem.

#### 6. The explicit local-field interface and adic-completeness transport

From this point the context is specifically `IsNonarchimedeanLocalField K` and a
finite Galois extension `L/K`. The carrier `↥(extensionIntegers K L)` is spelled out
in the Lean signatures. The scalar action is explicitly the one from
`extensionAlgebraMap K L`. Existing project results supply its DVR and
fraction-field structures and finite residue field. No abstract DVR hypothesis
has been silently strengthened.

`integerAut` restricts a Galois automorphism using
`decompositionSubgroup_extensionIntegers_eq_top` and
`MulSemiringAction.toRingEquiv`. The carrier formula gives exactly P94's `hst`.
`generator_period` uses positive finite degree and the order/cardinality identity
to derive the nonzero-degree and periodicity inputs in the local application.

```lean
section Local
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]


local instance : Algebra (↥𝒪[K]) (↥(extensionIntegers K L)) := (extensionAlgebraMap K L).toAlgebra

def integerAut (g : Gal(L/K)) : (↥(extensionIntegers K L)) ≃+* (↥(extensionIntegers K L))

abbrev σR (g : Gal(L/K)) : MulAut (↥(extensionIntegers K L))ˣ :=
  Units.mapEquiv (integerAut K L g).toMulEquiv

theorem integerAut_coe (g : Gal(L/K)) (r : (↥(extensionIntegers K L))) :
    ((integerAut K L g r : (↥(extensionIntegers K L))) : L) = g (r : L)

theorem generator_period (g : Gal(L/K)) (hgen : Subgroup.zpowers g = ⊤) :
    Module.finrank K L ≠ 0 ∧
    σL K L g ^ Module.finrank K L = 1 ∧
    σR K L g ^ Module.finrank K L = 1

theorem isAdicComplete_extensionIntegers :
    IsAdicComplete (maximalIdeal (↥(extensionIntegers K L))) (↥(extensionIntegers K L))
```

The adopted completeness route is transport of Mathlib's `IsAdicComplete`, not a
new compactness theorem. Inside the future transport proof install
`extensionValuativeRel K L`, `ValuativeRel.topologicalSpace L`,
`isNonarchimedeanLocalField_extension K L`,
`IsTopologicalAddGroup.rightUniformSpace L`, and
`isUniformAddGroup_of_addCommGroup (G := L)`. Under these instances Mathlib supplies
`IsAdicComplete 𝓂[L] 𝒪[L]`. Transport it across
`valued_integer_extensionValuativeRel K L`, the equality of that integer subring
with `(extensionIntegers K L).toSubring`. The instance path has been probed; the
transport theorem above remains unproved. Later, `IsPrecomplete.prec` turns
coherent congruences into limits. No completeness is inferred at the abstract
DVR stage.

#### 7. Small normal lattice, its unit groups, and their regular layers

Use the existing field basis `IsGalois.normalBasis K L`, with
`normalBasis_apply : b g = g (b 1)`. First scale its generator by a base-field
uniformizer power until every conjugate is integral. For its integral span `B₀`,
module-finiteness of the extension integers and the fact that `B₀` spans `L` give
a sandwich `π^r R ⊆ B₀ ⊆ R`. Scale further to `B = π^t B₀` with `t ≥ r+1`:
`B ⊆ 𝔪_R` and `B*B ⊆ πB`. The sandwich and the ramification comparison of
uniformizer powers give `𝔪_R^m ⊆ B` for some `m`. This requests a normal basis
for the **smaller lattice**, not an integral normal basis for all of `R`.
`IsIntegralClosure.finite`, used in `Extension/ResidueFinite.lean`, is the
module-finiteness input. No PID/cyclic-vector proof of the field normal basis is
queued: Mathlib already supplies it.

For each `i`, construct `V_i = 1 + π^i B` as a subgroup of `Rˣ`. Multiplication
uses `B*B ⊆ πB`. For inversion, if `x ∈ π^iB`, then `1+x` is a unit since
`x ∈ 𝔪_R`; with `z = (1+x)⁻¹ - 1`, the identity `z = -x - xz`, iterated modulo
ideal powers, puts `z` in the closed lattice `π^iB`. The sandwich makes that
lattice open and adically closed. These are proof routes, not proofs supplied
in Pass 95.

The last conjunct of `lattice_unit_groups_properties` is the actual limit
property used by the lifting theorem. The two cofinality conjuncts relate the
lattice filtration to ideal powers. Differences of a multiplicatively coherent
unit sequence are then adically small; `IsPrecomplete.prec` gives a limit in the
ring, and its congruence to the initial unit puts it in the unit group. Adic
closedness preserves every `V_i` congruence. The same comparison gives separation.

```lean
theorem exists_small_normal_lattice (π : (↥𝒪[K])) (hπ : Irreducible π) :
    ∃ (B : Submodule (↥𝒪[K]) (↥(extensionIntegers K L)))
      (b : Module.Basis Gal(L/K) (↥𝒪[K]) B) (a : (↥(extensionIntegers K L))),
      (∀ g : Gal(L/K), (b g : (↥(extensionIntegers K L))) = integerAut K L g a) ∧
      (∀ x ∈ B, x ∈ maximalIdeal (↥(extensionIntegers K L))) ∧
      (∀ x ∈ B, ∀ y ∈ B, x * y ∈ π • B) ∧
      (∃ m : ℕ, ∀ x ∈ maximalIdeal (↥(extensionIntegers K L)) ^ m, x ∈ B)

variable (π : (↥𝒪[K])) (hπ : Irreducible π) (B : Submodule (↥𝒪[K]) (↥(extensionIntegers K L)))
  (b : Module.Basis Gal(L/K) (↥𝒪[K]) B) (a : (↥(extensionIntegers K L)))
  (hbas : ∀ g : Gal(L/K), (b g : (↥(extensionIntegers K L))) = integerAut K L g a)
  (hsmall : ∀ x ∈ B, x ∈ maximalIdeal (↥(extensionIntegers K L)))
  (hmul : ∀ x ∈ B, ∀ y ∈ B, x * y ∈ π • B)
  (hopen : ∃ m : ℕ, ∀ x ∈ maximalIdeal (↥(extensionIntegers K L)) ^ m, x ∈ B)

include hπ hbas hsmall hmul hopen in
theorem exists_lattice_unit_groups :
    ∃ V : ℕ → Subgroup (↥(extensionIntegers K L))ˣ, ∀ i u,
      u ∈ V i ↔ (u : (↥(extensionIntegers K L))) - 1 ∈ (π ^ i) • B

variable (V : ℕ → Subgroup (↥(extensionIntegers K L))ˣ)
  (hV : ∀ i u, u ∈ V i ↔ (u : (↥(extensionIntegers K L))) - 1 ∈ (π ^ i) • B)

include hπ hbas hsmall hmul hopen hV in
theorem lattice_unit_groups_properties (g : Gal(L/K)) :
    Antitone V ∧ (⨅ i, V i) = ⊥ ∧
    (∀ i, (V i).map (σR K L g).toMonoidHom = V i) ∧
    (∃ m : ℕ, unitFiltration (↥(extensionIntegers K L)) m ≤ V 0) ∧
    (∀ m : ℕ, ∃ i : ℕ, V i ≤ unitFiltration (↥(extensionIntegers K L)) m) ∧
    (∀ u : ℕ → (↥(extensionIntegers K L))ˣ, u 0 ∈ V 0 →
      (∀ i, u (i + 1) * (u i)⁻¹ ∈ V i) →
      ∃ x : (↥(extensionIntegers K L))ˣ, x ∈ V 0 ∧ ∀ i, x * (u i)⁻¹ ∈ V i)

include hπ hbas hsmall hmul hopen hV in
theorem lattice_unit_layer_regular (g : Gal(L/K))
    (hstable : ∀ i, (V i).map (σR K L g).toMonoidHom = V i) (i : ℕ) :
    ∃ e : Layer V i ≃* (Gal(L/K) → Multiplicative (ResidueField (↥𝒪[K]))),
      ∀ x, e (layerAut (σR K L g) V hstable i x) =
        regularShift g (e x)
```

The layer equivalence takes `(1+x)` to the coefficients of `x` modulo the next
scaled lattice. Products linearize because `π^iB * π^iB ⊆ π^(i+1)B`.
`B/πB` has basis indexed by `Gal(L/K)` over `ResidueField 𝒪[K]`. The identity
`g(b_h) = b_(g*h)` makes the coordinate action `f(h) ↦ f(g⁻¹*h)`, exactly the
displayed `regularShift`. This is a statement of equivariant equivalence, not
just a comparison of cardinalities.

#### 8. Assembly targets and both carried finiteness inputs

Apply the generic lifting theorem in both orders on `M := V 0`, with
`F i := (V i).subgroupOf (V 0)` and the restricted action. The regular layer
equivalences supply both exactness conditions. Completeness and separation come
from section 7. `herbrandH_subsingleton_of_exact` then makes both cohomology
groups of `V 0` subsingletons. `U^m ≤ V 0` and
`finite_units_quotient_of_le` give a finite full-unit quotient. The first statement
below records this intermediate outcome explicitly; the next two are the arc's
synthesis targets. No lattice data are hypotheses of these synthesis statements.

```lean
theorem exists_cohomologicallyTrivial_units
    (g : Gal(L/K)) (hgen : Subgroup.zpowers g = ⊤) :
    ∃ V : Subgroup (↥(extensionIntegers K L))ˣ,
      V.map (σR K L g).toMonoidHom = V ∧
      Finite ((↥(extensionIntegers K L))ˣ ⧸ V) ∧
      (∀ u ∈ V, cyclicDiff (σR K L g) u = 1 →
        ∃ v ∈ V, cyclicNorm (σR K L g) (Module.finrank K L) v = u) ∧
      (∀ u ∈ V, cyclicNorm (σR K L g) (Module.finrank K L) u = 1 →
        ∃ v ∈ V, cyclicDiff (σR K L g) v = u)

theorem local_unit_quotient (g : Gal(L/K)) (hgen : Subgroup.zpowers g = ⊤) :
    Finite (H0 (σR K L g) (Module.finrank K L)) ∧
    Finite (H1 (σR K L g) (Module.finrank K L)) ∧
    cyclicHerbrandQuotient (σR K L g) (Module.finrank K L) = 1

theorem local_field_quotient (g : Gal(L/K)) (hgen : Subgroup.zpowers g = ⊤) :
    Finite (H1 (σL K L g) (Module.finrank K L)) ∧
    cyclicHerbrandQuotient (σL K L g) (Module.finrank K L) =
      (Module.finrank K L : ℚ)

end Local

end
end Anabelian.Pass95Design
```

<!-- pass95-signatures-end -->

For the first P94 instance, apply `finite_acyclic_kernel_reduction` to
`1 → V 0 → Rˣ → Rˣ/(V 0) → 1`, with `(f,g) = (cyclicDiff, cyclicNorm)`.
Restriction/projection compatibility and P94 naturality give all four
intertwinings. The two subsingleton instances come from the lifting step, and
the quotient is finite. The reduction **derives** both `Finite H0(Rˣ)` and
`Finite H1(Rˣ)` before multiplicativity, and gives `q(Rˣ) = 1`.

For the second P94 instance, apply `finite_H1_fractionField` with `integerAut`,
the field automorphism, and the just-derived `Finite H1(Rˣ)`. The valuation
argument of section 4 supplies `Finite H1(Lˣ)`; it does not assume Hilbert 90.
Value-group `H1` finiteness is already proved as
`finite_herbrandH_norm_diff_int`. `generator_period` supplies `n ≠ 0` and
periodicity. Finally P94 gives `q(Lˣ) = q(Rˣ)*n = [L:K]`.

Thus the two finiteness inputs remain explicit in the existing **abstract** P94
theorem and are to be discharged in the **local** application. The unit formula,
those discharges, and the field-norm comparison remain unproved at Pass 95.

#### 9. Dependency map, P24–27 applicability, and pass order

The dependency edges are:

```text
DVR + finite residue --> U^m API --> finite Rˣ/U^m --> finite Rˣ/V_0
finite Galois/local-field assembly --> integer action + degree/period
existing field normal basis + integral scaling + module-finite sandwich
  --> small B --> subgroups V_i + cofinality + stability
local-field IsAdicComplete transport + cofinality/closedness
  --> completeness and separation of V_i
normal-basis coordinates --> equivariant regular layers
regular cyclic exactness + two-map lifting + completeness/separation
  --> both H(V_0) subsingleton
both H(V_0) subsingleton + finite Rˣ/V_0 + P95 conditional reduction
  --> finite H0(Rˣ), finite H1(Rˣ), q(Rˣ)=1
finite H1(Rˣ) + P93/P94 valuation SES + n != 0 --> finite H1(Lˣ)+P94 + degree/period + both H1 instances + q(Rˣ)=1 --> q(Lˣ)=[L:K]
generator enumeration + automorphism-product norm --> cyclic norm = field norm
```

P24–27 filter **ramification groups**, not `Rˣ`. Their precise uses here are:

- `smul_mem_maximalIdeal_pow` (Ramification/Filtration) preserves ideal powers
  under decomposition actions. `smulUnit` (TameCharacter) supplies the existing
  unit action; `tameUnit_spec` gives the factor in `sπ = π*c`.
- P27's `residue_one_add_pow_mul` and coefficient calculations are reusable
  positive-depth algebra. They do not constitute the higher unit filtration.
- P25's `tameQuotientHom_injective` and P27's
  `additiveQuotientHom_injective` concern `G₀/G₁` and `G_i/G_(i+1)`. Their
  monogenicity hypotheses do not prove finite unit quotients or the limit step.
  P26 supplies a ramification exhibit. No monogenicity assumption is imported
  into this unit route. Finite residue and `Ideal.finite_quotient_pow` give the
  finite-index input; local-field adic completeness gives the limit input.

Proposed implementation order (pass boundaries may split if a proof is larger
than expected; the dependencies and theorem statements above fix the content):

| Pass | Concrete deliverable | Inputs |
|---|---|---|
| **P96** | Generic restriction, quotient and layer actions; `regularShift` and `regular_cyclic_exact`; `layer_of_surjective`, `ker_eq_range_of_filtration`, its cyclic corollary, and `herbrandH_subsingleton_of_exact` | P87–P94 algebra; no fields |
| **P97** | `unitFiltration`, membership/zero/antitone/separated/stable API, both finite quotient results, residue equivalence, and `unitCoeff` with specification, exactness, and twisted action | Abstract DVR; finite residue where displayed; P96 actions |
| **P98** | `integerAut`, carrier compatibility, `generator_period`, `isAdicComplete_extensionIntegers`; both field-norm comparison forms | Existing local-field assembly, normal finite-Galois APIs; P94 |
| **P99** | `exists_small_normal_lattice`: integral scaling of the existing normal basis, finite-module sandwich, smallness, product bound, and openness | Existing field normal basis; module-finiteness; P98 action |
| **P100** | `exists_lattice_unit_groups` and `lattice_unit_groups_properties`, including inversion, stability, cofinality, separation, and the explicit limit property | P97, P98 adic transport, P99 |
| **P101** | `lattice_unit_layer_regular`; apply P96 lifting twice to obtain `exists_cohomologicallyTrivial_units` | P96 exactness, P99 basis, P100 filtration |
| **P102** | `local_unit_quotient`; `finite_H1_fractionField`; `local_field_quotient` | P95 reduction, P97 finite index, P101 acyclicity, P93/P94 valuation SES |

The P98 norm comparison is independent of the lattice/limit arc and can be moved
without changing dependencies. No new field-normal-basis theorem is scheduled.
After this arc, `Rep`, Hilbert-90 packaging, unramified cohomology, class formation,
and reciprocity remain separate work. R1–R3 and Hasse–Arf are untouched.

#### 10. Checked inventory and reproducible validation

The pinned Mathlib and project source, rather than guessed names, supply:

| Input | Checked declaration and source |
|---|---|
| Field normal basis | `IsGalois.normalBasis`, `IsGalois.normalBasis_apply`, `Mathlib/FieldTheory/Galois/NormalBasis.lean:121–128` |
| Galois norm | `Algebra.norm_eq_prod_automorphisms`, `Mathlib/RingTheory/Norm/Transitivity.lean:272` |
| Generator enumeration | `IsCyclic.exists_generator`, `orderOf_eq_card_of_zpowers_eq_top`, `pow_orderOf_eq_one`, `finEquivPowers`, `IsGalois.card_aut_eq_finrank` |
| Finite ring quotients | `Ideal.finite_quotient_pow`, `Mathlib/RingTheory/Ideal/Quotient/Index.lean:101`; `IsLocalRing.surjective_units_map_of_local_ringHom` |
| Existing depth-one units | `ValuationSubring.principalUnitGroup`, `principalUnitGroupEquiv`, `unitsModPrincipalUnitsEquivResidueFieldUnits`, `Mathlib/RingTheory/Valuation/ValuationSubring.lean:634–744` |
| Induced actions | `MulEquiv.subgroupMap`, `MulEquiv.subgroupCongr`, `QuotientGroup.congr`, `MulEquiv.arrowCongr`, `Equiv.mulLeft` |
| Integral finite generation | `IsIntegralClosure.finite`; project use in `Anabelian/Extension/ResidueFinite.lean:49` |
| Separation and completion | `Ideal.iInf_pow_eq_bot_of_isLocalRing`, `IsPrecomplete.prec`, and the `IsAdicComplete 𝓂[L] 𝒪[L]` instance in `Mathlib/NumberTheory/LocalField/Basic.lean:176` |
| Local-field transport | `isNonarchimedeanLocalField_extension`, `valued_integer_extensionValuativeRel`, the existing DVR/fraction-field instances and `finite_residueField_extensionIntegers` |
| Galois stability and action | `decompositionSubgroup_extensionIntegers_eq_top`, `MulSemiringAction.toRingEquiv`; the P24–27 names listed in section 9 |
| Conditional reduction | `snake_exact_mid`, `herbrandHMap`, `herbrandQuotient_mul`, `herbrandQuotient_eq_one_of_finite`, `MonoidHom.ker_eq_bot_iff`, `Finite.of_injective`, `Nat.card_eq_one_iff_unique` |
| Remaining finiteness bridge | `dvrUnitsValuation_cyclicNorm`, `multiplicative_int_pow_eq_one`, `dvrUnitsValuation_ker`, `dvrUnitsInclusion_injective`, `cyclicHerbrandQuotient_units` |

**New proof targets, not ledger axioms:** the higher unit-filtration/coefficient
API, small normal-lattice construction and its unit subgroups, regular-action
exactness in this project's cyclic-pair interface, complete-filtration lifting,
adic transport to the project's integer carrier, the two local synthesis
theorems, and the `cyclicNorm`/field-norm adapter. Source searches found no existing
implementations of those combined interfaces. Mathlib does have principal units
at depth one, a field normal basis, and `MulEquiv.arrowCongr`; none is missing.
There is no reliance on a guessed `Units.map_surjective` name: use the checked
local-ring unit-surjectivity lemma where applicable.

The final catalogue was re-extracted from this NOTES entry and elaborated with
`lake env lean` from the project root: **45 declarations, 36 expected temporary
placeholder warnings, zero errors**. A separate **47-command** inventory probe
(`#check`/`#synth`, including the local adic-instance path) passed without warnings.
All probes live under ignored `.lake/`; no placeholder is committed in Lean code.
To reproduce the catalogue check from this entry alone, run:

```sh
python3 - <<'PY'
from pathlib import Path
import re
s = Path('NOTES.md').read_text()
s = s.split('<!-- pass95-signatures-begin -->', 1)[1]
s = s.split('<!-- pass95-signatures-end -->', 1)[0]
chunks = []
for block in re.findall(r'```lean\n(.*?)```', s, re.S):
    for chunk in re.split(r'\n\n+', block.strip()):
        theorem = re.search(r'^theorem ', chunk, re.M)
        missing_def = re.search(r'^def ', chunk, re.M) and ' :=\n' not in chunk
        if theorem or missing_def:
            chunk += ' := by sorry'
        chunks.append(chunk)
Path('.lake/Pass95NotesProbe.lean').write_text('\n\n'.join(chunks) + '\n')
PY
lake env lean .lake/Pass95NotesProbe.lean
```

The proved module passes its direct Lean check and standard-only audit.
`lake build`: **8570 jobs, zero warnings/errors**. `scripts/preflight.sh`:
**CLEAN**, including the **94-file** import-chain check. All **452** build audit
outputs use only the three standard axioms. Source scan: zero project axiom
declarations and zero proof holes. `git diff --check` passes.

README, ROADMAP's current frontier, HANDOFF for P96, and the ledger agree on
Pass 95, 94 files, and 0/0. HANDOFF restores the operational note that
`Quotient/LiftDvd.lean` can take approximately 15 minutes to elaborate on rebuild.
Earlier NOTES and ledger content, including the verbatim Pass-93 archives and
their pointers, is preserved. The constitutional file needs no status edit.


<a id="pass-96"></a>

### Pass 96 (2026-09-26) — the generic layer: stable actions, the regular module, and filtration lifting

**Ledger delta: 0 / 0; active count: 0 FOUNDATIONAL / 0 DEBT.** Three new files under
`Anabelian/ClassField/`, all pure group theory (no field, no valuation), implementing the
field-free part of the Pass-95 design (NOTES Pass 95 §3 and the P96 row). The project has
97 source files under `Anabelian/`. Everything proved; no `sorry`, no `axiom`; every audit
standard-only. No new `structure`/`class`; every hypothesis is carried, none is claimed
load-bearing; no owed witness; D1/D2 N/A. R1–R3 untouched.

#### What was proved

**`ClassField/StableAction.lean`** — for a commutative group `M`, `σ : MulAut M`, and a
`σ`-stable subgroup `S` (`h : S.map σ.toMonoidHom = S`):

```lean
theorem apply_mem_iff_of_map_eq (σ) (S) (h) (x : M) : σ x ∈ S ↔ x ∈ S
theorem pow_apply_mem_of_map_eq (σ) (S) (h) (j : ℕ) (hx : x ∈ S) : (σ ^ j) x ∈ S
theorem cyclicNorm_mem_of_map_eq (σ) (S) (h) (n) (hx : x ∈ S) : cyclicNorm σ n x ∈ S
theorem cyclicDiff_mem_of_map_eq (σ) (S) (h) (hx : x ∈ S) : cyclicDiff σ x ∈ S
def restrictAut (σ) (S) (h) : MulAut S := (σ.subgroupMap S).trans (MulEquiv.subgroupCongr h)
theorem restrictAut_coe (σ) (S) (h) (x : S) : (restrictAut σ S h x : M) = σ x        -- rfl
def quotientAut (σ) (S) (h) : MulAut (M ⧸ S) := QuotientGroup.congr S S σ h
theorem quotientAut_mk (σ) (S) (h) (x : M) :
    quotientAut σ S h (QuotientGroup.mk' S x) = QuotientGroup.mk' S (σ x)
abbrev Layer (F : ℕ → Subgroup M) (i : ℕ) := (F i) ⧸ ((F (i + 1)).subgroupOf (F i))
theorem subgroupOf_map_restrictAut (σ) (F) (hF : ∀ i, (F i).map σ.toMonoidHom = F i) (i) :
    ((F (i+1)).subgroupOf (F i)).map (restrictAut σ (F i) (hF i)).toMonoidHom
      = (F (i+1)).subgroupOf (F i)
def layerAut (σ) (F) (hF) (i) : MulAut (Layer F i)     -- quotientAut of restrictAut
theorem layerAut_mk (σ) (F) (hF) (i) (x : F i) :
    layerAut σ F hF i (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ (restrictAut σ (F i) (hF i) x)
-- naturality of the cyclic pair (Pass 94's map_cyclicNorm/map_cyclicDiff at the three maps)
theorem cyclicNorm_restrictAut_coe : ((cyclicNorm (restrictAut σ S h) n x : S) : M) = cyclicNorm σ n x
theorem cyclicDiff_restrictAut_coe : ((cyclicDiff (restrictAut σ S h) x : S) : M) = cyclicDiff σ x
theorem cyclicNorm_quotientAut_mk :
    cyclicNorm (quotientAut σ S h) n (mk' S x) = mk' S (cyclicNorm σ n x)
theorem cyclicDiff_quotientAut_mk : cyclicDiff (quotientAut σ S h) (mk' S x) = mk' S (cyclicDiff σ x)
theorem cyclicNorm_layerAut_mk :
    cyclicNorm (layerAut σ F hF i) n (mk' _ x) = mk' _ (cyclicNorm (restrictAut σ (F i) (hF i)) n x)
theorem cyclicDiff_layerAut_mk :
    cyclicDiff (layerAut σ F hF i) (mk' _ x) = mk' _ (cyclicDiff (restrictAut σ (F i) (hF i)) x)
theorem herbrandH_subsingleton_of_exact (f g : M →* M) (h : g.range = f.ker) :
    Subsingleton (herbrandH f g)
```

**`ClassField/FiltrationLifting.lean`** — the dévissage brick:

```lean
theorem ker_eq_range_of_filtration (f g : M →* M) (hfg : ∀ x, f (g x) = 1)
    (F : ℕ → Subgroup M) (hF0 : F 0 = ⊤)
    (hstab : ∀ i, ∀ x ∈ F i, g x ∈ F i)
    (hlayer : ∀ i, ∀ x ∈ F i, f x ∈ F (i + 1) → ∃ y ∈ F i, x * (g y)⁻¹ ∈ F (i + 1))
    (hsep : ∀ x, (∀ i, x ∈ F i) → x = 1)
    (hcomplete : ∀ z : ℕ → M, (∀ i, z (i + 1) * (z i)⁻¹ ∈ F i) →
      ∃ y, ∀ i, y * (z i)⁻¹ ∈ F i) :
    f.ker = g.range
theorem layer_of_surjective {W} [CommGroup W] (f g : M →* M) (S T : Subgroup M)
    (hfS : ∀ x ∈ S, f x ∈ S) (hgS : ∀ x ∈ S, g x ∈ S)
    (θ : S →* W) (hθ : Function.Surjective θ) (hker : ∀ x : S, θ x = 1 ↔ (x : M) ∈ T)
    (fW gW : W →* W)
    (hfθ : ∀ x : S, θ ⟨f x, hfS x x.property⟩ = fW (θ x))
    (hgθ : ∀ x : S, θ ⟨g x, hgS x x.property⟩ = gW (θ x))
    (hW : fW.ker ≤ gW.range) :
    ∀ x ∈ S, f x ∈ T → ∃ y ∈ S, x * (g y)⁻¹ ∈ T
theorem cyclic_exact_of_complete_filtration (σ : MulAut M) (n : ℕ) (hσ : σ ^ n = 1)
    (F : ℕ → Subgroup M) (hF : ∀ i, (F i).map σ.toMonoidHom = F i)
    (hzero : F 0 = ⊤) (hsep : (⨅ i, F i) = ⊥)
    (hcomplete : ∀ u : ℕ → M, (∀ i, u (i + 1) * (u i)⁻¹ ∈ F i) → ∃ x : M, ∀ i, x * (u i)⁻¹ ∈ F i)
    (hlayer : ∀ i,
      (cyclicNorm (layerAut σ F hF i) n).range = (cyclicDiff (layerAut σ F hF i)).ker ∧
      (cyclicDiff (layerAut σ F hF i)).range = (cyclicNorm (layerAut σ F hF i) n).ker) :
    (cyclicNorm σ n).range = (cyclicDiff σ).ker ∧ (cyclicDiff σ).range = (cyclicNorm σ n).ker
```

**`ClassField/RegularModule.lean`** — the acyclic layer module:

```lean
def regularShift (g : G) : MulAut (G → C) := MulEquiv.arrowCongr (Equiv.mulLeft g) (MulEquiv.refl C)
theorem regularShift_apply (g) (f : G → C) (h : G) : regularShift g f h = f (g⁻¹ * h)   -- rfl
theorem regularShift_pow_apply (g) (j : ℕ) (f) (h) : (regularShift g ^ j) f h = f ((g ^ j)⁻¹ * h)
theorem prod_range_card_pow [Fintype G] (g) (hgen : Subgroup.zpowers g = ⊤) (φ : G → C) :
    ∏ j ∈ Finset.range (Nat.card G), φ (g ^ j) = ∏ k, φ k
theorem cyclicNorm_regularShift_apply [Fintype G] (g) (hgen) (f : G → C) (h : G) :
    cyclicNorm (regularShift g) (Nat.card G) f h = ∏ k, f k
theorem regular_cyclic_exact [Finite G] (g : G) (hgen : Subgroup.zpowers g = ⊤) :
    (cyclicNorm (regularShift (C := C) g) (Nat.card G)).range = (cyclicDiff (regularShift g)).ker ∧
    (cyclicDiff (regularShift (C := C) g)).range = (cyclicNorm (regularShift g) (Nat.card G)).ker
```

#### Deviations from the Pass-95 catalogue (all strengthenings)

- `cyclic_exact_of_complete_filtration` carries **no** `Antitone F` hypothesis: the proof
  never uses it (`Layer` is stated with `subgroupOf`, and the lifting only needs
  `F 0 = ⊤`, stability, layer exactness, separation, completeness). The catalogue's
  statement is the instance with the unused hypothesis.
- `prod_range_card_pow` and `cyclicNorm_regularShift_apply` take `[Fintype G]` (they
  mention `∏ k, φ k`); `regular_cyclic_exact` keeps the catalogue's `[Finite G]` and
  installs `Fintype.ofFinite` inside its proof.
- The four intertwining lemmas `cyclicNorm_restrictAut_coe`/`cyclicDiff_restrictAut_coe`/
  `cyclicNorm_quotientAut_mk`/`cyclicDiff_quotientAut_mk` (plus the `layerAut` versions)
  are added as named statements; the catalogue left them implicit ("P94 naturality").
  They are exactly the four hypotheses of `herbrandQuotient_mul` /
  `finite_acyclic_kernel_reduction` for the sequence `1 → V₀ → Rˣ → Rˣ/V₀ → 1` in P102.
- The two helper membership lemmas `cyclicNorm_mem_of_map_eq`/`cyclicDiff_mem_of_map_eq`
  (and `apply_mem_iff_of_map_eq`, `pow_apply_mem_of_map_eq`, `subgroupOf_map_restrictAut`)
  are new bricks needed to state and prove `layerAut` and the stability hypothesis of the
  lifting lemma.

#### Proof routes and the Mathlib API that did the work

- **`ker_eq_range_of_filtration`** (successive approximation, ~50 lines): `⊇` is P87's
  `range_le_ker`. For `⊆`, given `x ∈ ker f`: package the layer correction as a total
  function `corr : ℕ → M → M` via a `dite` on `x ∈ F i ∧ f x = 1` with `Classical.choose`
  (so the recursion below is on plain `M`, not on a dependent type); define the approximants
  `xs 0 = x`, `xs (i+1) = xs i · (g (corr i (xs i)))⁻¹` and the partial products
  `zs 0 = 1`, `zs (i+1) = corr i (xs i) · zs i` by `Nat.rec`, exposed only through their
  two equations (an `obtain ⟨xs, hxs0, hxss⟩ : ∃ xs, …` — no `let`-unfolding friction).
  Invariants by induction: `xs i ∈ F i ∧ f (xs i) = 1` (using `f (g _) = 1`) and
  `xs i = x · (g (zs i))⁻¹` (`map_mul`, `mul_inv_rev`, `mul_assoc`). The `zs` are coherent
  (`zs (i+1) · (zs i)⁻¹ = corr i (xs i) ∈ F i`, `mul_inv_cancel_right`), so `hcomplete`
  gives `y` with `y · (zs i)⁻¹ ∈ F i`; then `x · (g y)⁻¹ = xs i · (g (y · (zs i)⁻¹))⁻¹ ∈ F i`
  for every `i` (`inv_mul_cancel_left`; `g`-stability of `F i`), and `hsep` finishes with
  `mul_inv_eq_one`.
- **`layer_of_surjective`**: `θ ⟨f x, _⟩ = 1` by `hker`, so `θ x ∈ ker fW ≤ im gW`; lift
  the preimage through `hθ` to `y : S`; then `θ (x · ⟨g y, _⟩⁻¹) = 1` (`map_mul`, `map_inv`,
  `hgθ`, `mul_inv_cancel`) and `hker` reads it as `x · (g y)⁻¹ ∈ T` — the subgroup
  coercions are definitional, so `(hker _).mp` closes the goal directly.
- **`cyclic_exact_of_complete_filtration`**: the general lemma twice, with
  `(f, g) = (cyclicDiff σ, cyclicNorm σ n)` and swapped; `hfg` are P91's
  `cyclicDiff_cyclicNorm`/`cyclicNorm_cyclicDiff` (this is where `σ ^ n = 1` enters);
  `hstab` from the membership lemmas; `hlayer` from `layer_of_surjective` at
  `θ := QuotientGroup.mk' ((F (i+1)).subgroupOf (F i))` (`QuotientGroup.mk'_surjective`,
  `QuotientGroup.eq_one_iff` + `Subgroup.mem_subgroupOf` for the kernel, the
  `layerAut_mk`-naturality lemmas for equivariance, `(hlayer i).1.symm.le` /
  `(hlayer i).2.symm.le` for `ker fW ≤ im gW`); `hsep` from `Subgroup.mem_iInf` +
  `Subgroup.mem_bot`.
- **`restrictAut`/`quotientAut`/`layerAut`**: Mathlib's `MulEquiv.subgroupMap`,
  `MulEquiv.subgroupCongr` (both coercions `rfl`: `coe_subgroupMap_apply`,
  `subgroupCongr_apply`), `QuotientGroup.congr` with `QuotientGroup.congr_mk'`. The
  stability of `(F (i+1)).subgroupOf (F i)` under `restrictAut` is a two-line `ext`
  through `Subgroup.mem_map`/`mem_subgroupOf` and `apply_mem_iff_of_map_eq`
  (`MulEquiv.injective` for the forward direction; the inverse image
  `(restrictAut …).symm y` for the backward one).
- **`herbrandH_subsingleton_of_exact`**: two `QuotientGroup.induction_on`,
  `QuotientGroup.eq`, `Subgroup.mem_subgroupOf`, then rewrite `g.range = f.ker` and use
  the subtype property of `a⁻¹ * b`.
- **`regular_cyclic_exact`** (~90 lines, the only computation): `regularShift` is
  `MulEquiv.arrowCongr (Equiv.mulLeft g) (MulEquiv.refl C)` — its application and power
  formulas are `rfl` and a `pow_succ'`/`MulAut.mul_apply`/`mul_inv_rev` induction. The norm
  is the constant function `∏_{k ∈ G} f k` (`cyclicNorm_apply`, `Finset.prod_apply`, and
  the enumeration `j ↦ g ^ j` of `G` by exponents `< |G|`: `Finset.prod_nbij` with
  `pow_injOn_Iio_orderOf` for injectivity — after `orderOf g = Nat.card G` from
  `orderOf_eq_card_of_zpowers_eq_top` — and `IsOfFinOrder.mem_powers_iff_mem_zpowers` +
  `Submonoid.mem_powers_iff` + `pow_mod_orderOf` for surjectivity; then
  `Fintype.prod_equiv ((Equiv.inv G).trans (Equiv.mulRight h))`). Four inclusions:
  norms are constant hence fixed (`mul_inv_cancel`); a fixed `f` is constant (`f (g ^ i) =
  f 1` by induction from `f (g⁻¹ h) = f h`, then `f k = f (g ^ idx k)`), and a constant `c`
  is the norm of `Pi.mulSingle 1 c` (`Finset.prod_pi_mulSingle'`); differences have trivial
  norm (`Finset.prod_mul_distrib`, `prod_inv_distrib`, reindex by `Equiv.mulLeft g⁻¹`); and
  a function of trivial norm is the difference of `y k := ∏_{j ∈ Ico (idx k + 1) |G|} f (g ^ j)`
  where `idx : G → ℕ` (from `choose` on the enumeration) is the unique exponent `< |G|` —
  the telescoping step is `Finset.prod_eq_prod_Ico_succ_bot`, and the wrap-around at
  `idx h = 0` (`h = 1`, `g⁻¹ = g ^ (|G| − 1)` from `pow_card_eq_one'`) uses
  `∏_{k} f k = 1` read as `f 1 · ∏_{Ico 1 |G|} f (g ^ j) = 1` (`Finset.range_eq_Ico`).
  No division by `|G|` anywhere.

#### House notes (this pass)

- `rw [lemma]` vs `rw [← lemma]` for the naturality equations: the goal produced by
  `layer_of_surjective` is `mk' ⟨f x, _⟩ = fW (mk' x)`; rewrite the **right** side forward
  with `cyclicDiff_layerAut_mk`, then `exact congrArg _ (Subtype.ext …)`. For `cyclicDiff`
  the two sides are already definitionally equal after the rewrite (`congr 1` closes the goal
  and a following `exact` errors with "no goals"); `congrArg _ (Subtype.ext _)` is uniform
  across the `Diff`/`Norm` cases.
- Recursively defined sequences inside a proof: `obtain ⟨xs, h0, hsucc⟩ : ∃ xs : ℕ → M,
  xs 0 = x ∧ ∀ i, xs (i+1) = … := ⟨fun i => Nat.rec x (fun j xj => …) i, rfl, fun _ => rfl⟩`
  gives clean equations and avoids `let` zeta-unfolding issues.
- `Finset.prod_nbij` (not `prod_bij`) is the right tool when the reindexing is a plain
  function with `Set.InjOn`/`Set.SurjOn` on the coerced finsets (`Finset.coe_range`).
- `Finset.prod_apply` evaluates a `Finset` product of functions pointwise; with
  `simp only [regularShift_pow_apply]` afterwards the norm becomes an honest product.

#### Verification and governance

`lake build`: success, zero warnings/errors (job count in the ledger entry).
`scripts/preflight.sh`: CLEAN, including the 97-file import-chain check. All audits
standard-only; the new ones (StableAction: 11 lines, FiltrationLifting: 3, RegularModule: 5)
are reproduced in the source audit blocks. README, ROADMAP, HANDOFF, and the ledger move to
Pass 96 (97 files, 0/0, next = P97 the abstract `unitFiltration` API). Historical NOTES and
ledger entries untouched.

**Honest scope.** Nothing here touches a field, a valuation, or a local field; the
arithmetic inputs of the Pass-95 design (the lattice, its unit subgroups, adic completeness,
finite index, the normal basis) are Passes 97–101. What is now true: *if* those inputs are
supplied for `V₀ ≤ 𝒪_Lˣ` with regular layers, then `cyclic_exact_of_complete_filtration`
+ `regular_cyclic_exact` + `herbrandH_subsingleton_of_exact` give the two `Subsingleton`
instances that `finite_acyclic_kernel_reduction` consumes. No Hilbert 90, no reciprocity;
R1–R3 untouched.

<a id="pass-97"></a>

### Pass 97 (2026-10-08) — governance: the Mathlib bump `v4.30.0` → `0653561` (Lean `v4.35.0-rc2`)

**Ledger delta: 0 / 0; active count: 0 FOUNDATIONAL / 0 DEBT.** A governance pass in the
sense of Pass 42: no new mathematics, no new file, no statement weakened. The project moves
from Mathlib `v4.30.0` (Lean `v4.30.0`) to Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` (Lean `v4.35.0-rc2`); `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` carry the pin. Branch `mathlib-bump`, not merged to
`master` in this pass. 97 project files; `lake build` 9029 jobs, zero warnings;
`scripts/preflight.sh` CLEAN; every `#print axioms` across all 97 files standard-only
(`propext` / `Classical.choice` / `Quot.sound`, or a subset). No `sorry`, no `axiom`, no
`native_decide`, no heartbeat change, and **no `backward.isDefEq.respectTransparency`
override anywhere** (the last resort was never needed).

#### Statement audit (the only statement-text change)

**`Anabelian/Quotient/RamificationIdx.lean`, `ramificationIdx_comapRingHom`.** Mathlib renamed
the two-ideal ramification index: the old `Ideal.ramificationIdx p P := sSup {n | map f p ≤ P ^ n}`
is now `Ideal.ramificationIdx' p P` (same body, verified against the `v4.30.0` source), and the
name `Ideal.ramificationIdx` now denotes a *new* definition `q.ramificationIdx R` (a module
length in the localization, `Mathlib/RingTheory/RamificationInertia/Ramification.lean`). The
theorem's statement is therefore spelled `Ideal.ramificationIdx'` — the same mathematical
statement under the constant's new name, not a weakening (pattern 3 of the bump: a rename with
a reused name). Every other theorem/def statement and hypothesis in the project is textually
unchanged; all changes below are inside proofs or imports.

#### Patterns, with the files they touched

1. **`IsGalois K (AlgebraicClosure K)` no longer reachable transitively** from `[PerfectField K]`
   / `[Finite K]`: the instance chain lives in `Mathlib.FieldTheory.IsSepClosed`. Fix: import it
   (`Galois/Basic`, `FiniteField/Basic`, `Reduction/Invariant`). Same species: `Invariant` also
   needed `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` (for
   `IsIntegrallyClosed.isIntegral_iff`) and `Mathlib.RingTheory.Valuation.Integral` (the
   instance `Valuation.Integers.isIntegrallyClosed_integers`, which is what gives
   `IsIntegrallyClosed 𝒪[K]`; located with a traced `#synth`).
2. **Concrete-category / `rw`-motive strictness.** `rw`/`simp` now refuse goals that are not
   type-correct at `implicit` transparency ("not type-correct under the `implicit` transparency
   level"). This bit wherever a `def` wrapping a quotient or a bundled carrier had been unfolded
   by an earlier tactic: `FiniteField/ZHatIso` (`GrpCat.of` carrier under `etaFn`),
   `Reduction/GaloisInertia` (`residueReductionHom` unfolded, `ResidueField` vs
   `B ⧸ maximalIdeal B`), `Reduction/ResidueIso` (same quotient/`ResidueField` mismatch),
   `ClassField/Multiplicativity` (three `rw [MonoidHom.mem_ker] at hc` after
   `QuotientGroup.induction_on`, `herbrandH` vs the raw quotient), and the two `calc` blocks in
   `ClassField/Snake` and `ClassField/TrivialAction` (`Trans Eq Eq ?m` unresolved because the
   quotient target was elaborated at the raw type). Fix in every case: apply the lemma as a term
   (`exact (lemma …).trans …`, `MonoidHom.mem_ker.mp hc`, `(galoisResidueAut K).map_eq_one_iff`,
   `Iff.trans AddSubgroup.mem_inertia AddSubgroup.mem_inertia.symm`) or state the unfolded goal
   with `change` and then `rw`. The `set_option backward.isDefEq.respectTransparency false`
   escape hatch was not used.
3. **Renames with reused names / shifted conventions.** `Equiv.setCongr` → `Set.equivOfEq`
   (`FiniteField/Level`, already fixed on the branch); TFAE indices start at 1 —
   `IsBezout.TFAE … .out 0 1` → `.out 1 2` (`Extension/Uniformizer`),
   `local_hom_TFAE … .out 4 0` → `.out 5 1` (`Reduction/ResidueIso`);
   `Ideal.ramificationIdx`/`ramificationIdx_spec` → `ramificationIdx'`/`ramificationIdx'_spec`
   (`Quotient/RamificationIdx`, see the statement audit).
4. **Signature changes.** `isIntegral_algebraMap_iff` takes `[FaithfulSMul A B]` instead of an
   explicit injectivity proof — call it as `(isIntegral_algebraMap_iff (B := _)).mp`
   (`Extension/Uniformizer`, `LocalField/Canonical`, `Quotient/ComapIntegers`,
   `Reduction/Invariant`). `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` now takes the ring
   hom and its integrality first (`Reduction/ResidueIso`). `multiplicity_self` now takes a
   `FiniteMultiplicity a a` witness — supplied via `FiniteMultiplicity.of_not_isUnit` with
   `Ideal.isUnit_iff`/`Ideal.span_singleton_eq_top`/`Ideal.span_singleton_eq_bot`
   (`ClassField/UnitsValuation`). `MonoidHom.restrict` → `MonoidHom.domRestrict`, with
   `restrict_range`/`ker_restrict` → `domRestrict_range`/`ker_domRestrict`
   (`Quotient/CardMultiplicativity`).
   `Ideal.card_inertia_eq_ramificationIdxIn` dropped its `p ≠ ⊥` argument and now asks for
   `[Module.Flat R S]` (from `IsDedekindDomain` + `Module.IsTorsionFree`, both already supplied
   by `Quotient/InertiaSetup`) and `[Algebra.HasSeparableResidueFieldsAt R S p]` (Mathlib's
   instance from `[Algebra.IsIntegral R S]` + `[PerfectField p.ResidueField]`); `InertiaCard`
   now proves `Finite p.ResidueField` locally (the residue field of `B` embeds in the finite
   residue field of `𝒪_L`; Mathlib's `[Finite (R ⧸ I)] → Finite I.ResidueField` instance), from
   which `PerfectField.ofFinite` closes it, and bridges the two ramification indices with
   `Ideal.ramificationIdx'_eq_ramificationIdx _ _ hbot`.
5. **New Mathlib instances replacing hand-rolled structure.** `Extension/ResidueFinite`: Mathlib
   now provides `Algebra (ResidueField R) (ResidueField S)` and the `IsScalarTower` instances
   from `[Algebra R S] [IsLocalHom (algebraMap R S)]`; the hand-rolled `letI` algebra
   structures no longer unify with them (an `IsScalarTower` goal failed to synthesize against the
   local `letI`), so the proof now supplies
   `IsLocalHom (algebraMap 𝒪[K] 𝒪_L) := inferInstanceAs (IsLocalHom (extensionAlgebraMap K L))`
   and lets Mathlib's instances carry the restriction of scalars. `Reduction/ResidueIso`'s
   algebraicity proof uses `IsLocalRing.residue_surjective` instead of
   `Ideal.Quotient.mk_surjective` so the lifted element is typed at `ResidueField B`.
6. **Deprecations (all switched to the new names, never silenced):** `if_pos`/`if_neg` →
   `ite_eq_left`/`ite_eq_right`, `dif_pos` → `dite_eq_left` (`Ramification/LowerIndexCount`,
   `Herbrand/Function`, `Herbrand/Formula`, `Herbrand/Slope`, `Extension/InertiaResidueCover`,
   `ClassField/RegularModule`, `ClassField/FiltrationLifting`); `ENat.coe_ne_top` →
   `ENat.natCast_ne_top` (`Ramification/LowerIndex`, `LowerIndexCount`, `LowerIndexGenerator`);
   `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` and `mul_le_one₀` (deprecated with no replacement)
   → `(mul_le_of_le_one_left _ hx).trans hy` (`Reduction/SpectralValuation`);
   `Valuation.exists_setOf_restrict_le_iff` → `exists_setOfPred_restrict_le_iff`
   (`LocalField/Instance`).
7. **New linters.** `linter.style.haveILetI`: `haveI`/`letI` whose goal is a `Prop` must be
   `have`/`let` — 164 one-to-one conversions across 35 files (plus a few inside the
   restructured `ResidueFinite` proof), converted exactly at the flagged lines by a script keyed
   on the build log; nothing was converted that the linter did not flag.
   `linter.unusedTactic`: a no-op `change` removed (`Herbrand/Transitivity`). The `show`-style
   linter: `show` used as a goal change must be `change` (`ClassField/Snake`,
   `ClassField/TrivialAction`). `simpa` normal form drifted in `Herbrand/UpperNumbering`
   (`u / g 0` vs `u * (g 0)⁻¹`): replaced by an explicit
   `rw [integral_const, sub_zero, smul_eq_mul, mul_one_div] at h; exact h`.

#### Per-file changes

Already fixed on the branch before this pass: `Galois/Basic` (import), `FiniteField/Basic`
(import), `FiniteField/ZHat` (term-mode `zhatToGalois_etaFn`), `FiniteField/Level`
(`Set.equivOfEq`). This pass:

- `haveI`/`letI` → `have`/`let` only (23 files): `Absolute/{Main,Surjectivity,Tower}`,
  `ClassField/{FiniteAcyclic,UnitsValuationEquivariance}`,
  `Extension/{Integers,Monogenic,MonogenicDischarge,WildTame}`, `ForMathlib/ValuativeRelCongr`,
  `Galois/RationalsNonAbelian`, `LocalField/{SpectralSeam,ValuativeRel,Valued}`,
  `Quotient/{IndexProfile,InertiaSetup,LemmaFive,NumericalLemmaFive}`,
  `Reduction/{Continuity,GaloisIntegersLocal,RamificationDegeneracy,ResidueAlgClosed,
  UnramifiedQuotient}`, plus the same edits inside `FiniteField/{Basic,Level,ZHatIso}`,
  `Extension/{InertiaResidueCover,ResidueFinite,Uniformizer}`, `LocalField/{Canonical,Instance}`,
  `Quotient/InertiaCard`, `Reduction/{GaloisInertia,ResidueIso}`, `ClassField/{RegularModule,
  TrivialAction}`.
- Substantive proof edits (statements unchanged): `FiniteField/ZHatIso` (pattern 2),
  `Reduction/Invariant` (patterns 1, 4), `Extension/Uniformizer` (patterns 3, 4),
  `Reduction/ResidueIso` (patterns 2, 3, 4, 5), `Extension/ResidueFinite` (pattern 5),
  `Reduction/SpectralValuation` (pattern 6), `Herbrand/UpperNumbering` (pattern 7),
  `Reduction/GaloisInertia` (pattern 2; `Ideal.ker_stabilizerHom` now lands in
  `P.inertia (stabilizer G P)` rather than a `subgroupOf`, hence the double `mem_inertia`),
  `LocalField/Canonical` and `Quotient/ComapIntegers` (pattern 4), `Quotient/InertiaCard`
  (pattern 4), `Quotient/CardMultiplicativity` (pattern 4), `ClassField/{Snake,TrivialAction,
  Multiplicativity}` (pattern 2), `ClassField/UnitsValuation` (pattern 4),
  `Herbrand/Transitivity` (pattern 7), and the pattern-6 renames listed above.
- Statement text changed (constant renamed, content identical): `Quotient/RamificationIdx`.

#### Verification and governance

`lake build`: 9029 jobs, zero warnings/errors. `scripts/preflight.sh`: CLEAN (clause 0 required
tracking the two non-ignored `.parley/` session records, `participants.json` and `log.jsonl`,
which the branch's `.gitignore` edit deliberately left unignored). Per-file
`lake env lean <file> | grep "depends on axioms"` over all 97 files: standard-only everywhere.
README/ROADMAP/HANDOFF move to Pass 97; the next mathematical pass is **Pass 98**, which
implements the Pass-95 design's *P97 row* (the abstract DVR unit filtration) — the design's row
labels P97–P102 are kept as written in the immutable Pass-95 entry and now map to Passes 98–103.

<a id="pass-98"></a>

### Pass 98 (2026-10-08) — the ClassFieldTheory bridge: Hasse–Arf at `𝒪_L`, imported and identified

**Ledger delta: 0 / 0; active count: 0 FOUNDATIONAL / 0 DEBT.** New file
`Anabelian/ClassField/Bridge.lean` (98 project files). Branch `mathlib-bump`, on top of the
prelude commit `38d973b` that added the Lake dependency
`n-yamaguchi-0729/ClassFieldTheory @ 7713795234690681b4406ae198b07aa95e82716a` (Apache 2.0;
author Naganori Yamaguchi, "assisted by OpenAI Codex" per its file headers; its only Lake
dependency is Mathlib, pinned compatibly with ours). `lake build` 10542 jobs, zero warnings;
`scripts/preflight.sh` CLEAN; every `#print axioms` in the new file — ten project
declarations and eight imported headlines — standard-only. No `sorry`, no `axiom`, no
`native_decide`, no heartbeat change, no `backward.isDefEq.respectTransparency` override.

#### What is imported, and what that means for the ledger

The dependency is an **external library whose headline theorems carry no non-standard
axioms**. It is therefore *not* a ledger axiom — the "Active axioms" table stays empty — but
it *is* a boundary the project now takes from outside, of the species `FOUNDATIONAL` was
designed to mark. `AXIOM_LEDGER.md` gains an **"External dependencies"** section listing the
imported theorems the project relies on with their `#print axioms` results, and the caveats
on which of them are existential. The honest reading: **local class field theory (L3.1–L3.3)
and Hasse–Arf are now inputs, not project theorems**; the project has not proved them and
does not claim to. The in-project L3.1 program (the Pass-95 unit-quotient design, rows
P97–P102) is no longer on the critical path to reciprocity — see the HANDOFF decision note.

#### Deliverable 1 — `hasseArf_extension` (and `hasseArf_herbrandPhi`)

The upstream `ClassFieldTheory.hasseArf` takes `[ValuativeRel L] [TopologicalSpace L]
[IsNonarchimedeanLocalField L]` and `[Valuation.HasExtension (valuation K) (valuation L)]`
as *instances on `L`*, and speaks of `(valuation L).valuationSubring`. The project's
convention (Passes 38–43, D2) is that `L` carries no such instances: its valuative structure is
the `def` `extensionValuativeRel K L` (induced by `𝒪_L = extensionIntegers K L`), installed by
`letI` inside proofs only. The bridge:

- `extensionIntegers_comap_algebraMap_eq : (extensionIntegers K L).toSubring.comap (algebraMap
  K L) = 𝒪[K]` — `𝒪_L ∩ K = 𝒪_K`. Proof: `isIntegral_algebraMap_iff` (descent along `K ↪ L`,
  the P97 `FaithfulSMul` form) then `Valuation.Integers.mem_of_integral` (a valuation ring is
  integrally closed in its fraction field) one way, `isIntegral_algebraMap` the other.
- `hasExtension_extensionValuativeRel` — `Valuation.HasExtension.ofComapInteger` applied to
  Pass 43's `integer_extensionValuativeRel_eq` (`𝒪[L] = 𝒪_L` under the rung-1 relation) and
  the lemma above. **This is the discharge the task asked for**: the compatibility is proved
  from Pass 38–43 bricks, not assumed.
- `valuationSubring_extensionValuativeRel_eq : (valuation L).valuationSubring =
  extensionIntegers K L` — the same identity at `ValuationSubring` level, so that the upstream
  statement's `(valuation L).valuationSubring` can be rewritten to `𝒪_L`.
- **`hasseArf_extension`** — statement, verbatim:

  ```lean
  theorem hasseArf_extension [IsAbelianGalois K L] {n : ℕ}
      (hn : ClassFieldTheory.IsLowerRamificationJump K (extensionIntegers K L) n) :
      ∃ z : ℤ,
        ClassFieldTheory.herbrandFunctionAtLowerIndex K (extensionIntegers K L) n = (z : ℚ)
  ```

  with the file's variables `(K) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (L) [Field L] [Algebra K L] [FiniteDimensional K L]`. No
  instance on `L`; `IsAbelianGalois K L` supplies `Algebra.IsSeparable K L` for Pass 41's
  `isNonarchimedeanLocalField_extension`. Proof: four `let`/`have`s install the rung-1 structure,
  topology, local-field instance and `HasExtension`; `rw [← hA]` rewrites `𝒪_L` back to
  `(valuation L).valuationSubring` in `hn` and the goal; `exact ClassFieldTheory.hasseArf K L hn`.
- **`hasseArf_herbrandPhi`** — the same in project vocabulary:

  ```lean
  theorem hasseArf_herbrandPhi [IsAbelianGalois K L] {n : ℕ}
      (hn : ramificationGroup K (extensionIntegers K L) n
        ≠ ramificationGroup K (extensionIntegers K L) (n + 1)) :
      ∃ z : ℤ, herbrandPhi K (extensionIntegers K L) (n : ℝ) = (z : ℝ)
  ```

  via the identification below and `Rat.cast_intCast`.

#### Deliverable 2 — the Herbrand identification (verdict: **they agree**, proved)

| ClassFieldTheory | project | relation | lemma |
|---|---|---|---|
| `lowerRamificationGroup K A n` (carrier `∀ x, σ•x − x ∈ 𝔪^(n+1)`) | `ramificationGroup K A n` (`(𝔪^(n+1)).inertia`) | equal, carriers definitionally the same (`Iff.rfl`) | `lowerRamificationGroup_eq_ramificationGroup` |
| `herbrandFunctionAtLowerIndex K A n : ℚ` = `(∑_{Icc 1 n} |G_i|)/|G_0|` | `herbrandPhi K A n` = `∫₀ⁿ dt/(G_0:G_t)` | equal in `ℝ` (P48 `herbrandPhi_natCast` + `Finset.sum_Ico_add'` reindexing) | `herbrandPhi_natCast_eq` |
| `herbrandFunction K A : ℝ → ℝ` (piecewise linear; `id` on `s < 0`) | `herbrandPhi K A` | **equal as functions** (P48 affine formula on `[⌊s⌋₊, ⌊s⌋₊+1]`; P44 `herbrandPhi_eq_id`) | `herbrandPhi_eq_herbrandFunction` |
| `inverseHerbrandFunction K L t` = `Function.invFun (herbrandFunction K 𝒪)` | `herbrandPsi K A` = `Function.invFun (herbrandPhi K A)` | equal (`rfl` after the previous row) | `herbrandPsi_eq_invFun_herbrandFunction` |
| `realLowerRamificationGroup K A s` (carrier `∈ 𝔪^(⌈s+1⌉.toNat)`) | `ramificationGroup K A ⌈s⌉₊` | equal for `-1 < s`; **differ for `s ≤ -1`** (theirs `⊤` = Serre's `G_{-1}`; ours bottoms at `G_0`) | `realLowerRamificationGroup_eq` |
| `upperRamificationGroup K L t` = real-lower at `inverseHerbrandFunction t` | `upperRamificationGroup K A v` = `G_{⌈ψ v⌉₊}` | agree for `-1 < t` by the two rows above, **modulo transport** across `valuationSubring_extensionValuativeRel_eq` (different-but-equal `ValuationSubring`s, hence different decomposition-group types) — not performed | *next pass* |

The one genuine convention difference is the negative half-line (`G_{-1} = ⊤` vs ℕ-truncation);
it affects nothing at `t > -1`, which is where all jumps live. The one piece not closed is the
*type transport* of the upper-group identification (and hence of their
`IsUpperRamificationJump`/`isUpperRamificationJump_int` against the project's `G^v`): both
sides are proved to be "the same construction at `A`", but their `upperRamificationGroup` is
hard-wired to `(valuation L).valuationSubring` under the instance package, so stating the
equality needs a `letI`-stated transport along `hA`. Deferred — Pass 99 if wanted.

#### Mathlib API that did the work

`Valuation.HasExtension.ofComapInteger` (`RingTheory/Valuation/Extension.lean`),
`Valuation.Integers.mem_of_integral` + `Valuation.integer.integers`
(`RingTheory/Valuation/Integral.lean`), `isIntegral_algebraMap_iff` (P97 form),
`Finset.sum_Ico_add'`, `Nat.floor_le`/`Nat.lt_floor_add_one`, `Int.ceil_add_one`,
`Int.ceil_toNat`, `Int.lt_ceil`, `Rat.cast_intCast`. Upstream names verified by reading
`.lake/packages/ClassFieldTheory/Lean4/ClassFieldTheory/{Definitions,Theorems}/HasseArf/*`.

#### Rule-2 / scope

No new `structure`/`class`; no load-bearing-hypothesis claim (the abelian hypothesis is the
upstream theorem's; no "necessary" claim is made, so no owed witness). D2 respected: the two
`letI`-stated bricks are the only statements mentioning `extensionValuativeRel`; the two
headlines and all identification lemmas are instance-free on `L`. Recovers nothing from an
abstract group; R1–R3 untouched. **Hasse–Arf is imported, not earned** — the pass's own
mathematics is `𝒪_L ∩ K = 𝒪_K`, the `HasExtension` discharge, and the identification of two
independently-built Herbrand theories, which is real but small.
