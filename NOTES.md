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
