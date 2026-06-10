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
