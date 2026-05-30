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
