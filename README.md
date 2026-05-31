# anabelian

A long-horizon (multi-year) Lean 4 + Mathlib formalization effort in **anabelian geometry**,
aimed ultimately at the **mono-anabelian reconstruction** of a field from Galois- and
monoid-theoretic data.

This is **not** a continuation of the `iutt` project and does not import it. `iutt`'s job was to
*locate* the reconstruction gap; this repository's job is to *fill* it, rung by rung, axiom-free.

## How this repository is governed

The discipline matters more than any single file. Read these in order:

- **`CLAUDE.md`** — the constitution: the axiom-budget discipline, rule-2, the honest scope.
- **`AXIOM_LEDGER.md`** — every non-standard axiom, classified `FOUNDATIONAL` (honest boundary) vs
  `DEBT` (a hole we intend to fill). Currently **zero `FOUNDATIONAL`, one `DEBT`** (the residue
  surjection; introduced Pass 5 as `FOUNDATIONAL`, reclassified to `DEBT` Pass 11 once its discharge
  was begun). This, not `#print axioms` alone, is the source of truth for what is assumed.
- **`ROADMAP.md`** — the dependency ladder from the current Mathlib floor up to mono-anabelian
  reconstruction. Bottom rungs concrete; top rungs explicitly multi-year and far.
- **`NOTES.md`** — per-pass record: the Mathlib inventory, what was proved, the ledger delta.

## Current state (Pass 20) — the `DEBT` is discharged

Clean cached build on Mathlib `v4.30.0` (8494 jobs). **Zero `FOUNDATIONAL`, zero `DEBT`** — and **zero
`axiom` declarations project-wide.** The project's sole non-standard axiom, the residue surjection
`residueReduction_surjective`, was **DISCHARGED into a proved `theorem` in Pass 20** (perfect case):
`#print axioms` is standard-only (`propext`/`Classical.choice`/`Quot.sound`) on it and on every
downstream result. Zero open owed witnesses; no second boundary ever stacked. This is the project's
**first `DEBT`-discharged-into-theorem** — the genuine progress signal the discipline exists to produce.

**Milestone (Pass 10): the first L1 *whole of depth* is closed.** `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ` — the absolute
Galois group of a finite field is the profinite completion of `ℤ`, as a topological group — is proved
as a complete axiom-free `ContinuousMulEquiv` (`Anabelian.galoisContinuousMulEquivZHat`), earned across
Passes 6–10 with **nothing posited** in the chain.

**Inflection (Pass 11): begin discharging the one boundary.** Rather than harvest more breadth, Pass 11
committed to *driving the single boundary down*: it built the valuation-on-`K̄` foundational brick (the
spectral valuation ring `𝒪[K̄]` + Galois-invariance, `Anabelian.spectralIntegers`, axiom-free) and
reclassified `residueReduction_surjective` `FOUNDATIONAL → DEBT` — a committed, under-construction debt,
not a static posit. The valuation on `K̄` is the common prerequisite for both the residue discharge and
any ramification-filtration work.

**Verdict (Pass 12): the hard step is not a wall.** Front-loading the discharge's hardest step (the
*lifting*), Pass 12 found Mathlib already proves the residue-reduction surjectivity in the profinite
setting — `Ideal.Quotient.stabilizerHom_surjective_of_profinite` — so **no maximal-unramified
construction is needed**; the discharge is a bounded sub-plan with the keystone present. The `DEBT`
remains **open** (no new axiom).

**Fit + pivot (Pass 13): the keystone's exact hypotheses, verified.** Pass 13 checked the keystone fits
`𝒪[K̄]`/`Gal(K̄/K)`: `B` must carry the **discrete** (Krull) topology, and `Gal(K̄/K)` is profinite only
via `IsGalois K K̄` (a tracked prerequisite — holds for perfect/char-0 local fields, not imperfect
equal-char). It pivoted the route to `B = integralClosure 𝒪[K] K̄` (native to `ValuativeRel`,
**avoiding the `NormedField` bridge — no D2 diamond**) and built that ring + its Galois `MulSemiringAction`
(`Anabelian.galoisIntegers`, `galoisIntegers_isInvariant`, route step 1b). Steps 2–4 remain; `DEBT` open.

**Step 2 + generality (Pass 14).** Built the fixed-ring `𝒪[K̄]^Gal = 𝒪[K]`
(`Anabelian.galoisIntegers_algebraIsInvariant`, the keystone's `Algebra.IsInvariant` hypothesis,
perfect case, axiom-free). **Generality decision:** the discharge will be the **perfect case**
(`[PerfectField K]` — char-0/mixed-char local fields); the statement is also true for imperfect
equal-char `K` (`𝔽_q((t))`), tracked as a named remainder.

**Step 2b + residue-iso verdict (Pass 15).** Built `Anabelian.continuousSMul_galoisIntegers` (the
keystone's `DiscreteTopology` + `ContinuousSMul` hypotheses, via open Krull stabilizers, axiom-free).
The remaining **blocker** — the residue iso `𝒪[K̄]/𝔪 ≅ AlgebraicClosure 𝓀[K]` — is now a verified
**bounded multi-pass sub-plan** (its `𝒪[K̄]`-local and residue-algebraically-closed pieces are
absent/substantial; the `≅ AlgebraicClosure` repackaging is `IsAlgClosure`-supported), **not a wall**.
`DEBT` still **open**.

**Brick 3c + the D2-fork decision (Pass 16).** Built `Anabelian.galoisResidueField_isAlgClosed` — the
**residue field of `𝒪[K̄]` is algebraically closed** — axiom-free and *route-independent*, via a general
lemma (`residueField_isAlgClosed_of_integrallyClosed`: the residue field of an integrally-closed subring
of an algebraically closed field is algebraically closed, by a monic-lift argument, **not** Hensel) plus
its two `𝒪[K̄]` hypotheses (injectivity; `𝒪[K̄]` integrally closed in `K̄`). This is the residue iso's
brick **3c, done modulo 3a**. The pass also **decided the D2 fork explicitly**: 3a (`𝒪[K̄]` local)
reduces to "`integralClosure 𝒪[K] K̄` is a `ValuationRing`" (then local for free) — absent, but the
`spectralNorm` route gives **no shortcut** (its `norm ≤ 1 ↔ integral` link is equally absent), so the
discharge **stays native and incurs no D2**. The residue iso now reduces to the single gate 3a; `DEBT`
still **open**.

**3a route comparison + bridge's algebraic half (Pass 17).** Re-opened the 3a route decision by
**estimated pass-count across three routes** — (i) native `ValuationRing` (~3 passes; valuation-extension-
to-`K̄` absent), (ii) `spectralNorm` (~2 passes **+ a tracked D2**; local-ness *free* via `Valued.integer`,
bridge *reachable* via `spectralValue_le_one_iff`), (iii) Henselian-local-direct (~2–3 passes;
integral-closure-local + colimit absent). **Chose route (ii) and to incur the tracked D2**, by the cost
principle (a bounded fix-once D2 is cheaper than several passes of foundational theory) — **reversing
Pass 16's "stay native"** on new evidence (Pass 16 had missed `spectralValue_le_one_iff` and the free
`Valued.integer` local-ness). Built `Anabelian.isIntegral_iff_minpoly_coeff_mem` — `IsIntegral 𝒪[K] x ↔
minpoly K x` has all coefficients in `𝒪[K]` — the bridge's **algebraic half**, axiom-free and **D2-free**
(D2 deferred to the spectral steps). `DEBT` still **open**; 3a is ~2 passes out (D2 setup + bridge +
transport), the discharge ~3.

**Brick 3a — `𝒪[K̄]` is local — DONE, with the D2 diamond localized (Pass 18).** Built
`Anabelian.isLocalRing_galoisIntegers : IsLocalRing ↥(integralClosure 𝒪[K] K̄)` via route (ii): the
spectral `Valued.integer K̄` is a `ValuationRing` ⟹ local for free, and the bridge `integralClosure 𝒪[K]
K̄ = Valued.integer K̄` (via `spectralValue_le_one_iff` + Pass-17's algebraic half + the norm↔valuation
agreement, which is `Iff.rfl`) transports local-ness back along a `RingEquiv`. **The D2 `NormedField`
diamond is incurred but localized entirely inside the proof** (a `letI` chain — none leaks to the
statement), so the prior bricks 2a/2b/3c **re-typecheck standard-axioms-only** (verified). With 3a,
`𝔪[K̄]` is *the* maximal ideal, so brick 3c gives `𝓀̄` algebraically closed. 3a was the **last
substantial gate**: the residue iso now reduces to 3b (residue algebraic) + 3d/3e (`IsAlgClosure`
repackaging), then Step 4 (apply the keystone, **delete the axiom**) — the discharge is ~2 passes out.
`DEBT` still **open**.

**Residue identification complete (Pass 19) — clean partial, discharge ~1 pass out.** Built
`Anabelian/ResidueIso.lean` (axiom-free): `galoisIntegers_isLocalHom` (`algebraMap 𝒪[K] 𝒪[K̄]` is a local
hom, which hands `(𝔪[K̄]).LiesOver (𝔪[K])` and `Algebra 𝓀[K] 𝓀̄` for free), `galoisResidueEquiv` (bricks
3b+3d: `𝓀̄ := 𝒪[K̄]/𝔪[K̄] ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K]`), and `galoisResidueAut` (brick 3e:
`Aut(𝓀̄/𝓀[K]) ≃* Field.absoluteGaloisGroup 𝓀[K]`). A probe confirmed the keystone
`stabilizerHom_surjective_of_profinite` **typechecks** on our `G/B/A/P/Q` (the only missing instance is
`ContinuousSMul`, = Pass-2b). So only **Step 4** remains — supply `ContinuousSMul`, prove `stabilizer G
𝔪[K̄] = ⊤`, reinterpret via `galoisResidueAut`, and **delete the axiom** for a `[PerfectField K]` theorem.
Step 4 was **deliberately not half-assembled** this pass (a half-built discharge is worse than a clean
partial); the discharge is **~1 pass out**. `DEBT` still **open**.

**THE DISCHARGE (Pass 20): `residueReduction_surjective` is now a proved `theorem`, `DEBT → 0`.** In
`UnramifiedQuotient.lean` the `axiom` was **deleted** and replaced by a `theorem` (perfect case,
`[PerfectField K]`) of the same statement. Step 4 assembled the keystone
`Ideal.Quotient.stabilizerHom_surjective_of_profinite`: with `𝒪[K̄]` local, `𝔪[K̄]` is the unique
maximal ideal, so every `σ ∈ Gal(K̄/K)` fixes it (`stabilizer = ⊤`); the keystone gives `stabilizer ↠
Aut(𝓀̄/𝓀[K])`; `galoisResidueAut` (the residue identification) turns the codomain into
`Field.absoluteGaloisGroup 𝓀[K]` and `stabilizer = ⊤` the domain into `Gal(K̄/K)`. **`#print axioms` is
standard-only on the theorem and all downstream (`unramifiedQuotient_iso`/`_procyclic` now carry
`[PerfectField K]`); no new axiom replaced it.** The surjection now *follows* — nothing posited. The
imperfect equal-characteristic case (via `Aut(K̄/K) ≅ Gal(K^sep/K)`) is the tracked remainder. **Ledger
`0 FOUNDATIONAL / 0 DEBT`** — the project's first `DEBT`-discharged-into-theorem.

- `Anabelian/Basic.lean` (L0) — faithfulness of the infinite Galois correspondence: the
  *precondition* of reconstruction, not reconstruction.
- `Anabelian/FiniteField.lean` (L1) — the absolute Galois group of a finite field is **commutative**
  (Pass 1) and **procyclic**, i.e. topologically generated by Frobenius (Pass 2).
- `Anabelian/RationalsNonAbelian.lean` (L1) — `Gal(ℚ̄/ℚ)` is **non-commutative** (Pass 3), via
  `(X³-2).Gal ≅ S₃`. This discharges owed witness **W1**, proving `[Finite F]` is load-bearing for
  the finite-field lemmas above.
- `Anabelian/ResidueReduction.lean` (L1) — the **faithfulness half** of the residue reduction
  (Pass 4): inertia = pointwise residue-stabilizer, and `decomposition ⧸ inertia` embeds in residue
  automorphisms (axiom-free).
- `Anabelian/UnramifiedQuotient.lean` (L1) — Pass 5 takes the residue **surjectivity** as a classified
  `FOUNDATIONAL` boundary (`residueReduction_surjective`, Serre/Neukirch, strictly below R1) and proves
  real structure on it: the **unramified quotient `G_K ⧸ N ≅ Gal(𝓀̄/𝓀)` is procyclic** (via Pass 2).
- `Anabelian/FiniteFieldZHat.lean` (L1) — Pass 6 proves, axiom-free, the **surjective half of
  `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`**: the canonical map `Ẑ → Gal(K̄/K)` (profinite-completion universal property) is
  surjective. No new boundary (the anti-`FOUNDATIONAL`-stacking discipline).
- `Anabelian/FiniteGaloisCyclic.lean` (L1) — Pass 7 closes, axiom-free, the **per-level ingredient of
  `≅ Ẑ`'s injective half**: `Gal(L/K) ≃* Multiplicative (ZMod (finrank K L))` for finite `L/K` (the
  level `Gal(𝔽_{q^n}/𝔽_q) ≅ ℤ/n`). A *complete* theorem, not another half — but modest; the full `≅ Ẑ`
  remains open (needs `Ẑ = lim ℤ/n` + cofinal matching) and is **not** posited. No new boundary.
- `Anabelian/ZHatProcyclic.lean` (L1) — Pass 8 proves, axiom-free, the **`Ẑ`-side inverse-system
  presentation** of `≅ Ẑ`: `Ẑ` is **procyclic** (`zhat_topologicalClosure_eq_top`, the `Ẑ`-side
  analogue of Pass 2) and its finite quotients are **cyclic** (`zhat_quotient_isCyclic`). The pass's
  job was to *close* `≅ Ẑ`; closure is blocked on the absent Galois-side level subfield `𝔽_{q^n} ⊆ K̄`,
  so the iso is **not** closed and **not** posited — instead a numbered Pass 9–11 sub-plan (in
  `ROADMAP.md`) sharpens the remainder. No new boundary.
- `Anabelian/FiniteFieldLevel.lean` (L1) — Pass 9 builds, axiom-free, the **Galois-side level
  subfields** for `≅ Ẑ` (sub-plan rung 9, **infrastructure**): `𝔽_{q^n} ⊆ K̄` of degree `n`
  (`levelField`/`levelFGIF`), the restriction `r_n : Gal(K̄/K) → Gal(𝔽_{q^n}/K)` (`levelRestrict`,
  surjective), and the **Frobenius-aligned** generator (`levelRestrict_frobenius`:
  `r_n(Frob) = frobeniusAlgEquivOfAlgebraic`; `orderOf (r_n Frob) = n`). Graded as infrastructure: the
  iso is **not** closed and **not** posited; injectivity is Pass 10. No new boundary.
- `Anabelian/FiniteFieldZHatIso.lean` (L1) — Pass 10 **closes `Gal(𝔽_q̄/𝔽_q) ≅ Ẑ`** axiom-free, the
  **first L1 whole of depth**: `zhatToGalois_injective` (`ker zhatToGalois = ⊥`, via
  `ker χ_m = closure⟨zhatGen^m⟩` + separation + Lagrange) and the topological-group isomorphism
  `galoisContinuousMulEquivZHat : Gal(𝔽_q̄/𝔽_q) ≃ₜ* Ẑ`. Nothing posited; no new boundary.
- `Anabelian/SpectralValuation.lean` (L1) — Pass 11 begins discharging the one boundary, axiom-free:
  the **spectral valuation ring `𝒪[K̄]`** (`spectralIntegers`, the closed unit ball of `spectralNorm`,
  a `Subring`) and that **`Gal(K̄/K)` preserves it** (`spectralIntegers_mem_iff_galois`). The
  foundational brick of the residue-surjection discharge route; the lifting (its heart) is untouched.
- `Anabelian/ResidueReductionRoute.lean` (L1) — Pass 12's lifting-tractability verdict (the hard step
  is **not** a wall; `stabilizerHom_surjective_of_profinite` supplies the surjectivity) + the
  Galois **`MulSemiringAction` on `𝒪[K̄]`** (`spectralIntegers_isInvariant`, route step 1b, axiom-free).
- `Anabelian/ResidueReductionIntegral.lean` (L1) — Pass 13's keystone fit-verdict + route pivot to
  `B = integralClosure 𝒪[K] K̄` (the keystone's actual ring, no `NormedField` bridge): `galoisIntegers`
  + `galoisIntegers_isInvariant` (the Galois `MulSemiringAction` on `B`, axiom-free), over the exact
  `IsNonarchimedeanLocalField` setting. Records the `IsGalois K K̄` profinite prerequisite.
- `Anabelian/ResidueReductionInvariant.lean` (L1) — Pass 14's fixed-ring `𝒪[K̄]^Gal = 𝒪[K]`
  (`galoisIntegers_algebraIsInvariant`, the keystone's `Algebra.IsInvariant` hypothesis, perfect case,
  axiom-free) + the documented generality decision (perfect-case discharge; imperfect case tracked).
- `Anabelian/ResidueReductionContinuity.lean` (L1) — Pass 15's Step 2b (`galoisStabilizer_isOpen` ⟹
  `continuousSMul_galoisIntegers`, the keystone's `DiscreteTopology` + `ContinuousSMul` hypotheses,
  axiom-free) + the residue-iso verdict (bounded multi-pass sub-plan, not a wall) in its docstring.
- `Anabelian/ResidueAlgClosed.lean` (L1) — Pass 16's brick **3c**: the general
  `residueField_isAlgClosed_of_integrallyClosed` (residue field of an integrally-closed subring of an
  alg-closed field is alg-closed; monic-lift, not Hensel) + `galoisIntegers_integrallyClosed` (`𝒪[K̄]`
  integrally closed in `K̄`) ⟹ `galoisResidueField_isAlgClosed` (residue field at any maximal ideal of
  `𝒪[K̄]` is alg-closed — 3c done modulo 3a). Axiom-free, route-independent; the D2-fork decision (stay
  native) is in its docstring.
- `Anabelian/GaloisIntegersLocal.lean` (L1) — Pass 17's 3a work: the **three-route comparison** (native
  `ValuationRing` ~3 / `spectralNorm` ~2 +D2 / Henselian-direct ~2–3, chosen route (ii), reversing
  Pass 16) in its docstring, and the brick `isIntegral_iff_minpoly_coeff_mem` (`IsIntegral 𝒪[K] x ↔
  minpoly K x` coeffs in `𝒪[K]`) — the **algebraic half** of route (ii)'s bridge, axiom-free, D2-free.
  Pass 18 lands brick **3a** here too: `isLocalRing_galoisIntegers` (`𝒪[K̄]` local, via route (ii); the
  D2 `NormedField` diamond incurred-localized inside the proof). Uses `import Mathlib` (sanctioned
  fallback for the breadth of spectral/valued/normed API).
- `Anabelian/ResidueIso.lean` (L1) — Pass 19's **residue identification** (axiom-free): the connective
  `galoisIntegers_isLocalHom` (`algebraMap 𝒪[K] 𝒪[K̄]` local hom ⟹ `LiesOver` + `Algebra 𝓀[K] 𝓀̄` free),
  `galoisResidueEquiv` (bricks 3b+3d: `𝓀̄ ≃ₐ[𝓀[K]] AlgebraicClosure 𝓀[K]`), `galoisResidueAut` (brick 3e:
  `Aut(𝓀̄/𝓀[K]) ≃* Gal 𝓀[K]`). All that remains for the discharge is Step 4 (keystone application —
  which typechecks — + `stabilizer = ⊤` + axiom deletion). Uses `import Mathlib`.

**Every file now rests on standard axioms only** — `residueReduction_surjective` (the lone non-standard
axiom, `FOUNDATIONAL` Passes 5–10, `DEBT` Passes 11–19) was discharged into a `theorem` in Pass 20, so
there are **zero `axiom` declarations** in the project (see `AXIOM_LEDGER.md`). All files touch the
project's subject (absolute Galois groups) while recovering nothing from an abstract group — the
reconstruction targets (R1–R3 in `ROADMAP.md`) remain distant and untouched.

`AXIOM_LEDGER.md` also tracks **Owed witnesses** (unproved load-bearing-hypothesis claims, a debt of
rigor distinct from axioms); W1 was discharged in Pass 3, so none are open.

## Build

```sh
lake exe cache get   # never build Mathlib from source
lake build
```

`lake build` re-runs the `#print axioms` audit of the headline results on every build.
