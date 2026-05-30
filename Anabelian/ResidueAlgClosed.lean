/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ResidueReductionIntegral
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Rung L1, discharging the `DEBT`: the residue field is algebraically closed (Pass 16, brick 3c)

## What this pass builds

Continuing the discharge of `residueReduction_surjective` (perfect case) via
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` applied to `B = 𝒪[K̄] = integralClosure
𝒪[K] K̄`, the one remaining hard step is the **residue identification** `𝒪[K̄]/𝔪[K̄] ≅
AlgebraicClosure 𝓀[K]`. Pass 15 decomposed it into bricks 3a–3e. This pass builds the **substantive
content of brick 3c** — that the residue field is algebraically closed — and reduces it, for the
actual `𝒪[K̄]`, to **just brick 3a** (that `𝒪[K̄]` is local, i.e. `𝔪[K̄]` is its maximal ideal).

The key move: 3c is a **general** fact, proved here route-independently and applied to `𝒪[K̄]`:

* `residueField_isAlgClosed_of_integrallyClosed` — **the general 3c lemma.** If `R` is a subring of
  an algebraically closed field `L` (`algebraMap R L` injective) and `R` is **integrally closed in
  `L`** (every `x : L` integral over `R` lies in `R`), then for **any** maximal ideal `m`, the
  residue field `R ⧸ m` is algebraically closed. Proof: a monic `p` over `R ⧸ m` lifts to a monic
  `P` over `R` of the same degree (`lifts_and_natDegree_eq_and_monic`); `P` maps to a monic poly
  over the algebraically closed `L`, which has a root `r` (`IsAlgClosed.exists_root`); `r` is
  integral over `R` (root of the monic `P`), hence `r ∈ R` (integrally closed); and `r mod m` is a
  root of `p`. **This uses `L` algebraically closed + integral-closedness — NOT Henselianness**
  (`K̄` is not complete, so `𝒪[K̄]` is not Henselian; the naive Hensel route does not apply, as
  Pass 15 flagged).

Applied to `R = 𝒪[K̄]`, `L = K̄`, its two hypotheses are discharged here, both route-independent:

* injectivity of `algebraMap 𝒪[K̄] K̄` is `Subtype.coe_injective`;
* `galoisIntegers_integrallyClosed` — **`𝒪[K̄]` is integrally closed in `K̄`** — is the integral
  closure being integrally closed (`x` integral over `integralClosure 𝒪[K] K̄` ⟹ integral over
  `𝒪[K]` by transitivity ⟹ in `integralClosure 𝒪[K] K̄`), via `isIntegral_trans` +
  `IsIntegralClosure.isIntegral_iff`.

* `galoisResidueField_isAlgClosed` — **brick 3c for `𝒪[K̄]`.** For any maximal ideal `m` of `𝒪[K̄]`,
  the residue field `𝒪[K̄] ⧸ m` is algebraically closed. This is 3c **done modulo 3a**: once 3a
  supplies that `𝒪[K̄]` is local (so `𝔪[K̄]` is a maximal ideal), this gives `𝓀̄` algebraically
  closed.

## The D2 fork, decided explicitly (Pass-16 primary discipline)

Brick **3a** (`𝒪[K̄]` local) is this discharge's remaining substantial gate. Pass 16 probed both
routes and found:

* **Native `ValuativeRel` route** — 3a's local-ness reduces to "`integralClosure 𝒪[K] K̄` is a
  `ValuationRing`" (then `ValuationRing.isLocalRing` gives local **for free**). But that
  `ValuationRing` fact is the unique extension of a complete DVR's valuation to `K̄` (Serre,
  *Local Fields* II) —
  **ABSENT** from Mathlib (no valuation-extension-to-algebraic, no Henselian-unique-extension). A
  substantial multi-pass valuation-theory construction.
* **`spectralNorm` route** — would give the valuation on `K̄` directly (Pass 11), but connecting
  it to `integralClosure` needs `spectralNorm x ≤ 1 ↔ IsIntegral 𝒪[K] x`, **also ABSENT**; and it
  re-introduces the `NormedField`-on-`K` bridge (**D2**).

**Decision: stay on the native route; D2 is NOT incurred.** The `spectralNorm` route offers **no
shortcut** for 3a (its `norm ≤ 1 ↔ integral` link is equally absent), so taking on the D2 diamond
buys nothing — exactly the "do not let D2-avoidance turn 3a into an unbounded yak-shave, but do not
incur D2 for no gain" call. The honest target for 3a is therefore: **`integralClosure 𝒪[K] K̄` is a
`ValuationRing`** (⟹ `IsLocalRing` for free), which requires building the unique-extension theory.
That deepens Pass 15's "3a substantial" verdict: 3a is genuinely multi-pass absent valuation theory,
not a one-pass brick.

## `DEBT` status: OPEN — not discharged

The `axiom residueReduction_surjective` is **still present**. Brick **3c is now done** (general
lemma + the `𝒪[K̄]` hypothesis discharges; reduced to 3a). **Route-steps remaining: [3a `𝒪[K̄]`
local = `integralClosure` is a `ValuationRing` (the substantial gate, native route, no D2); 3b
residue algebraic over `𝓀[K]` (moderate); 3d `𝓀̄ ≅ AlgebraicClosure 𝓀[K]` + 3e `Aut` (supported);
Step 4 apply keystone + delete axiom, perfect-case narrowing].** Done: steps 1, 1b, 2a (Passes
13–14), 2b (Pass 15), **3c (this pass)**. **Nothing cardinal-sin posited** — 3c is *proved*, not
stubbed; the residue iso is being *built*, the surjection to be *applied* from a present theorem.
Ledger unchanged at `0 FOUNDATIONAL / 1 DEBT`.

## Axiom status

Standard axioms only (`#print axioms` below). Recovers nothing from an abstract group; no new
`structure`/`class` (no rule-2 obligation). D1 N/A; **D2 not incurred** (native `ValuativeRel`/
integral-closure route; the `spectralNorm` re-entry rejected this pass — no shortcut, see the D2
fork above).
-/

open Polynomial

namespace Anabelian

section General

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] [IsAlgClosed L]

/-- **The general brick 3c.** If `R` is a subring of an algebraically closed field `L`
(`algebraMap R L` injective) that is **integrally closed in `L`** (`hcl`: every `x : L` integral
over `R` lies in `R`), then the residue field `R ⧸ m` at any maximal ideal `m` is algebraically
closed. Route-independent; uses `L` algebraically closed + integral-closedness, **not**
Henselianness. -/
theorem residueField_isAlgClosed_of_integrallyClosed
    (hinj : Function.Injective (algebraMap R L))
    (hcl : ∀ x : L, IsIntegral R x → x ∈ (algebraMap R L).range)
    (m : Ideal R) [m.IsMaximal] :
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    IsAlgClosed (R ⧸ m) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  apply IsAlgClosed.of_exists_root
  intro p hpm hpirr
  -- A monic `p` over `R ⧸ m` lifts to a monic `P` over `R` of the same degree.
  have hlifts : p ∈ Polynomial.lifts (Ideal.Quotient.mk m) :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr (fun _ => Ideal.Quotient.mk_surjective _)
  obtain ⟨P, hPmap, hPdeg, hPmonic⟩ := lifts_and_natDegree_eq_and_monic hlifts hpm
  -- `P` over the algebraically closed `L` has a root `r` (its degree is positive: `p` irreducible).
  have hdeg : (P.map (algebraMap R L)).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hPmonic.map (algebraMap R L)).ne_zero,
        hPmonic.natDegree_map, hPdeg]
    exact_mod_cast hpirr.natDegree_pos.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root (P.map (algebraMap R L)) hdeg
  -- `r` is integral over `R` (root of the monic `P`), hence `r ∈ R` by integral-closedness.
  have haeval : (aeval r) P = 0 := by rw [aeval_def, ← eval_map]; exact hr
  have hrint : IsIntegral R r := ⟨P, hPmonic, haeval⟩
  obtain ⟨s, hs⟩ := hcl r hrint
  -- `s mod m` is the sought root of `p` in `R ⧸ m`.
  refine ⟨Ideal.Quotient.mk m s, ?_⟩
  have hsP : Polynomial.eval s P = 0 := by
    apply hinj
    rw [map_zero, ← eval₂_at_apply (algebraMap R L) s, ← aeval_def, hs]; exact haeval
  rw [← hPmap, eval_map, eval₂_at_apply, hsP, map_zero]

end General

section LocalField

open scoped ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- **`𝒪[K̄]` is integrally closed in `K̄`** — the `hcl` hypothesis of the general 3c brick for the
actual ring. An `x : K̄` integral over `integralClosure 𝒪[K] K̄` is integral over `𝒪[K]`
(transitivity), hence already lies in the integral closure. Route-independent. -/
theorem galoisIntegers_integrallyClosed (x : AlgebraicClosure K)
    (hx : IsIntegral ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) x) :
    x ∈ (algebraMap ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) (AlgebraicClosure K)).range := by
  have hx0 : IsIntegral ↥𝒪[K] x := isIntegral_trans _ hx
  rw [RingHom.mem_range]
  exact IsIntegralClosure.isIntegral_iff.mp hx0

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- **Brick 3c for `𝒪[K̄]`.** For any maximal ideal `m` of `𝒪[K̄] = integralClosure 𝒪[K] K̄`, the
residue field `𝒪[K̄] ⧸ m` is algebraically closed — the general 3c brick applied to `R = 𝒪[K̄]`,
`L = K̄`, with injectivity (`Subtype.coe_injective`) and integral-closedness
(`galoisIntegers_integrallyClosed`) discharged. This is 3c **done modulo 3a**: once 3a supplies that
`𝒪[K̄]` is local (so `𝔪[K̄]` is maximal), `𝓀̄` is algebraically closed. -/
theorem galoisResidueField_isAlgClosed
    (m : Ideal ↥(integralClosure ↥𝒪[K] (AlgebraicClosure K))) [m.IsMaximal] :
    letI : Field (↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) ⧸ m) := Ideal.Quotient.field m
    IsAlgClosed (↥(integralClosure ↥𝒪[K] (AlgebraicClosure K)) ⧸ m) :=
  residueField_isAlgClosed_of_integrallyClosed Subtype.coe_injective
    (galoisIntegers_integrallyClosed K) m

end LocalField

-- Reproducible axiom audit. Standard axioms only — strictly-lower, nothing posited.
#print axioms residueField_isAlgClosed_of_integrallyClosed
#print axioms galoisIntegers_integrallyClosed
#print axioms galoisResidueField_isAlgClosed

end Anabelian
