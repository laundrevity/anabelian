/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.ExactCycle
import Mathlib

/-!
# L3.1: the snake — the connecting homomorphism (Pass 89)

The hard brick of the Herbrand-quotient multiplicativity. For a pair-equivariant short
exact sequence of commutative groups `1 → M' →ι M →π M'' → 1` (with pairs
`(f',g') → (f,g) → (f'',g'')` intertwined by `ι, π` and `f∘g = g∘f = 1` on `M`):

> **`snakeDelta : Ĥ⁰(M'') →* Ĥ¹(M')`** with **`snakeDelta (Φ x) = ψ x`**

where `Ĥ⁰ = herbrandH f'' g''`, `Ĥ¹ = herbrandH g' f'` (Pass 87's carriers).

The construction avoids all cocycle bookkeeping through two structural observations:
1. **The pullback is a homomorphism**: on the subgroup `T = π⁻¹(ker f'') ≤ M`, the map
   `Y : x ↦ (the unique y' with ι y' = f x)` is multiplicative — `ι`-injectivity forces
   it. No "well-defined up to choice" at this stage: `Y` is a genuine `T →* ker g'`.
2. **One kernel condition**: the classical two-step well-definedness (independence of the
   lift; invariance under `im g''`) merges into the single containment `ker Φ ≤ ker ψ`
   (where `Φ : T → Ĥ⁰(M'')` is projection and `ψ = mk ∘ Y`), proved by one computation.
   `δ` is then `ψ` factored through the surjective `Φ` — the first isomorphism theorem.

The `(f,g)`-swap instantiates the periodic partner `Ĥ¹(M'') → Ĥ⁰(M')` with no new code.
Next pass: the six exactness proofs of the cycle
`Ĥ⁰(M') → Ĥ⁰(M) → Ĥ⁰(M'') →δ Ĥ¹(M') → Ĥ¹(M) → Ĥ¹(M'') →δ' (loop)`, then Pass 88's
alternating-card lemma closes `q(M) = q(M')·q(M'')`.

## Honesty

Homological infrastructure below the multiplicativity theorem, which is NOT yet claimed
(exactness remains) — **no reach toward R1–R3**. No new `structure`/`class`; no owed
witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian


section Snake

variable {M' M M'' : Type*} [CommGroup M'] [CommGroup M] [CommGroup M'']

/-- For `x` in the lift domain `T = π⁻¹(ker f'')`, `f x` lands in `ι`'s range:
`π(f x) = f''(π x) = 1` and `ker π = range ι`. -/
theorem f_mem_range_of_mem_comap (ι : M' →* M) (π : M →* M'') (f : M →* M)
    (f'' : M'' →* M'') (hexact : ι.range = π.ker) (hfπ : ∀ x, π (f x) = f'' (π x))
    {x : M} (hx : x ∈ f''.ker.comap π) : f x ∈ ι.range := by
  rw [hexact, MonoidHom.mem_ker, hfπ]
  rw [Subgroup.mem_comap, MonoidHom.mem_ker] at hx
  exact hx

/-- The snake pullback: for `x ∈ T`, the unique `y' ∈ M'` with `ι y' = f x`. -/
noncomputable def snakePull (ι : M' →* M) (π : M →* M'') (f : M →* M) (f'' : M'' →* M'')
    (hexact : ι.range = π.ker) (hfπ : ∀ x, π (f x) = f'' (π x))
    (x : f''.ker.comap π) : M' :=
  (f_mem_range_of_mem_comap ι π f f'' hexact hfπ x.2).choose

theorem iota_snakePull (ι : M' →* M) (π : M →* M'') (f : M →* M) (f'' : M'' →* M'')
    (hexact : ι.range = π.ker) (hfπ : ∀ x, π (f x) = f'' (π x))
    (x : f''.ker.comap π) :
    ι (snakePull ι π f f'' hexact hfπ x) = f x.1 :=
  (f_mem_range_of_mem_comap ι π f f'' hexact hfπ x.2).choose_spec

/-- **The pullback is a homomorphism** `T →* ker g'` — the design observation that makes
the whole snake tractable: `ι`-injectivity forces multiplicativity
(`ι(Y(xy)) = f(xy) = f(x)f(y) = ι(Y(x)·Y(y))`), and `g(f x) = 1` puts the values in
`ker g'`. No cocycle bookkeeping. -/
noncomputable def snakeY (ι : M' →* M) (π : M →* M'') (g' : M' →* M')
    (f g : M →* M) (f'' : M'' →* M'')
    (hι : Function.Injective ι) (hexact : ι.range = π.ker)
    (hgι : ∀ z, ι (g' z) = g (ι z)) (hfπ : ∀ x, π (f x) = f'' (π x))
    (hgf : ∀ x : M, g (f x) = 1) :
    (f''.ker.comap π) →* g'.ker where
  toFun x := ⟨snakePull ι π f f'' hexact hfπ x, by
    rw [MonoidHom.mem_ker]
    apply hι
    rw [hgι, iota_snakePull, hgf, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply hι
    rw [iota_snakePull]
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply hι
    push_cast
    rw [map_mul, iota_snakePull, iota_snakePull, iota_snakePull]
    push_cast
    rw [map_mul]

/-- `Φ : T →* Ĥ⁰(M'')` — restrict `π` to the lift domain and project. Surjective, and its
kernel is exactly the ambiguity of the snake construction. -/
noncomputable def snakePhi (π : M →* M'') (f'' g'' : M'' →* M'') :
    (f''.ker.comap π) →* herbrandH f'' g'' :=
  (QuotientGroup.mk' (g''.range.subgroupOf f''.ker)).comp
    { toFun := fun x => ⟨π x.1, x.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp }

theorem snakePhi_surjective (π : M →* M'') (f'' g'' : M'' →* M'')
    (hπ : Function.Surjective π) :
    Function.Surjective (snakePhi π f'' g'') := by
  intro c
  induction c using QuotientGroup.induction_on with | _ x'' =>
  obtain ⟨x, hx⟩ := hπ x''.1
  have hxT : x ∈ f''.ker.comap π := by
    rw [Subgroup.mem_comap, hx]
    exact x''.2
  refine ⟨⟨x, hxT⟩, ?_⟩
  have h2 : (⟨π x, hxT⟩ : f''.ker) = x'' := Subtype.ext hx
  change QuotientGroup.mk (⟨π x, hxT⟩ : f''.ker) = QuotientGroup.mk x''
  rw [h2]

/-- `ψ : T →* Ĥ¹(M')` — the pullback hom composed with the projection. -/
noncomputable def snakePsi (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M')
    (f g : M →* M) (f'' : M'' →* M'')
    (hι : Function.Injective ι) (hexact : ι.range = π.ker)
    (hgι : ∀ z, ι (g' z) = g (ι z)) (hfπ : ∀ x, π (f x) = f'' (π x))
    (hgf : ∀ x : M, g (f x) = 1) :
    (f''.ker.comap π) →* herbrandH g' f' :=
  (QuotientGroup.mk' (f'.range.subgroupOf g'.ker)).comp
    (snakeY ι π g' f g f'' hι hexact hgι hfπ hgf)

/-- **The kernel condition** `ker Φ ≤ ker ψ` — the entire well-definedness of the snake in
one statement (lift-independence AND `im g''`-invariance merge): if `π x = g'' w''`, then
`x = (g w)·ι z'` for a lift `w` of `w''`, so `ι(Y x) = f(g w)·f(ι z') = ι(f' z')` (using
`f∘g = 1` on `M`), so `Y x ∈ im f'` and `ψ x = 1`. -/
theorem snakePhi_ker_le (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M')
    (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) (hgf : ∀ x : M, g (f x) = 1) :
    (snakePhi π f'' g'').ker ≤ (snakePsi ι π f' g' f g f'' hι hexact hgι hfπ hgf).ker := by
  intro x hx
  -- Φ x = 1 means π x ∈ range g'' (inside ker f'')
  have hx' : ((⟨π x.1, x.2⟩ : f''.ker)
      : f''.ker ⧸ (g''.range.subgroupOf f''.ker)) = 1 := hx
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx'
  obtain ⟨w'', hw''⟩ := hx'
  obtain ⟨w, hw⟩ := hπ w''
  -- x = (g w) · ι z' for some z'
  have hker : x.1 * (g w)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgπ, hw, hw'']
    simp
  rw [← hexact] at hker
  obtain ⟨z', hz'⟩ := hker
  -- ι (Y x) = f x = f(g w) · f(ι z') = ι (f' z')
  have hx1 : x.1 = g w * ι z' := by
    rw [hz', mul_comm x.1, mul_inv_cancel_left]
  have hY : ι (snakePull ι π f f'' hexact hfπ x) = ι (f' z') := by
    rw [iota_snakePull, hx1, map_mul, hfg, one_mul, hfι]
  -- so Y x ∈ range f', hence ψ x = 1
  have hgoal : ((snakeY ι π g' f g f'' hι hexact hgι hfπ hgf x : g'.ker)
      : g'.ker ⧸ (f'.range.subgroupOf g'.ker)) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨z', (hι hY).symm⟩
  exact hgoal

/-- **THE CONNECTING HOMOMORPHISM** `δ : Ĥ⁰(M'') →* Ĥ¹(M')` of a pair-equivariant short
exact sequence `1 → M' → M → M'' → 1`: factor `ψ` through the surjection `Φ` (first
isomorphism theorem + the kernel condition). The `(f,g)`-swapped instance gives the
periodic partner `Ĥ¹(M'') → Ĥ⁰(M')` for free. -/
noncomputable def snakeDelta (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M')
    (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) (hgf : ∀ x : M, g (f x) = 1) :
    herbrandH f'' g'' →* herbrandH g' f' :=
  (QuotientGroup.lift (snakePhi π f'' g'').ker
    (snakePsi ι π f' g' f g f'' hι hexact hgι hfπ hgf)
    (snakePhi_ker_le ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg hgf)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (snakePhi_surjective π f'' g'' hπ)).symm.toMonoidHom

/-- **The characterizing property** `δ(Φ x) = ψ x` for every `x` in the lift domain — the
computation rule the six exactness proofs will consume. -/
theorem snakeDelta_apply (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M')
    (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) (hgf : ∀ x : M, g (f x) = 1)
    (x : f''.ker.comap π) :
    snakeDelta ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg hgf
        (snakePhi π f'' g'' x)
      = snakePsi ι π f' g' f g f'' hι hexact hgι hfπ hgf x := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective _
      (snakePhi_surjective π f'' g'' hπ)).symm (snakePhi π f'' g'' x)
      = QuotientGroup.mk x := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [snakeDelta, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
  rfl

end Snake


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms snakePull
#print axioms snakeY
#print axioms snakePhi
#print axioms snakePsi
#print axioms snakePhi_ker_le
#print axioms snakeDelta
#print axioms snakeDelta_apply

end Anabelian
