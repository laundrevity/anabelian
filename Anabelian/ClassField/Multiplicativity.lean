/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.Snake
import Mathlib

/-!
# L3.1: the six-term cycle and the multiplicativity of the Herbrand quotient (Pass 90)

The classical trio completes (Pass 87: triviality; Pass 88: the counting engine; Pass 89:
the snake; here: exactness + assembly). For a pair-equivariant short exact sequence
`1 → M' →ι M →π M'' → 1` of commutative groups:

* **`snake_exact_mid` / `snake_exact_top` / `snake_exact_bot`** — exactness of the
  six-term cycle `Ĥ⁰(M') → Ĥ⁰(M) → Ĥ⁰(M'') →δ Ĥ¹(M') → Ĥ¹(M) → Ĥ¹(M'') →δ'` at three
  generic nodes; the other three ARE the same lemmas at the `(f,g)`-swap — six exactness
  facts from three proofs.
* **`herbrandQuotient_mul`** — **`q(M) = q(M') · q(M'')`** (Serre VIII §4 Prop. 10):
  the cycle fed into Pass 88's alternating-card identity, with only the three
  `Ĥ¹`-finiteness hypotheses (infinite `Ĥ⁰`s collapse both sides to `0` together).

With triviality (P87) and multiplicativity, the Herbrand-quotient calculus is OPERATIONAL:
`q` ignores finite modules and multiplies along filtrations — exactly the two moves the
unit-cohomology computations of the cyclic layer (`q(Lˣ)`, `q(U_L)`) perform. Those
computations, the `Rep`-bridge to Mathlib's `FiniteCyclic` `Hⁱ`, and the Hilbert-90
packaging are the remaining L3.1 bricks.

## Honesty

Group-cohomological bookkeeping for the cyclic layer — **no reach toward R1–R3**, and not
yet any class field theory (the reciprocity wall L3.3 is untouched). No new
`structure`/`class`; no owed witness; D1 N/A; D2 untouched.

## Axiom status

Standard axioms only (`#print axioms` below). Ledger: `0 FOUNDATIONAL / 0 DEBT`, unchanged.
-/

namespace Anabelian


section Exactness

variable {M' M M'' : Type*} [CommGroup M'] [CommGroup M] [CommGroup M'']

/-- Computation rule for the functorial map (definitional). -/
theorem herbrandHMap_mk {N : Type*} [CommGroup N]
    (fM gM : M →* M) (fN gN : N →* N) (φ : M →* N)
    (hf : ∀ x, φ (fM x) = fN (φ x)) (hg : ∀ x, φ (gM x) = gN (φ x)) (x : fM.ker) :
    herbrandHMap fM gM fN gN φ hf hg (QuotientGroup.mk x)
      = QuotientGroup.mk (kerRestrict fM fN φ hf x) := rfl

/-- Computation rule for `snakePhi` (definitional). -/
theorem snakePhi_mk (π : M →* M'') (f'' g'' : M'' →* M'') (x : f''.ker.comap π) :
    snakePhi π f'' g'' x = QuotientGroup.mk (⟨π x.1, x.2⟩ : f''.ker) := rfl

/-- Computation rule for `snakePsi` (definitional). -/
theorem snakePsi_mk (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M')
    (f g : M →* M) (f'' : M'' →* M'')
    (hι : Function.Injective ι) (hexact : ι.range = π.ker)
    (hgι : ∀ z, ι (g' z) = g (ι z)) (hfπ : ∀ x, π (f x) = f'' (π x))
    (hgf : ∀ x : M, g (f x) = 1) (x : f''.ker.comap π) :
    snakePsi ι π f' g' f g f'' hι hexact hgι hfπ hgf x
      = QuotientGroup.mk (snakeY ι π g' f g f'' hι hexact hgι hfπ hgf x) := rfl

/-- **Exactness at `Ĥ⁰(M)`**: `im(Ĥ⁰(M') → Ĥ⁰(M)) = ker(Ĥ⁰(M) → Ĥ⁰(M''))`. The
`(f,g)`-swap instantiates exactness at `Ĥ¹(M)`. -/
theorem snake_exact_mid
    (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M') (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) :
    (herbrandHMap f' g' f g ι hfι hgι).range
      = (herbrandHMap f g f'' g'' π hfπ hgπ).ker := by
  have hπι : ∀ z, π (ι z) = 1 := fun z => by
    have h1 : ι z ∈ π.ker := by rw [← hexact]; exact ⟨z, rfl⟩
    exact h1
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using QuotientGroup.induction_on with | _ y' =>
    rw [MonoidHom.mem_ker, herbrandHMap_mk, herbrandHMap_mk]
    have h2 : kerRestrict f f'' π hfπ (kerRestrict f' f ι hfι y')
        = (1 : f''.ker) := Subtype.ext (hπι y'.1)
    rw [h2]
    rfl
  · intro c hc
    induction c using QuotientGroup.induction_on with | _ x =>
    replace hc := MonoidHom.mem_ker.mp hc
    rw [herbrandHMap_mk] at hc
    have hc2 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hc)
    obtain ⟨w'', hw''⟩ := hc2
    have hw''' : g'' w'' = π x.1 := hw''
    obtain ⟨w, hw⟩ := hπ w''
    have hker : x.1 * (g w)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgπ, hw, hw''']
      simp
    rw [← hexact] at hker
    obtain ⟨z', hz'⟩ := hker
    have hz'ker : z' ∈ f'.ker := by
      rw [MonoidHom.mem_ker]
      apply hι
      have hx1 : f x.1 = 1 := x.2
      rw [hfι, hz', map_mul, map_inv, hfg, hx1, map_one, inv_one, mul_one]
    refine ⟨QuotientGroup.mk ⟨z', hz'ker⟩, ?_⟩
    rw [herbrandHMap_mk]
    refine (QuotientGroup.eq).mpr (Subgroup.mem_subgroupOf.mpr ⟨w, ?_⟩)
    have h3 : ((kerRestrict f' f ι hfι ⟨z', hz'ker⟩ : f.ker) : M) = ι z' := rfl
    push_cast
    rw [h3, hz', mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]

/-- **Exactness at `Ĥ⁰(M'')`**: `im(Ĥ⁰(M) → Ĥ⁰(M'')) = ker δ`. The `(f,g)`-swap
instantiates exactness at `Ĥ¹(M'')`. -/
theorem snake_exact_top
    (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M') (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) (hgf : ∀ x : M, g (f x) = 1) :
    (herbrandHMap f g f'' g'' π hfπ hgπ).range
      = (snakeDelta ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ
          hfg hgf).ker := by
  have hπι : ∀ z, π (ι z) = 1 := fun z => by
    have h1 : ι z ∈ π.ker := by rw [← hexact]; exact ⟨z, rfl⟩
    exact h1
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using QuotientGroup.induction_on with | _ x =>
    rw [MonoidHom.mem_ker, herbrandHMap_mk]
    have hT : x.1 ∈ f''.ker.comap π := by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker, ← hfπ]
      have hx1 : f x.1 = 1 := x.2
      rw [hx1, map_one]
    have hPhi : snakePhi π f'' g'' ⟨x.1, hT⟩
        = QuotientGroup.mk (kerRestrict f f'' π hfπ x) := rfl
    rw [← hPhi, snakeDelta_apply, snakePsi_mk]
    have hY : snakeY ι π g' f g f'' hι hexact hgι hfπ hgf ⟨x.1, hT⟩
        = (1 : g'.ker) := by
      apply Subtype.ext
      apply hι
      have h4 := iota_snakePull ι π f f'' hexact hfπ ⟨x.1, hT⟩
      have hx1 : f x.1 = 1 := x.2
      have h5 : (snakeY ι π g' f g f'' hι hexact hgι hfπ hgf ⟨x.1, hT⟩ : M')
          = snakePull ι π f f'' hexact hfπ ⟨x.1, hT⟩ := rfl
      rw [OneMemClass.coe_one, map_one, h5, h4, hx1]
    rw [hY]
    rfl
  · intro c hc
    induction c using QuotientGroup.induction_on with | _ x'' =>
    replace hc := MonoidHom.mem_ker.mp hc
    obtain ⟨x, hx⟩ := hπ x''.1
    have hT : x ∈ f''.ker.comap π := by
      rw [Subgroup.mem_comap, hx]
      exact x''.2
    have h2 : (⟨π x, hT⟩ : f''.ker) = x'' := Subtype.ext hx
    have hPhi : snakePhi π f'' g'' ⟨x, hT⟩ = QuotientGroup.mk x'' := by
      rw [snakePhi_mk, h2]
    rw [← hPhi, snakeDelta_apply, snakePsi_mk] at hc
    have hc2 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hc)
    obtain ⟨u', hu'⟩ := hc2
    have h5 : ι (snakePull ι π f f'' hexact hfπ ⟨x, hT⟩) = f x :=
      iota_snakePull ι π f f'' hexact hfπ ⟨x, hT⟩
    have h6 : ι (f' u') = f x := by
      rw [← h5]
      exact congrArg ι hu'
    have hxt : x * (ι u')⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hfι, h6]
      simp
    refine ⟨QuotientGroup.mk ⟨x * (ι u')⁻¹, hxt⟩, ?_⟩
    rw [herbrandHMap_mk]
    have h7 : kerRestrict f f'' π hfπ ⟨x * (ι u')⁻¹, hxt⟩ = x'' := by
      apply Subtype.ext
      have h8 : (kerRestrict f f'' π hfπ ⟨x * (ι u')⁻¹, hxt⟩ : M'')
          = π (x * (ι u')⁻¹) := rfl
      rw [h8, map_mul, map_inv, hπι, inv_one, mul_one, hx]
    rw [h7]

/-- **Exactness at `Ĥ¹(M')`**: `im δ = ker(Ĥ¹(M') → Ĥ¹(M))`. The `(f,g)`-swap
instantiates exactness at `Ĥ⁰(M')` — closing the cycle. -/
theorem snake_exact_bot
    (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M') (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) (hgf : ∀ x : M, g (f x) = 1) :
    (snakeDelta ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ
        hfg hgf).range
      = (herbrandHMap g' f' g f ι hgι hfι).ker := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using QuotientGroup.induction_on with | _ x'' =>
    obtain ⟨x, hx⟩ := hπ x''.1
    have hT : x ∈ f''.ker.comap π := by
      rw [Subgroup.mem_comap, hx]
      exact x''.2
    have h2 : (⟨π x, hT⟩ : f''.ker) = x'' := Subtype.ext hx
    have hPhi : snakePhi π f'' g'' ⟨x, hT⟩ = QuotientGroup.mk x'' := by
      rw [snakePhi_mk, h2]
    rw [MonoidHom.mem_ker, ← hPhi, snakeDelta_apply, snakePsi_mk,
        herbrandHMap_mk]
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    refine ⟨x, ?_⟩
    have h9 : ((kerRestrict g' g ι hgι
        (snakeY ι π g' f g f'' hι hexact hgι hfπ hgf ⟨x, hT⟩) : g.ker) : M)
        = ι (snakePull ι π f f'' hexact hfπ ⟨x, hT⟩) := rfl
    rw [h9, iota_snakePull]
  · intro c hc
    induction c using QuotientGroup.induction_on with | _ y' =>
    replace hc := MonoidHom.mem_ker.mp hc
    rw [herbrandHMap_mk] at hc
    have hc2 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hc)
    obtain ⟨x, hx⟩ := hc2
    have hx' : f x = ι y'.1 := hx
    have hT : x ∈ f''.ker.comap π := by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker, ← hfπ, hx']
      have h9 : ι y'.1 ∈ π.ker := by rw [← hexact]; exact ⟨y'.1, rfl⟩
      exact h9
    refine ⟨snakePhi π f'' g'' ⟨x, hT⟩, ?_⟩
    rw [snakeDelta_apply, snakePsi_mk]
    have hYy : snakeY ι π g' f g f'' hι hexact hgι hfπ hgf ⟨x, hT⟩ = y' := by
      apply Subtype.ext
      apply hι
      have h5 : (snakeY ι π g' f g f'' hι hexact hgι hfπ hgf ⟨x, hT⟩ : M')
          = snakePull ι π f f'' hexact hfπ ⟨x, hT⟩ := rfl
      rw [h5, iota_snakePull, hx']
    rw [hYy]

/-- **THE MULTIPLICATIVITY THEOREM** (Serre VIII §4 Prop. 10, Neukirch IV 7.3): for a
pair-equivariant short exact sequence `1 → M' → M → M'' → 1`,

`q(M) = q(M') · q(M'')`

— the six-term exact cycle (the three lemmas above + their `(f,g)`-swaps) fed into the
alternating-card identity (Pass 88). Only the three `Ĥ¹`-finiteness hypotheses are
needed: on infinite `Ĥ⁰`s the `Nat.card = 0` conventions collapse both sides to `0`
together. -/
theorem herbrandQuotient_mul
    (ι : M' →* M) (π : M →* M'') (f' g' : M' →* M') (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hexact : ι.range = π.ker)
    (hfι : ∀ z, ι (f' z) = f (ι z)) (hgι : ∀ z, ι (g' z) = g (ι z))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x : M, f (g x) = 1) (hgf : ∀ x : M, g (f x) = 1)
    [Finite (herbrandH g' f')] [Finite (herbrandH g f)]
    [Finite (herbrandH g'' f'')] :
    herbrandQuotient f g
      = herbrandQuotient f' g' * herbrandQuotient f'' g'' := by
  have hcard := card_prod_eq_of_exact_cycle
    (herbrandHMap f' g' f g ι hfι hgι)
    (herbrandHMap f g f'' g'' π hfπ hgπ)
    (snakeDelta ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg hgf)
    (herbrandHMap g' f' g f ι hgι hfι)
    (herbrandHMap g f g'' f'' π hgπ hfπ)
    (snakeDelta ι π g' f' g f g'' f'' hι hπ hexact hgι hfι hgπ hfπ hgf hfg)
    (snake_exact_mid ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg)
    (snake_exact_top ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg hgf)
    (snake_exact_bot ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg hgf)
    (snake_exact_mid ι π g' f' g f g'' f'' hι hπ hexact hgι hfι hgπ hfπ hgf)
    (snake_exact_top ι π g' f' g f g'' f'' hι hπ hexact hgι hfι hgπ hfπ hgf hfg)
    (snake_exact_bot ι π g' f' g f g'' f'' hι hπ hexact hgι hfι hgπ hfπ hgf hfg)
  -- hcard : |Ĥ⁰M'|·|Ĥ⁰M''|·|Ĥ¹M| = |Ĥ⁰M|·|Ĥ¹M'|·|Ĥ¹M''|
  have hb : (Nat.card (herbrandH g f) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hb' : (Nat.card (herbrandH g' f') : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hb'' : (Nat.card (herbrandH g'' f'') : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  rw [herbrandQuotient, herbrandQuotient, herbrandQuotient,
      div_mul_div_comm, div_eq_div_iff hb (mul_ne_zero hb' hb'')]
  have hnat : Nat.card (herbrandH f g)
        * (Nat.card (herbrandH g' f') * Nat.card (herbrandH g'' f''))
      = Nat.card (herbrandH f' g') * Nat.card (herbrandH f'' g'')
        * Nat.card (herbrandH g f) := by
    ring_nf
    ring_nf at hcard
    linarith [hcard]
  exact_mod_cast hnat

end Exactness


-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms herbrandHMap_mk
#print axioms snake_exact_mid
#print axioms snake_exact_top
#print axioms snake_exact_bot
#print axioms herbrandQuotient_mul

end Anabelian
