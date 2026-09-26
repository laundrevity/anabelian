/-
Copyright (c) 2026 Conor Mahany. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Conor Mahany
-/
import Anabelian.ClassField.Multiplicativity

/-!
# L3.1: reduction through an acyclic subgroup with finite quotient (Pass 95)

For a pair-equivariant short exact sequence `1 → M' → M → M'' → 1`, assume `M''`
is finite and both cohomology groups of `M'` are trivial. Then both cohomology
groups of `M` are finite and its Herbrand quotient is one.

`snake_exact_mid`, in both orders of the pair, first injects the middle cohomology
groups into those of `M''`. Only after deriving finiteness do we apply
`herbrandQuotient_mul` and finite-group triviality. Thus middle finiteness is a
conclusion, not an input to its own derivation.

The intended local-field application takes `M'` to be a small lattice-unit subgroup
and `M` to be the full integral unit group. Constructing that subgroup and proving
its acyclicity remain future work, recorded in NOTES Pass 95. This theorem is an
abstract conditional reduction; no local-field unit formula is proved here.
-/

namespace Anabelian

/-- An acyclic kernel and a finite quotient give finite middle cohomology in both
degrees and Herbrand quotient one. All hypotheses are carried; no sharpness claim
is made. -/
theorem finite_acyclic_kernel_reduction
    {M' M M'' : Type*} [CommGroup M'] [CommGroup M] [CommGroup M''] [Finite M'']
    (ι : M' →* M) (π : M →* M'')
    (f' g' : M' →* M') (f g : M →* M) (f'' g'' : M'' →* M'')
    (hι : Function.Injective ι) (hπ : Function.Surjective π) (hexact : ι.range = π.ker)
    (hfι : ∀ x, ι (f' x) = f (ι x)) (hgι : ∀ x, ι (g' x) = g (ι x))
    (hfπ : ∀ x, π (f x) = f'' (π x)) (hgπ : ∀ x, π (g x) = g'' (π x))
    (hfg : ∀ x, f (g x) = 1) (hgf : ∀ x, g (f x) = 1)
    [Subsingleton (herbrandH f' g')] [Subsingleton (herbrandH g' f')] :
    Finite (herbrandH f g) ∧ Finite (herbrandH g f) ∧ herbrandQuotient f g = 1 := by
  letI : Finite (herbrandH f'' g'') :=
    inferInstanceAs (Finite (f''.ker ⧸ g''.range.subgroupOf f''.ker))
  letI : Finite (herbrandH g'' f'') :=
    inferInstanceAs (Finite (g''.ker ⧸ f''.range.subgroupOf g''.ker))
  have hinj0 : Function.Injective (herbrandHMap f g f'' g'' π hfπ hgπ) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← snake_exact_mid ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg]
    apply le_antisymm _ bot_le
    rintro x ⟨a, rfl⟩
    have ha : a = 1 := Subsingleton.elim _ _
    simp [ha]
  have hinj1 : Function.Injective (herbrandHMap g f g'' f'' π hgπ hfπ) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [← snake_exact_mid ι π g' f' g f g'' f'' hι hπ hexact hgι hfι hgπ hfπ hgf]
    apply le_antisymm _ bot_le
    rintro x ⟨a, rfl⟩
    have ha : a = 1 := Subsingleton.elim _ _
    simp [ha]
  letI : Finite (herbrandH f g) := Finite.of_injective _ hinj0
  letI : Finite (herbrandH g f) := Finite.of_injective _ hinj1
  have hfg'' : ∀ x, f'' (g'' x) = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    rw [← hgπ, ← hfπ, hfg, map_one]
  have hgf'' : ∀ x, g'' (f'' x) = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := hπ x
    rw [← hfπ, ← hgπ, hgf, map_one]
  have hq' : herbrandQuotient f' g' = 1 := by
    have h0 : Nat.card (herbrandH f' g') = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    have h1 : Nat.card (herbrandH g' f') = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [herbrandQuotient, h0, h1]
    norm_num
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [herbrandQuotient_mul ι π f' g' f g f'' g'' hι hπ hexact hfι hgι hfπ hgπ hfg hgf,
    hq', herbrandQuotient_eq_one_of_finite f'' g'' hfg'' hgf'', one_mul]

-- Reproducible axiom audit (re-runs on every `lake build`). Standard-axioms-only.
#print axioms finite_acyclic_kernel_reduction

end Anabelian
