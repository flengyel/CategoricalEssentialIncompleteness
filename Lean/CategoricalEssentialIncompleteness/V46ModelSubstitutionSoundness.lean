/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ModelLogicalSoundness
import CategoricalEssentialIncompleteness.V46LogicalSchemes

/-! # Instantiation and equality through the actual admissibility diagrams -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w k
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ModelSubstitutionSoundness
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable (G : C ⥤ Type w) {V : C} {σ π : ℕ → C} {d : ℕ}
variable (S : CategoricalSyntax V σ π d) {K : Type k}
variable (name : G.obj V → ℕ)
variable (eval : G.obj S.algebra.a.1 → (ℕ → K) → K)
variable (P : G.obj S.algebra.a.2 → (ℕ → K) → Prop)
variable (hsub : ∀ (a : G.obj S.admissibleSubstitution) (ρ : ℕ → K),
  P (G.map S.formulaSubstitution a) ρ ↔
    P (G.map prod.fst (G.map S.admissibleInclusion a))
      (Function.update ρ
        (name (G.map prod.fst (G.map prod.snd (G.map S.admissibleInclusion a))))
        (eval (G.map prod.snd (G.map prod.snd (G.map S.admissibleInclusion a))) ρ)))

include hsub in
/-- A commutative admissibility square identifies the substitution
coordinates, even when the pullback carrier uses a different code. -/
theorem substitute_at_input {A : C} (f : A ⟶ S.algebra.a.2 ⨯ S.substitutionParameters)
    (a : A ⟶ S.admissibleSubstitution) (h : f = a ≫ S.admissibleInclusion)
    (z : G.obj A) (ρ : ℕ → K) :
    P (G.map (a ≫ S.formulaSubstitution) z) ρ ↔
      P (G.map prod.fst (G.map f z))
        (Function.update ρ (name (G.map prod.fst (G.map prod.snd (G.map f z))))
          (eval (G.map prod.snd (G.map prod.snd (G.map f z))) ρ)) := by
  rw [h,Functor.map_comp_apply,Functor.map_comp_apply]
  exact hsub _ ρ

variable (himp : ∀ (z : G.obj (S.algebra.a.2 ⨯ S.algebra.a.2)) (ρ : ℕ → K),
  P (G.map S.implicationConstructor z) ρ ↔
    (P (G.map prod.fst z) ρ → P (G.map prod.snd z) ρ))
variable (hall : ∀ (z : G.obj (V ⨯ S.algebra.a.2)) (ρ : ℕ → K),
  P (G.map S.quantifierConstructor z) ρ ↔
    ∀ a : K, P (G.map prod.snd z)
      (Function.update ρ (name (G.map prod.fst z)) a))
variable (heq : ∀ (z : G.obj (S.algebra.a.1 ⨯ S.algebra.a.1)) (ρ : ℕ → K),
  P (G.map S.equalityConstructor z) ρ ↔
    eval (G.map prod.fst z) ρ = eval (G.map prod.snd z) ρ)

include hsub himp hall in
theorem valid_instantiation (z : G.obj S.instantiationParameters) :
    ∀ ρ : ℕ → K, P (G.map S.hilbertInstantiation z) ρ := by
  dsimp only [CategoricalSyntax.substitutionParameters] at *
  intro ρ
  simp only [CategoricalSyntax.hilbertInstantiation,Functor.map_comp_apply,
    himp,hall,ModelLogicalSoundness.map_lift_fst,ModelLogicalSoundness.map_lift_snd]
  intro h
  have hs := substitute_at_input G S name eval P hsub
    (S.instantiationInclusion ≫ S.instantiationInput) S.instantiationAdmissible
    S.instantiation_admissible z ρ
  rw [Functor.map_comp_apply] at hs
  apply hs.mpr
  simp only [CategoricalSyntax.instantiationInput,Functor.map_comp_apply,
    ModelLogicalSoundness.map_lift_fst]
  erw [ModelLogicalSoundness.map_lift_snd,ModelLogicalSoundness.map_lift_fst,
    ModelLogicalSoundness.map_lift_snd]
  simpa only [Functor.map_comp_apply] using
      h (eval (G.map prod.snd (G.map prod.snd (G.map S.instantiationInclusion z))) ρ)

include hsub himp heq in
theorem valid_equality (z : G.obj S.equalitySchemeParameters) :
    ∀ ρ : ℕ → K, P (G.map S.hilbertEquality z) ρ := by
  dsimp only [CategoricalSyntax.substitutionParameters,CategoricalSyntax.equalitySchemeBase] at *
  intro ρ
  simp only [CategoricalSyntax.hilbertEquality,Functor.map_comp_apply,
    himp,ModelLogicalSoundness.map_lift_fst,ModelLogicalSoundness.map_lift_snd]
  intro hEq hφ
  rw [heq] at hEq
  have hu := substitute_at_input G S name eval P hsub
    (S.equalitySchemeInclusion ≫ S.equalityFirstInput) S.equalityFirstAdmissible
    S.equality_first_admissible z ρ
  have ht := substitute_at_input G S name eval P hsub
    (S.equalitySchemeInclusion ≫ S.equalitySecondInput) S.equalitySecondAdmissible
    S.equality_second_admissible z ρ
  rw [Functor.map_comp_apply] at hu ht
  apply ht.mpr
  have hp := hu.mp hφ
  simp only [CategoricalSyntax.equalityFirstInput,Functor.map_comp_apply,
    ModelLogicalSoundness.map_lift_fst] at hp
  erw [ModelLogicalSoundness.map_lift_snd,ModelLogicalSoundness.map_lift_fst,
    ModelLogicalSoundness.map_lift_snd] at hp
  simp only [Functor.map_comp_apply] at hp
  simp only [CategoricalSyntax.equalitySecondInput,Functor.map_comp_apply,
    ModelLogicalSoundness.map_lift_fst]
  erw [ModelLogicalSoundness.map_lift_snd,ModelLogicalSoundness.map_lift_fst,
    ModelLogicalSoundness.map_lift_snd]
  simpa only [Functor.map_comp_apply,hEq] using hp

end CategoricalEssentialIncompleteness.V46.ModelSubstitutionSoundness
