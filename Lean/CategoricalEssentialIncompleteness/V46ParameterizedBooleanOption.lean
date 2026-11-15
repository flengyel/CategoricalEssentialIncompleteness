/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedOptionConstructors
public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanEquations

/-! # Option-valued Boolean computations at a shared support parameter -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
variable {W : D}

theorem evaluate_precomp (p : W ⟶ P) (f : W ⟶ S.algebra.a.2) {U : D} (k : U ⟶ W) :
    k ≫ evaluate S P d p f = evaluate S P d (k ≫ p) (k ≫ f) := by
  simp only [evaluate, prod.comp_lift_assoc]

theorem option_negation_value (p : W ⟶ P) (a : W ⟶ OptionSyntax.obj S.algebra.a.2) :
    ParameterizedOption.map (value S P d) p (a ≫ OptionSyntax.map S.negationConstructor) =
      ParameterizedOption.map (value S P d) p a ≫
        OptionSyntax.map (Two.unary Bool.not (𝟙 (Two D))) := by
  apply ParameterizedOption.map_natural_value
  intro A p y
  simpa only [Two.unary, Category.id_comp, evaluate, Category.assoc] using
    evaluate_negation S P d p y

theorem option_implication_value (p : W ⟶ P)
    (a b : W ⟶ OptionSyntax.obj S.algebra.a.2) :
    ParameterizedOption.map (value S P d) p
        (prod.lift a b ≫ OptionSyntax.binary S.implicationConstructor) =
      prod.lift (ParameterizedOption.map (value S P d) p a)
          (ParameterizedOption.map (value S P d) p b) ≫
        OptionSyntax.binary (Two.binaryArrow NullaryBooleanValuation.implies) := by
  apply ParameterizedOption.map_binary
  intro A p y z
  exact evaluate_implication S P d p y z

theorem option_quantifier_value (p : W ⟶ P) (v : W ⟶ V)
    (a : W ⟶ OptionSyntax.obj S.algebra.a.2) :
    ParameterizedOption.map (value S P d) p
      (prod.lift v a ≫ OptionSyntax.coefficient S.quantifierConstructor) =
        ParameterizedOption.map (value S P d) p a := by
  apply ParameterizedOption.map_ignore_coefficient
  intro A p v y
  exact evaluate_quantifier S P d p v y

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
