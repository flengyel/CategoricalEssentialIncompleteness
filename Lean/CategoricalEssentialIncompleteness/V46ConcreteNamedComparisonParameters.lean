/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Product charts for the numerical substitution parameters -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Both the inner parameter product and the outer constant-family product are passed
through their categorical comparisons. -/
def parameterInput (V R C : PredicateCategory T) :
    @Quiver.Hom (PredicateCategory T) inferInstance ((V ⨯ R) ⨯ C)
      (productCarrier (productCarrier V R) C) :=
  prod.map (toRawProduct T V R) (𝟙 C) ≫
    toRawProduct T (productCarrier V R) C

/-- Public substitution takes word first, so its parameter chart also
includes the specified product braiding. -/
def publicParameterInput (V R C : PredicateCategory T) :
    @Quiver.Hom (PredicateCategory T) inferInstance (C ⨯ (V ⨯ R))
      (productCarrier (productCarrier V R) C) :=
  (prod.braiding C (V ⨯ R)).hom ≫ parameterInput T V R C

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem parameterInput_value (V R C : PredicateCategory T) (q : Obj T M ((V ⨯ R) ⨯ C)) :
    ((F T M).map (parameterInput T V R C) q).val =
      Arithmetic.pair
        (Arithmetic.pair
          ((F T M).map (prod.fst : V ⨯ R ⟶ V)
            ((F T M).map (prod.fst : (V ⨯ R) ⨯ C ⟶ V ⨯ R) q)).val
          ((F T M).map (prod.snd : V ⨯ R ⟶ R)
            ((F T M).map (prod.fst : (V ⨯ R) ⨯ C ⟶ V ⨯ R) q)).val)
        ((F T M).map (prod.snd : (V ⨯ R) ⨯ C ⟶ C) q).val := by
  change ((F T M).map (prod.map (toRawProduct T V R) (𝟙 C) ≫
    toRawProduct T (productCarrier V R) C) q).val = _
  rw [Functor.map_comp_apply]
  erw [toRawProduct_value T M,model_map_fst T M,model_map_snd T M]
  erw [toRawProduct_value T M,Functor.map_id_apply]

theorem publicParameterInput_value (V R C : PredicateCategory T) (q : Obj T M (C ⨯ (V ⨯ R))) :
    ((F T M).map (publicParameterInput T V R C) q).val =
      Arithmetic.pair
        (Arithmetic.pair
          ((F T M).map (prod.fst : V ⨯ R ⟶ V)
            ((F T M).map (prod.snd : C ⨯ (V ⨯ R) ⟶ V ⨯ R) q)).val
          ((F T M).map (prod.snd : V ⨯ R ⟶ R)
            ((F T M).map (prod.snd : C ⨯ (V ⨯ R) ⟶ V ⨯ R) q)).val)
        ((F T M).map (prod.fst : C ⨯ (V ⨯ R) ⟶ C) q).val := by
  change ((F T M).map (prod.lift prod.snd prod.fst ≫ parameterInput T V R C) q).val = _
  rw [Functor.map_comp_apply]
  erw [parameterInput_value T M V R C,model_lift_fst T M,model_lift_snd T M]

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
