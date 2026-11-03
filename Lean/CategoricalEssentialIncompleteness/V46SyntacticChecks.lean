import CategoricalEssentialIncompleteness.V46SyntacticExtension

/-! Explicit types for the syntactic complementary-conditional comparison
and its preservation under theory extension. -/

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory
open PCategoryStruct (nearProd)
open CategoricalEssentialIncompleteness.LocalConnectedness

variable (T T' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [T ⪯ T']

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (τ : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T)
    (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : omegaObject T ≅ coprod (omegaObject T) (omegaObject T)) :
    Inseparable (diagonal0 τ b) (diagonal1 τ b) :=
  SyntacticModel.syntactic_pair_inseparable_v46_of_model T M τ hτ b

example (hT : Consistent T)
    (τ : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T)
    (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : omegaObject T ≅ coprod (omegaObject T) (omegaObject T)) :
    Inseparable (diagonal0 τ b) (diagonal1 τ b) :=
  SyntacticModel.syntactic_pair_inseparable_v46 T hT τ hτ b

example (X Y : CodedProgramCategory T) :
    Function.Surjective ((SyntacticExtension.functor T T').map (X := X) (Y := Y)) :=
  SyntacticExtension.map_surjective T T' X Y

example {W X Y : CodedProgramCategory T}
    (τ : nearProd W X ⟶ Y) (hτ : RecursionCategory.IsTuringMorphism τ) :
    RecursionCategory.IsTuringMorphism ((SyntacticExtension.functor T T').map τ) :=
  SyntacticExtension.map_isTuringMorphism T T' τ hτ

example (hT' : Consistent T')
    (τ : nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T)
    (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : omegaObject T ≅ coprod (omegaObject T) (omegaObject T)) :
    Inseparable ((SyntacticExtension.rangeFunctor T T').mapIdem (diagonal0 τ b))
      ((SyntacticExtension.rangeFunctor T T').mapIdem (diagonal1 τ b)) :=
  SyntacticExtension.extension_arbitrary_pair_inseparable_v46 T T' hT' τ hτ b
