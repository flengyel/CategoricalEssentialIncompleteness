import CategoricalEssentialIncompleteness.V46NamedBooleanReflection

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedBooleanReflectionChecks
open ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (V : PredicateCategory T) (q : Obj T M (V ⨯ listObject T V)) (b : Bool) :
    (F T M).map (membershipArrow T V) q =
        (F T M).map (Two.constant (V ⨯ listObject T V) b) q ↔
      ConcreteNamedSubstitution.member
        ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) q).val
        ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) q).val =
          if b then 1 else 0 := membershipArrow_point_iff T M V q b
end CategoricalEssentialIncompleteness.V46.NamedBooleanReflectionChecks
