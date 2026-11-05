import CategoricalEssentialIncompleteness.V46PrintedObjectCodingModels

/-! Recursive coding and the actual conjugated model graphs. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition FailureOfComposition.CodedObjectMembership
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 PrintedObjectCoding
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (x : M) : value M .omega x = x := rfl
example (Q R : STObjectCode) (x : SyntacticModel.interpretedType M Q)
    (y : SyntacticModel.interpretedType M R) :
    value M (.product Q R) (x, y) =
      ExponentialPairing.code (value M Q x) (value M R y) := rfl
example (Q R : STObjectCode) (x : SyntacticModel.interpretedType M Q) :
    value M (.coproduct Q R) (.inl x) = 2 * value M Q x := rfl
example (Q R : STObjectCode) (x : SyntacticModel.interpretedType M R) :
    value M (.coproduct Q R) (.inr x) = 2 * value M R x + 1 := rfl

example (Q : STObjectCode) : Function.Bijective (value M Q) := value_bijective T M Q
example (Q : STObjectCode) : SyntacticModel.interpretedType M Q ≃ M := valueEquiv T M Q

example (Q : STObjectCode) (x : SyntacticModel.interpretedType M Q) :
    SyntacticModel.programRelation T M (isoToOmega T Q).hom.val
      (SyntacticModel.codingEquiv T M Q x).val (value M Q x) := value_model T M Q x

example {Q R : CodedProgramCategory T} (f : Q ⟶ R)
    (x : SyntacticModel.interpretedType M (objectCode Q))
    (y : SyntacticModel.interpretedType M (objectCode R)) :
    SyntacticModel.programRelation T M ((comparison T).map f).hom.val
        (value M (objectCode Q) x) (value M (objectCode R) y) ↔
      SyntacticModel.programRelation T M f.val
        (SyntacticModel.codingEquiv T M (objectCode Q) x).val
        (SyntacticModel.codingEquiv T M (objectCode R) y).val := comparison_model T M f x y
