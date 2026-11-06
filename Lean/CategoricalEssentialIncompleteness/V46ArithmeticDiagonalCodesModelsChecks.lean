import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesModels

/-! # Exact statement checks for the arithmetic diagonal construction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.ModelsChecks
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example : diagonalArrow = sourceDiagonal := diagonalIndex_represents
example : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
    a0 = setIdem {x : M | alpha.val.Evalb ![x]} :=
  model_a0 M
example : (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
    a1 = setIdem {x : M | beta.val.Evalb ![x]} :=
  model_a1 M
example (x y : M) : y ∈ ((SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceDiagonal x : Part M) ↔
    UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] := mem_sourceDiagonal M x y
end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.ModelsChecks
