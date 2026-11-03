import CategoricalEssentialIncompleteness.V46SplitExtension

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)

universe v₁ v₂ u₁ u₂

namespace CategoricalEssentialIncompleteness.LocalConnectedness.V46.StatementChecks

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
  [RestrictionCategory R] [RestrictionCategory A]
  [Ranges R] [Ranges A]
  [CoprodStruct R] [CategoryTheory.HasCoproducts R]
  [CoprodStruct A] [CategoryTheory.HasCoproducts A]
  [HasZeroMorphisms R] [HasZeroMorphisms A]
  [RestrictionCoproducts R] [RestrictionCoproducts A]

example (F : RangeFunctor R A) [Splits A] : RangeFunctor (SplitObject R) A :=
  splitRangeFunctor F

example (F : RangeFunctor R A) [Splits A] :
    splittingInclusion (C := R) ⋙ (splitRangeFunctor F).toFunctor = F.toFunctor :=
  splitRangeFunctor_inclusion F

end CategoricalEssentialIncompleteness.LocalConnectedness.V46.StatementChecks
