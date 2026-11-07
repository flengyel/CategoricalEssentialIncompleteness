import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersAlgebraSplit
noncomputable section
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAlgebraSplit
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
example (F : C ⥤ C) (G : D ⥤ D) :
    Endofunctor.Algebra (F.prod G) ≌ Endofunctor.Algebra F × Endofunctor.Algebra G :=
  equivalence F G
example (F : C ⥤ C) (G : D ⥤ D) (A : Endofunctor.Algebra (F.prod G)) (hA : IsInitial A) :
    IsInitial ((split F G).obj A).1 := firstInitial F G A hA
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAlgebraSplit
