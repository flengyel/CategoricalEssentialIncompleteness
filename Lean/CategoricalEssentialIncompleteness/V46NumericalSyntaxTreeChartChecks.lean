/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalSyntaxTreeChart


/-! # Statement checks in `V46NumericalSyntaxTreeChartChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
universe u₃ u₄ v₃ v₄
/-- A typed spelling of the same algebra identity and full structure equation. -/
def TransportedAlgebraEquation {C : Type u₃} {D : Type u₄}
    [Category.{v₃} C] [Category.{v₄} D] (E : C ≌ D) {F : C ⥤ C} {G : D ⥤ D}
    (a : F ⋙ E.functor ≅ E.functor ⋙ G) (A : Endofunctor.Algebra F)
    (B : Endofunctor.Algebra G) : Prop :=
  B = AlgebraTransport.mappedAlgebra E a A ∧
    (AlgebraTransport.mappedAlgebra E a A).str = a.inv.app A.a ≫ E.functor.map A.str
variable (R : ℕ → NumericalTuples.Object) (N : ℕ)
example (C : NumericalTuples.Object) (n : ℕ) : (E.inverse.obj C).val.Evalb ![n] ↔
    ∃ x : NumericalTuples.Tuple C.dimension, x ∈ C.support ∧
      NumericalTuples.code C.dimension x = n := coefficient_label_iff C n
example (C : NumericalTuples.Object) (x : NumericalTuples.Point C) :
    (((wordPresentationIso (E.inverse.obj C)).hom).toFun
      ((E.counitIso.app C).inv.toFun x)).val = NumericalTuples.code C.dimension x.val :=
  coefficient_input_code C x
example : oneSortNormalized R N ≅ NumericalSyntax.oneSortAlgebra R N := normalizedOneSortChart R N
example : (oneSortNormalized R N).a = E.functor.obj (treePredicate R N) := oneSortNormalized_carrier R N
example : (oneSortNormalized R N).str = rawConstructorInput R N ≫
    E.functor.map (oneSortRaw R N).str.1 := normalized_raw_constructor R N
example : (treeObject R N).dimension = 1 := treeObject_dimension R N
example (n : ℕ) : n ∈ (treeObject R N).support ↔
    (treePredicate R N).val.Evalb ![n] := treeObject_mem R N n
example : (NumericalSyntax.oneSortAlgebra R N).a ≅ treeObject R N := treeChart R N
example : NumericalSyntax.oneSortAlgebra R N ≅ literalOneSort R N := literalOneSortIso R N
example : IsInitial (literalOneSort R N) := literalOneSortInitial R N
example : (SyntacticSyntax.constructorFunctor R N).map (literalOneSortIso R N).hom.f ≫
    (literalOneSort R N).str =
      (NumericalSyntax.oneSortAlgebra R N).str ≫ (literalOneSortIso R N).hom.f := tree_constructor R N
example : (SyntacticSyntax.constructorFunctor R N).map
      (wordPresentationIso (treePredicate R N)).hom ≫
    (literalOneSort R N).str = (oneSortNormalized R N).str ≫
      (wordPresentationIso (treePredicate R N)).hom := literal_raw_constructor R N
example (p q : SyntaxPolynomial NumericalTuples.Object) :
    TransportedAlgebraEquation (E.prod E)
      (SyntaxPolynomialTransport.jointIso E E.inverse.obj id
        (fun X => E.counitIso.app X) p q) (rawPairAlgebra p q) (mappedPair p q) :=
  ⟨rfl,mappedPair_constructor p q⟩

end CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
