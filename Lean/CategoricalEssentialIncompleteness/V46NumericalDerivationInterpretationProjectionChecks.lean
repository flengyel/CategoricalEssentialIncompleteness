/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationProjection


/-! # Statement checks in `V46NumericalDerivationInterpretationProjectionChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Projection
open SyntacticSyntax
variable (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ)
  (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit))
example : K.map (constructorProjection σ N A) ≫ (oneSortInputIso σ N A.a.1).hom =
    (constructorInputIso σ N A.a).hom ≫
      constructorProjection (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A) := projection_square σ N A
example : (mappedOneSortAlgebra σ N (projectedConstructorAlgebra σ N A)).str =
    (projectedConstructorAlgebra (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A)).str :=
  projected_mapping_str σ N A
example : (projectedMappingIso σ N A).hom.f = 𝟙 (K.obj A.a.1) := rfl
example : (constructorFunctor (fun n => K.obj (σ n)) N).map (projectedMappingIso σ N A).hom.f ≫
    (projectedConstructorAlgebra (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A)).str =
  (mappedOneSortAlgebra σ N (projectedConstructorAlgebra σ N A)).str ≫
    (projectedMappingIso σ N A).hom.f := (projectedMappingIso σ N A).hom.h
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Projection
