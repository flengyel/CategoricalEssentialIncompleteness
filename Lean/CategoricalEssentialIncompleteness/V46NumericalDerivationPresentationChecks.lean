/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation


/-! # Statement checks in `V46NumericalDerivationPresentationChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivation
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
example (i : Fin (N + 1)) (n : ℕ) :
    (codeEquivalence.inverse.obj
      (SyntacticDerivation.PolynomialComparison.coefficients R i.val)).val.Evalb ![n] ↔
      ∃ x : NumericalTuples.Tuple (R.instances i).dimension, x ∈ (R.instances i).support ∧
        NumericalTuples.code (R.instances i).dimension x = n := rule_label_iff R i n
example : ordinaryTree R ≅ literalOrdinaryTree R := ordinaryWordAlgebraIso R
example : (SyntacticDerivation.PolynomialComparison.ordinary R).map
      (ordinaryWordAlgebraIso R).hom.f ≫ (literalOrdinaryTree R).str =
    (ordinaryTree R).str ≫ (ordinaryWordAlgebraIso R).hom.f := ordinaryWord_constructor R
example : (codeObject R).dimension = 1 := codeObject_dimension R
example (d : ℕ) : (successfulCodes R).val.Evalb ![d] ↔
    ∃ z : ℕ, (SyntacticDerivation.SuccessCarrier.valueGraph (predicateValidator R)).val.Evalb ![d,z] :=
  successfulCodes_mem R d
example (d : ℕ) (hd : (successfulCodes R).val.Evalb ![d]) :
    (rawTreePredicate R).val.Evalb ![d] := successfulCodes_word R d hd
example (x : NumericalTuples.Point (codeObject R)) :
    ((codeWordInclusion R).toFun x).val = x.val := codeWordInclusion_value R x
example (x : NumericalTuples.Point (codeObject R)) :
    ((codeEncodedConclusion R).toFun x).val =
      NumericalTuples.code F.dimension ((codeConclusion R).toFun x).val := codeEncodedConclusion_value R x
example (x : NumericalTuples.Point (codeObject R)) :
    (SyntacticDerivation.SuccessCarrier.valueGraph (predicateValidator R)).val.Evalb (M := ℕ)
      ![x.val,NumericalTuples.code F.dimension ((codeConclusion R).toFun x).val] := codeConclusion_graph R x
example : IsPullback (codeTreeInclusion R) (codeConclusion R) (validatorFold R).f
    (coprod.inr : F ⟶ OptionSyntax.obj F) := code_isPullback R
example : IsInitial (codeAlgebra R) := codeInitial R
example : codeAlgebra R ≅ derivationAlgebra R := codeAlgebraIso R
example : R.inference.map (codeAlgebraIso R).hom.f ≫ (derivationAlgebra R).str =
    (codeAlgebra R).str ≫ (codeAlgebraIso R).hom.f := code_constructor_comparison R
example : (codeAlgebraIso R).hom.f.left ≫ conclusion R = codeConclusion R :=
  code_conclusion_comparison R
example : (codeAlgebra R).str.left ≫ codeTreeInclusion R =
    SyntacticDerivation.InputGeometry.forget R (codeAlgebra R).a ≫
      (SyntacticDerivation.PolynomialComparison.ordinary R).map (codeTreeInclusion R) ≫ (ordinaryTree R).str :=
  code_constructor_tree R
example (B : Endofunctor.Algebra R.inference) :
    (codeFold R B).f.left ≫ B.a.hom = codeConclusion R := codeFold_conclusion R B
example (B : Endofunctor.Algebra R.inference) :
    (codeAlgebra R).str ≫ (codeFold R B).f = R.inference.map (codeFold R B).f ≫ B.str :=
  codeFold_constructor R B
example (B : Endofunctor.Algebra R.inference) (f : codeAlgebra R ⟶ B) :
    f = codeFold R B := codeFold_unique R B f
end CategoricalEssentialIncompleteness.V46.NumericalDerivation
