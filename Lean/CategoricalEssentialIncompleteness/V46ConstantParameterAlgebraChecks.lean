/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedSubstitutionAlgebra

/-! # Independent statements for changing parameters of algebra folds -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open ConstantParameterAlgebra SyntaxParameterChange

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P Q : D} (r : P ⟶ Q) (X : D × D)

example (p : SyntaxPolynomial D) {Y : D}
    (s : (p.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y) :
    polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫ s =
      (Over.map r).map (component r X p s) ≫ baseMap r Y := component_commutes r X p s

example (p : SyntaxPolynomial D) {Y : D} (f : p.eval.obj X ⟶ Y) :
    component r X p (SyntaxPolynomial.parameterComparison Q X p ≫
      (constantFamilyFunctor Q).map f) =
        SyntaxPolynomial.parameterComparison P X p ≫ (constantFamilyFunctor P).map f :=
  component_constant r X p f

example (p : SyntaxPolynomial D) {Y : D} (f : Q ⨯ p.eval.obj X ⟶ Y) :
    component r X p (SyntaxPolynomial.parameterComparison Q X p ≫ parameterHom f) =
      SyntaxPolynomial.parameterComparison P X p ≫ parameterHom (prod.map r (𝟙 _) ≫ f) :=
  component_parameter r X p f

example {V : D} {σ π : ℕ → D} {n : ℕ} (S : CategoricalSyntax V σ π n)
    (B : Data (SyntaxPolynomial.termExpression V σ n)
      (SyntaxPolynomial.formulaExpression V π n) Q X) :
    ((Over.map r).map (S.foldWithParameters P (B.reindex r).algebra).1 ≫ baseMap r X.1,
      (Over.map r).map (S.foldWithParameters P (B.reindex r).algebra).2 ≫ baseMap r X.2) =
        S.crossParameterFold r B.algebra := fold_comparison r S X B

example {V X : D} (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
    {R : D} (r : R ⟶ S.substitutionParameters) :
    (ParameterizedSubstitution.fold S r).2.left ≫ prod.snd =
      prod.map r (𝟙 S.algebra.a.2) ≫ S.substitutionFold.2.left ≫ prod.snd :=
  ParameterizedSubstitution.formula_value S r

#print axioms ConstantParameterAlgebra.Data.algebra
#print axioms ConstantParameterAlgebra.component
#print axioms ConstantParameterAlgebra.component_commutes
#print axioms ConstantParameterAlgebra.Data.reindex
#print axioms ConstantParameterAlgebra.pushHom
#print axioms ConstantParameterAlgebra.pushHom_commutes
#print axioms ConstantParameterAlgebra.fold_comparison
#print axioms ConstantParameterAlgebra.component_value
#print axioms ConstantParameterAlgebra.component_precomp
#print axioms ConstantParameterAlgebra.component_inl
#print axioms ConstantParameterAlgebra.component_inr
#print axioms ConstantParameterAlgebra.component_coprod
#print axioms ConstantParameterAlgebra.component_constant
#print axioms ConstantParameterAlgebra.component_parameter
#print axioms ParameterizedSubstitution.data
#print axioms ParameterizedSubstitution.algebra
#print axioms ParameterizedSubstitution.fold
#print axioms ParameterizedSubstitution.formula_value
#print axioms ParameterizedSubstitution.formula_structure
