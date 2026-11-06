/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonTermCommutation
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonFormulaCommutation

/-! # The numerical state traversal is the actual stable substitution fold -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "A₀" => projectionSourceAlgebra T V V σ π d

theorem computedTerm_commutes :
    ((SyntaxPolynomial.termExpression V σ d).withParameters P).eval.map (computedStatePair T V σ π d) ≫
      (S).substitutionAlgebra.str.1 = (A₀).str.1 ≫ (computedStatePair T V σ π d).1 := by
  apply Over.OverMorphism.ext
  change (((SyntaxPolynomial.termExpression V σ d).withParameters P).eval.map
      (computedStatePair T V σ π d)).left ≫ (S).substitutionAlgebra.str.1.left =
        (A₀).str.1.left ≫ (computedStatePair T V σ π d).1.left
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  rw [Functor.map_comp,Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  exact computedTerm_commutes_model T V σ π d M q

theorem computedFormula_commutes :
    ((SyntaxPolynomial.formulaExpression V π d).withParameters P).eval.map (computedStatePair T V σ π d) ≫
      (S).substitutionAlgebra.str.2 = (A₀).str.2 ≫ (computedStatePair T V σ π d).2 := by
  apply Over.OverMorphism.ext
  change (((SyntaxPolynomial.formulaExpression V π d).withParameters P).eval.map
      (computedStatePair T V σ π d)).left ≫ (S).substitutionAlgebra.str.2.left =
        (A₀).str.2.left ≫ (computedStatePair T V σ π d).2.left
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  rw [Functor.map_comp,Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  exact computedFormula_commutes_model T V σ π d M q

/-- Every constructor equation has been proved before this actual
algebra morphism is formed; no commutation or initiality field is supplied. -/
def computedSubstitutionHom : (A₀) ⟶ (S).substitutionAlgebra where
  f := computedStatePair T V σ π d
  h := Prod.ext (computedTerm_commutes T V σ π d) (computedFormula_commutes T V σ π d)

theorem computedStatePair_eq_fold : computedStatePair T V σ π d = (S).substitutionFold :=
  (S).substitutionFold_unique (computedStatePair T V σ π d) (computedSubstitutionHom T V σ π d).h

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
