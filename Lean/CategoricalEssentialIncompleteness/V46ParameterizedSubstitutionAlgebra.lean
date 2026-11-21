/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantParameterConstructors

/-! # The substitution fold with an additional parameter -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ParameterizedSubstitution
open ConstantParameterAlgebra SyntaxParameterChange
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)

def data : Data (SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0)
    (SyntaxPolynomial.formulaExpression V (fun _ => X) 0)
    S.substitutionParameters S.substitutionCarriers where
  term := S.substitutionAlgebra.str.1
  formula := S.substitutionAlgebra.str.2

theorem data_algebra : (data S).algebra = S.substitutionAlgebra := rfl

variable {R : D} (r : R ⟶ S.substitutionParameters)

def algebra := ((data S).reindex r).algebra

def fold := S.foldWithParameters R (algebra S r)

/-- Adding a parameter changes neither the original formula nor its
computed Option result. The complete substitution state is retained. -/
theorem formula_value :
    (fold S r).2.left ≫ prod.snd =
      prod.map r (𝟙 S.algebra.a.2) ≫ S.substitutionFold.2.left ≫ prod.snd := by
  have hh : (Over.map r).map (fold S r).2 ≫ baseMap r S.substitutionCarriers.2 =
      baseMap r S.algebra.a.2 ≫ S.substitutionFold.2 :=
    congrArg Prod.snd (fold_comparison r S S.substitutionCarriers (data S))
  have h := congrArg (fun f => f.left ≫ prod.snd) hh
  simpa only [Over.comp_left, Over.map_map_left, baseMap, Over.homMk_left,
    Category.assoc, prod.map_snd, Category.comp_id] using h

/-- Formula constructors compute the same substitution operations, with
the substitution parameters read through r. -/
theorem formula_structure :
    (algebra S r).str.2 =
      coprod.desc
        (coprod.desc
          (coprod.desc
            (coprod.desc
              (SyntaxPolynomial.parameterComparison R S.substitutionCarriers
                (SyntaxPolynomial.power .term 2) ≫
                  (constantFamilyFunctor R).map S.equalitySubstitutionPair)
              (SyntaxPolynomial.parameterComparison R S.substitutionCarriers
                (SyntaxPolynomial.constructors (fun _ => X) 0) ≫
                  (constantFamilyFunctor R).map S.relationSubstitutionPair))
            ((constantFamilyFunctor R).map S.negationSubstitutionPair))
          (SyntaxPolynomial.parameterComparison R S.substitutionCarriers
            (SyntaxPolynomial.power .formula 2) ≫
              (constantFamilyFunctor R).map S.implicationSubstitutionPair))
        (SyntaxPolynomial.parameterComparison R S.substitutionCarriers
          (.product (.coefficient V) .formula) ≫
            parameterHom (prod.map r (𝟙 _) ≫ S.quantifierSubstitutionPair)) := by
  have hn : component r S.substitutionCarriers .formula
      ((constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair) =
        (constantFamilyFunctor R).map S.negationSubstitutionPair := by
    simpa only [SyntaxPolynomial.parameterComparison, Category.id_comp] using
      component_constant r S.substitutionCarriers .formula S.negationSubstitutionPair
  change component r S.substitutionCarriers
    (SyntaxPolynomial.formulaExpression V (fun _ => X) 0) S.substitutionAlgebra.str.2 = _
  dsimp only [CategoricalSyntax.substitutionAlgebra, SyntaxPolynomial.formulaExpression]
  simp only [component_coprod, component_constant, component_parameter, hn]
  dsimp only [SyntaxPolynomial.eval, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.productFunctor, CategoryTheory.Prod.snd]
  rfl

end CategoricalEssentialIncompleteness.V46.ParameterizedSubstitution
