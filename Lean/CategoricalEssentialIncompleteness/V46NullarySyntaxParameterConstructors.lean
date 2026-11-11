/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxInterpretation
public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebra
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentity
public import CategoricalEssentialIncompleteness.V46SliceProductCoordinates

/-! # Constructors of the nullary-predicate syntax in a parameter slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)

abbrev parameterAlgebra := SyntaxPolynomial.algebraWithParameters
  (SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0)
  (SyntaxPolynomial.formulaExpression V (fun _ => X) 0) S.algebra P

theorem parameter_variable : NullarySyntaxAlgebra.variableConstructor (parameterAlgebra S P) =
    (constantFamilyFunctor P).map S.variableConstructor := by
  change coprod.inl ≫ (parameterAlgebra S P).str.1 = _
  rw [S.term_parameter_structure P]
  exact coprod.inl_desc _ _

theorem parameter_equality : NullarySyntaxAlgebra.equalityConstructor (parameterAlgebra S P) =
    constantProductComparison P S.algebra.a.1 S.algebra.a.1 ≫
      (constantFamilyFunctor P).map S.equalityConstructor := by
  change coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫
    (parameterAlgebra S P).str.2 = _
  rw [S.formula_parameter_structure P]
  dsimp only [parameterAlgebra, SyntaxPolynomial.algebraWithParameters,
    SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst, CategoryTheory.Prod.snd]
  simpa only [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.power,
    SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst,
    coprod.inl_desc, prod.map_id_id, Category.assoc] using
    Category.id_comp (constantProductComparison P S.algebra.a.1 S.algebra.a.1 ≫
      (constantFamilyFunctor P).map S.equalityConstructor)

theorem parameter_negation : NullarySyntaxAlgebra.negationConstructor (parameterAlgebra S P) =
    (constantFamilyFunctor P).map S.negationConstructor := by
  change coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ (parameterAlgebra S P).str.2 = _
  rw [S.formula_parameter_structure P]
  simp only [coprod.inl_desc, coprod.inr_desc]

theorem parameter_implication :
    NullarySyntaxAlgebra.implicationConstructor (parameterAlgebra S P) =
      constantProductComparison P S.algebra.a.2 S.algebra.a.2 ≫
        (constantFamilyFunctor P).map S.implicationConstructor := by
  change coprod.inr ≫ coprod.inl ≫ (parameterAlgebra S P).str.2 = _
  rw [S.formula_parameter_structure P]
  dsimp only [parameterAlgebra, SyntaxPolynomial.algebraWithParameters,
    SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst, CategoryTheory.Prod.snd]
  simpa only [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.power,
    SyntaxPolynomial.withParameters, SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor, CategoryTheory.Prod.snd,
    coprod.inl_desc, coprod.inr_desc, prod.map_id_id, Category.assoc] using
    Category.id_comp (constantProductComparison P S.algebra.a.2 S.algebra.a.2 ≫
      (constantFamilyFunctor P).map S.implicationConstructor)

theorem parameter_quantifier :
    NullarySyntaxAlgebra.quantifierConstructor (parameterAlgebra S P) =
      constantProductComparison P V S.algebra.a.2 ≫
        (constantFamilyFunctor P).map S.quantifierConstructor := by
  change coprod.inr ≫ (parameterAlgebra S P).str.2 = _
  rw [S.formula_parameter_structure P]
  dsimp only [parameterAlgebra, SyntaxPolynomial.algebraWithParameters,
    SyntaxPolynomial.productFunctor, CategoryTheory.Prod.fst, CategoryTheory.Prod.snd]
  simpa only [SyntaxPolynomial.parameterComparison, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, CategoryTheory.Prod.snd,
    Functor.const_obj_obj, Functor.const_obj_map,
    coprod.inr_desc, prod.map_id_id, Category.assoc] using
    Category.id_comp (constantProductComparison P V S.algebra.a.2 ≫
      (constantFamilyFunctor P).map S.quantifierConstructor)

theorem parameter_atom : NullarySyntaxAlgebra.atomConstructor (parameterAlgebra S P) =
    (constantFamilyFunctor P).map (atomFormula S) := by
  change prod.lift (𝟙 (constantFamily P X)) (terminal.from (constantFamily P X)) ≫
    coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ (parameterAlgebra S P).str.2 = _
  rw [S.formula_parameter_structure P]
  simp only [coprod.inl_desc, coprod.inr_desc]
  apply constantFamily_hom_ext
  simp [atomFormula, constantFamilyFunctor, constantFamily, SyntaxPolynomial.parameterComparison,
    SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, constantProductComparison,
    constantUnitComparison, Category.assoc, prod.comp_lift_assoc, prod.lift_map_assoc]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
