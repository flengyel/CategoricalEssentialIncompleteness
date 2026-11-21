/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanValuation
public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebraHom
public import CategoricalEssentialIncompleteness.V46NullarySyntaxParameterConstructors

/-! # Boolean formula valuations with an internal parameter

The atom assignment may vary with the parameter. The formula valuation is one
morphism, obtained from the stable initial syntax algebra. Its values lie in the
constant family of the Boolean object of the base category.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))

/-- Constant Boolean values on an arbitrary family over the parameter. -/
def constant (W : Over P) (b : Bool) : W ⟶ constantFamily P (Two D) :=
  Over.homMk (prod.lift W.hom (Two.constant W.left b)) (by simp [constantFamily])

@[simp] theorem constant_value (W : Over P) (b : Bool) :
    (constant P W b).left ≫ prod.snd = Two.constant W.left b := by
  simp [constant]

@[reassoc (attr := simp)] theorem comp_constant {W Z : Over P} (f : W ⟶ Z) (b : Bool) :
    f ≫ constant P Z b = constant P W b := by
  apply constantFamily_hom_ext
  simp [constant, Two.comp_constant]

/-- The no-function term carrier is terminal. The formula operations are
Boolean operations, with the supplied parameter-dependent atom assignment. -/
def algebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters P)
    ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters P)) where
  a := (⊤_ (Over P), constantFamily P (Two D))
  str := (terminal.from _,
    coprod.desc
      (coprod.desc
        (coprod.desc
          (coprod.desc (constant P _ true) (prod.fst ≫ d))
          ((constantFamilyFunctor P).map (Two.unary Bool.not (𝟙 (Two D)))))
        (constantProductComparison P (Two D) (Two D) ≫
          (constantFamilyFunctor P).map (Two.binaryArrow NullaryBooleanValuation.implies)))
      prod.snd)

def valuation : constantFamily P S.algebra.a.2 ⟶ constantFamily P (Two D) :=
  (S.foldWithParameters P (algebra (V := V) P d)).2

/-- Underlying value morphism, retaining the internal parameter as input. -/
def value : P ⨯ S.algebra.a.2 ⟶ Two D := (valuation S P d).left ≫ prod.snd

@[reassoc] theorem equality_value :
    constantProductComparison P S.algebra.a.1 S.algebra.a.1 ≫
      (constantFamilyFunctor P).map S.equalityConstructor ≫ valuation S P d =
        constant P _ true := by
  have h := NullarySyntaxAlgebra.hom_equality ((S.stable P).to (algebra (V := V) P d))
  change NullarySyntaxAlgebra.equalityConstructor (NullaryInterpretation.parameterAlgebra S P) ≫
      valuation S P d = _ at h
  rw [NullaryInterpretation.parameter_equality S P] at h
  have hb : NullarySyntaxAlgebra.equalityConstructor (algebra (V := V) P d) =
      constant P _ true := by
    simp [NullarySyntaxAlgebra.equalityConstructor, algebra,
      SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.power, SyntaxPolynomial.constructors,
      SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor]
  rw [hb, comp_constant] at h
  simpa only [Category.assoc, NullaryInterpretation.parameterAlgebra,
    SyntaxPolynomial.algebraWithParameters, valuation, CategoricalSyntax.foldWithParameters] using h

@[reassoc] theorem atom_value :
    (constantFamilyFunctor P).map (NullaryInterpretation.atomFormula S) ≫
      valuation S P d = d := by
  have h := NullarySyntaxAlgebra.hom_atom ((S.stable P).to (algebra (V := V) P d))
  rw [NullaryInterpretation.parameter_atom S P] at h
  have hb : NullarySyntaxAlgebra.atomConstructor (algebra (V := V) P d) = d := by
    simp [NullarySyntaxAlgebra.atomConstructor, algebra,
      SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.power, SyntaxPolynomial.constructors,
      SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor]
  exact h.trans hb

@[reassoc] theorem negation_value :
    (constantFamilyFunctor P).map S.negationConstructor ≫ valuation S P d =
      valuation S P d ≫
        (constantFamilyFunctor P).map (Two.unary Bool.not (𝟙 (Two D))) := by
  have h := NullarySyntaxAlgebra.hom_negation ((S.stable P).to (algebra (V := V) P d))
  rw [NullaryInterpretation.parameter_negation S P] at h
  have hb : NullarySyntaxAlgebra.negationConstructor (algebra (V := V) P d) =
      (constantFamilyFunctor P).map (Two.unary Bool.not (𝟙 (Two D))) := by
    simp [NullarySyntaxAlgebra.negationConstructor, algebra,
      SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.power, SyntaxPolynomial.constructors,
      SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor]
  exact h.trans (congrArg (fun k => valuation S P d ≫ k) hb)

@[reassoc] theorem implication_value :
    constantProductComparison P S.algebra.a.2 S.algebra.a.2 ≫
      (constantFamilyFunctor P).map S.implicationConstructor ≫ valuation S P d =
        prod.map (valuation S P d) (valuation S P d) ≫
          constantProductComparison P (Two D) (Two D) ≫
            (constantFamilyFunctor P).map (Two.binaryArrow NullaryBooleanValuation.implies) := by
  have h := NullarySyntaxAlgebra.hom_implication ((S.stable P).to (algebra (V := V) P d))
  change NullarySyntaxAlgebra.implicationConstructor (NullaryInterpretation.parameterAlgebra S P) ≫
      valuation S P d = _ at h
  rw [NullaryInterpretation.parameter_implication S P] at h
  have hb : NullarySyntaxAlgebra.implicationConstructor (algebra (V := V) P d) =
      constantProductComparison P (Two D) (Two D) ≫
        (constantFamilyFunctor P).map (Two.binaryArrow NullaryBooleanValuation.implies) := by
    simp [NullarySyntaxAlgebra.implicationConstructor, algebra,
      SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.power, SyntaxPolynomial.constructors,
      SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor]
  simpa only [Category.assoc] using
    h.trans (congrArg (fun k => prod.map (valuation S P d) (valuation S P d) ≫ k) hb)

@[reassoc] theorem quantifier_value :
    constantProductComparison P V S.algebra.a.2 ≫
      (constantFamilyFunctor P).map S.quantifierConstructor ≫ valuation S P d =
        prod.snd ≫ valuation S P d := by
  have h := NullarySyntaxAlgebra.hom_quantifier ((S.stable P).to (algebra (V := V) P d))
  change NullarySyntaxAlgebra.quantifierConstructor (NullaryInterpretation.parameterAlgebra S P) ≫
      valuation S P d = _ at h
  rw [NullaryInterpretation.parameter_quantifier S P] at h
  have hb : NullarySyntaxAlgebra.quantifierConstructor (algebra (V := V) P d) = prod.snd := by
    simp [NullarySyntaxAlgebra.quantifierConstructor, algebra,
      SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.power, SyntaxPolynomial.constructors,
      SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor]
  rw [hb, prod.map_snd] at h
  simpa only [Category.assoc, NullaryInterpretation.parameterAlgebra,
    SyntaxPolynomial.algebraWithParameters, valuation, CategoricalSyntax.foldWithParameters] using h

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
