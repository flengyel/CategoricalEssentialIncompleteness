/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportParameterPolynomial
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsCore

/-!
The canonical parameter-family carrier comparison is a complete syntax algebra
isomorphism. Its proof uses the ordinary constructor comparison and the polynomial
parameter comparison.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (V : D) (σ π : ℕ → D) (d : ℕ)
local notation "p₀" => SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d
local notation "q₀" => SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d
local notation "p₁" => SyntaxPolynomial.termExpression V σ d
local notation "q₁" => SyntaxPolynomial.formulaExpression V π d
local notation "H" => sliceEquivalence E b

def syntaxParameterLanguageIso :
    SyntaxPolynomial.jointFunctor ((p₀).withParameters P) ((q₀).withParameters P) ⋙ ((H).prod H).functor ≅
      ((H).prod H).functor ⋙ SyntaxPolynomial.jointFunctor ((p₁).withParameters Q) ((q₁).withParameters Q) :=
  normalizedParameterJointIso E b p₁ q₁ p₀ q₀ p₁ q₁
    (mapCoefficients_termExpression E.inverse.obj V σ d).symm
    (mapCoefficients_formulaExpression E.inverse.obj V π d).symm
    (termTargetExpressionEquality V σ d) (formulaTargetExpressionEquality V π d)

def syntaxParameterTermInputIso (X : C × C) (Y : D × D) (i : (E.prod E).functor.obj X ≅ Y) :=
  substitutionNormalizedParameterInputIso E b X Y i p₁ p₀ p₁
    (mapCoefficients_termExpression E.inverse.obj V σ d) (termTargetExpressionEquality V σ d)

def syntaxParameterFormulaInputIso (X : C × C) (Y : D × D) (i : (E.prod E).functor.obj X ≅ Y) :=
  substitutionNormalizedParameterInputIso E b X Y i q₁ q₀ q₁
    (mapCoefficients_formulaExpression E.inverse.obj V π d) (formulaTargetExpressionEquality V π d)

@[reassoc] theorem syntaxParameterLanguageIso_fst (X : C × C) (Y : D × D)
    (i : (E.prod E).functor.obj X ≅ Y) :
    ((syntaxParameterLanguageIso E b V σ π d).hom.app (constantFamily P X.1,constantFamily P X.2)).1 ≫
        ((p₁).withParameters Q).eval.map (substitutionFamilyPairIso E b X Y i).hom =
      (syntaxParameterTermInputIso E b V σ d X Y i).hom := by
  exact normalizedParameterJointIso_fst E b p₁ q₁ p₀ q₀ p₁ q₁
    (mapCoefficients_termExpression E.inverse.obj V σ d).symm
    (mapCoefficients_formulaExpression E.inverse.obj V π d).symm
    (termTargetExpressionEquality V σ d) (formulaTargetExpressionEquality V π d) X Y i

@[reassoc] theorem syntaxParameterLanguageIso_snd (X : C × C) (Y : D × D)
    (i : (E.prod E).functor.obj X ≅ Y) :
    ((syntaxParameterLanguageIso E b V σ π d).hom.app (constantFamily P X.1,constantFamily P X.2)).2 ≫
        ((q₁).withParameters Q).eval.map (substitutionFamilyPairIso E b X Y i).hom =
      (syntaxParameterFormulaInputIso E b V π d X Y i).hom := by
  exact normalizedParameterJointIso_snd E b p₁ q₁ p₀ q₀ p₁ q₁
    (mapCoefficients_termExpression E.inverse.obj V σ d).symm
    (mapCoefficients_formulaExpression E.inverse.obj V π d).symm
    (termTargetExpressionEquality V σ d) (formulaTargetExpressionEquality V π d) X Y i

variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

theorem syntaxParameterTerm_structure :
    (H).functor.map (SyntaxPolynomial.algebraWithParameters p₀ q₀ S₀.algebra P).str.1 ≫
        (coefficientComparison E b S₀.algebra.a.1 S₁.algebra.a.1
          (syntaxTermIso E V σ π d S₀ c)).hom =
      (syntaxParameterTermInputIso E b V σ d S₀.algebra.a S₁.algebra.a
        (syntaxCarrierIso E V σ π d S₀ c)).hom ≫
          (SyntaxPolynomial.algebraWithParameters p₁ q₁ S₁.algebra Q).str.1 := by
  have hc := substitution_parameterize_square E b (syntaxTermConstructorInputIso E V σ π d S₀ S₁ c)
    (syntaxTermIso E V σ π d S₀ c) S₀.algebra.str.1 S₁.algebra.str.1
    (syntax_term_structure E V σ π d S₀ S₁ c)
  have h := map_substitution_normalizedParameterOperation E b S₀.algebra.a S₁.algebra.a
    (syntaxCarrierIso E V σ π d S₀ c) p₁ p₀ p₁
    (mapCoefficients_termExpression E.inverse.obj V σ d) (termTargetExpressionEquality V σ d)
    (syntaxTermIso E V σ π d S₀ c) (prod.snd ≫ S₀.algebra.str.1)
    (prod.snd ≫ S₁.algebra.str.1) hc
  simpa only [← substitution_constantFamily_map,SyntaxPolynomial.algebraWithParameters,
    syntaxParameterTermInputIso] using h

theorem syntaxParameterFormula_structure :
    (H).functor.map (SyntaxPolynomial.algebraWithParameters p₀ q₀ S₀.algebra P).str.2 ≫
        (coefficientComparison E b S₀.algebra.a.2 S₁.algebra.a.2
          (syntaxFormulaIso E V σ π d S₀ c)).hom =
      (syntaxParameterFormulaInputIso E b V π d S₀.algebra.a S₁.algebra.a
        (syntaxCarrierIso E V σ π d S₀ c)).hom ≫
          (SyntaxPolynomial.algebraWithParameters p₁ q₁ S₁.algebra Q).str.2 := by
  have hc := substitution_parameterize_square E b (syntaxFormulaConstructorInputIso E V σ π d S₀ S₁ c)
    (syntaxFormulaIso E V σ π d S₀ c) S₀.algebra.str.2 S₁.algebra.str.2
    (syntax_formula_structure E V σ π d S₀ S₁ c)
  have h := map_substitution_normalizedParameterOperation E b S₀.algebra.a S₁.algebra.a
    (syntaxCarrierIso E V σ π d S₀ c) q₁ q₀ q₁
    (mapCoefficients_formulaExpression E.inverse.obj V π d) (formulaTargetExpressionEquality V π d)
    (syntaxFormulaIso E V σ π d S₀ c) (prod.snd ≫ S₀.algebra.str.2)
    (prod.snd ≫ S₁.algebra.str.2) hc
  simpa only [← substitution_constantFamily_map,SyntaxPolynomial.algebraWithParameters,
    syntaxParameterFormulaInputIso] using h

/-- The carrier is the family comparison followed by the constant-family image of the
original syntax carrier isomorphism. -/
def syntaxParameterAlgebraIso :
    AlgebraTransport.mappedAlgebra ((H).prod H) (syntaxParameterLanguageIso E b V σ π d)
        (SyntaxPolynomial.algebraWithParameters p₀ q₀ S₀.algebra P) ≅
      SyntaxPolynomial.algebraWithParameters p₁ q₁ S₁.algebra Q := by
  let A := SyntaxPolynomial.algebraWithParameters p₀ q₀ S₀.algebra P
  let B := SyntaxPolynomial.algebraWithParameters p₁ q₁ S₁.algebra Q
  let a := syntaxParameterLanguageIso E b V σ π d
  let i := substitutionFamilyPairIso E b S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
  refine Endofunctor.Algebra.isoMk i ?_
  apply (cancel_epi ((a).app A.a).hom).mp
  change (a.app A.a).hom ≫
      ((SyntaxPolynomial.jointFunctor ((p₁).withParameters Q) ((q₁).withParameters Q)).map i.hom ≫ B.str) =
    (a.app A.a).hom ≫ (((a.app A.a).inv ≫ ((H).prod H).functor.map A.str) ≫ i.hom)
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  apply Prod.ext
  · change ((syntaxParameterLanguageIso E b V σ π d).hom.app
      (constantFamily P S₀.algebra.a.1,constantFamily P S₀.algebra.a.2)).1 ≫
        ((p₁).withParameters Q).eval.map (substitutionFamilyPairIso E b S₀.algebra.a S₁.algebra.a
          (syntaxCarrierIso E V σ π d S₀ c)).hom ≫ B.str.1 =
      (H).functor.map A.str.1 ≫ (coefficientComparison E b S₀.algebra.a.1 S₁.algebra.a.1
        (syntaxTermIso E V σ π d S₀ c)).hom
    rw [syntaxParameterLanguageIso_fst_assoc]
    exact (syntaxParameterTerm_structure E b V σ π d S₀ S₁ c).symm
  · change ((syntaxParameterLanguageIso E b V σ π d).hom.app
      (constantFamily P S₀.algebra.a.1,constantFamily P S₀.algebra.a.2)).2 ≫
        ((q₁).withParameters Q).eval.map (substitutionFamilyPairIso E b S₀.algebra.a S₁.algebra.a
          (syntaxCarrierIso E V σ π d S₀ c)).hom ≫ B.str.2 =
      (H).functor.map A.str.2 ≫ (coefficientComparison E b S₀.algebra.a.2 S₁.algebra.a.2
        (syntaxFormulaIso E V σ π d S₀ c)).hom
    rw [syntaxParameterLanguageIso_snd_assoc]
    exact (syntaxParameterFormula_structure E b V σ π d S₀ S₁ c).symm

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
