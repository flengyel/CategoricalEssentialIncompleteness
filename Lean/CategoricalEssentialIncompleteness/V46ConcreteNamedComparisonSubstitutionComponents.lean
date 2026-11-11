/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Actual result projections of the substitution constructor algebra -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

/-- Both original/result state components are projected by actual
product arrows. The second target sort is a genuine option object. -/
def optionResultProjection : S.substitutionCarriers ⟶
    (S.algebra.a.1,OptionSyntax.obj S.algebra.a.2) := (prod.snd,prod.snd)

theorem functionSubstitution_result_component :
    (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
      (SyntaxPolynomial.constructors σ d) ≫
        (constantFamilyFunctor S.substitutionParameters).map S.functionSubstitutionPair) ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.snd : S.algebra.a.1 ⨯ S.algebra.a.1 ⟶ S.algebra.a.1) =
    ((SyntaxPolynomial.constructors σ d).withParameters S.substitutionParameters).eval.map
      ((constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.1,
        (constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.2) ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.algebra.a
        (SyntaxPolynomial.constructors σ d) ≫
          (constantFamilyFunctor S.substitutionParameters).map S.functionConstructors) := by
  apply (SyntacticSyntax.parameterHom_component S.substitutionParameters
    (SyntaxPolynomial.constructors σ d) S.termResultProjection
    S.functionSubstitutionPair S.functionConstructors
    (prod.snd : S.algebra.a.1 ⨯ S.algebra.a.1 ⟶ S.algebra.a.1) ?_).symm
  simp only [CategoricalSyntax.functionSubstitutionPair,prod.lift_snd]

theorem equalitySubstitution_result_component :
    (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
      (SyntaxPolynomial.power .term 2) ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair) ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) =
    ((SyntaxPolynomial.power .term 2).withParameters S.substitutionParameters).eval.map
      ((constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.1,
        (constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.2) ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.algebra.a
        (SyntaxPolynomial.power .term 2) ≫
          (constantFamilyFunctor S.substitutionParameters).map (S.equalityConstructor ≫ coprod.inr)) := by
  apply (SyntacticSyntax.parameterHom_component S.substitutionParameters
    (SyntaxPolynomial.power .term 2) S.termResultProjection
    S.equalitySubstitutionPair (S.equalityConstructor ≫ coprod.inr)
    (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) ?_).symm
  simp only [CategoricalSyntax.equalitySubstitutionPair,prod.lift_snd]

theorem relationSubstitution_result_component :
    (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
      (SyntaxPolynomial.constructors π d) ≫
        (constantFamilyFunctor S.substitutionParameters).map S.relationSubstitutionPair) ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) =
    ((SyntaxPolynomial.constructors π d).withParameters S.substitutionParameters).eval.map
      ((constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.1,
        (constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.2) ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters S.algebra.a
        (SyntaxPolynomial.constructors π d) ≫
          (constantFamilyFunctor S.substitutionParameters).map (S.relationConstructors ≫ coprod.inr)) := by
  apply (SyntacticSyntax.parameterHom_component S.substitutionParameters
    (SyntaxPolynomial.constructors π d) S.termResultProjection
    S.relationSubstitutionPair (S.relationConstructors ≫ coprod.inr)
    (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) ?_).symm
  simp only [CategoricalSyntax.relationSubstitutionPair,prod.lift_snd]

theorem negationSubstitution_result_component :
    (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) =
    (constantFamilyFunctor S.substitutionParameters).map
      (prod.snd ≫ OptionSyntax.map S.negationConstructor) := by
  rw [← Functor.map_comp]
  congr 1
  simp only [CategoricalSyntax.negationSubstitutionPair,prod.lift_snd]

theorem implicationSubstitution_result_component :
    (SyntaxPolynomial.parameterComparison S.substitutionParameters S.substitutionCarriers
      (SyntaxPolynomial.power .formula 2) ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair) ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) =
    ((SyntaxPolynomial.power .formula 2).withParameters S.substitutionParameters).eval.map
      ((constantFamilyFunctor S.substitutionParameters).map (optionResultProjection S).1,
        (constantFamilyFunctor S.substitutionParameters).map (optionResultProjection S).2) ≫
      (SyntaxPolynomial.parameterComparison S.substitutionParameters
        (S.algebra.a.1,OptionSyntax.obj S.algebra.a.2) (SyntaxPolynomial.power .formula 2) ≫
          (constantFamilyFunctor S.substitutionParameters).map (OptionSyntax.binary S.implicationConstructor)) := by
  apply (SyntacticSyntax.parameterHom_component S.substitutionParameters
    (SyntaxPolynomial.power .formula 2) (optionResultProjection S)
    S.implicationSubstitutionPair (OptionSyntax.binary S.implicationConstructor)
    (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) ?_).symm
  simp only [CategoricalSyntax.implicationSubstitutionPair,prod.lift_snd]
  rfl

theorem quantifierSubstitution_result_component :
    parameterHom S.quantifierSubstitutionPair ≫
      (constantFamilyFunctor S.substitutionParameters).map
        (prod.snd : S.algebra.a.2 ⨯ OptionSyntax.obj S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2) =
      parameterHom S.quantifierSubstitutionResult := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;>
    simp [parameterHom,CategoricalSyntax.quantifierSubstitutionPair,constantFamilyFunctor]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
