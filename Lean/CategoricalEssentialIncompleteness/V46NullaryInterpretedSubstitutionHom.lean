/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryInterpretedSubstitution

/-! # The interpreted substitution fold as an algebra morphism -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

def interpretedSubstitutionHom : parameterAlgebra S S.substitutionParameters ⟶
    targetSubstitutionAlgebra S Q f := by
  refine NullarySyntaxAlgebra.homOfConstructorsOfInitial
    (NullarySyntaxAlgebra.constantInitial S.substitutionParameters)
    (parameterHom (interpretedTermPair S Q f), parameterHom (interpretedFormulaPair S Q f))
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [parameter_variable]
    simp only [NullarySyntaxAlgebra.variableConstructor, targetSubstitutionAlgebra,
      coprod.inl_desc]
    apply constantFamily_hom_ext
    simpa [-prod.lift_fst_comp_snd_comp, constantFamilyFunctor, parameterHom,
      interpretedTermPair, Over.comp_left,
      Category.assoc, prod.comp_lift_assoc] using interpreted_variable S Q f prod.fst prod.snd
  · rw [parameter_equality]
    simp only [NullarySyntaxAlgebra.equalityConstructor, targetSubstitutionAlgebra,
      coprod.inl_desc]
    apply constantFamily_hom_ext
    have ha := interpretedTermPair_family S Q f
      (prod.fst : constantFamily S.substitutionParameters S.algebra.a.1 ⨯
        constantFamily S.substitutionParameters S.algebra.a.1 ⟶ _)
    have hb := interpretedTermPair_family S Q f
      (prod.snd : constantFamily S.substitutionParameters S.algebra.a.1 ⨯
        constantFamily S.substitutionParameters S.algebra.a.1 ⟶ _)
    simpa [-prod.lift_fst_comp_snd_comp, constantFamilyFunctor, parameterHom,
      constantProductComparison, parameterAlgebra, SyntaxPolynomial.algebraWithParameters,
      ha, hb,
      Over.comp_left, Category.assoc, prod.comp_lift_assoc, prod.lift_map_assoc] using
      interpreted_equality S Q f
        (constantFamily S.substitutionParameters S.algebra.a.1 ⨯
          constantFamily S.substitutionParameters S.algebra.a.1).hom
        ((prod.fst : constantFamily S.substitutionParameters S.algebra.a.1 ⨯
          constantFamily S.substitutionParameters S.algebra.a.1 ⟶ _).left ≫ prod.snd)
        ((prod.snd : constantFamily S.substitutionParameters S.algebra.a.1 ⨯
          constantFamily S.substitutionParameters S.algebra.a.1 ⟶ _).left ≫ prod.snd)
  · rw [parameter_atom]
    simp only [NullarySyntaxAlgebra.atomConstructor, targetSubstitutionAlgebra,
      coprod.inl_desc, coprod.inr_desc]
    apply constantFamily_hom_ext
    simpa [-prod.lift_fst_comp_snd_comp, constantFamilyFunctor, parameterHom,
      interpretedFormulaPair, Over.comp_left,
      Category.assoc, prod.comp_lift_assoc] using interpreted_atom S Q f prod.fst prod.snd
  · rw [parameter_negation]
    simp only [NullarySyntaxAlgebra.negationConstructor, targetSubstitutionAlgebra,
      coprod.inl_desc, coprod.inr_desc]
    apply constantFamily_hom_ext
    simpa [-prod.lift_fst_comp_snd_comp, constantFamilyFunctor, parameterHom,
      interpretedFormulaPair, Over.comp_left,
      Category.assoc, prod.comp_lift_assoc] using interpreted_negation S Q f prod.fst prod.snd
  · rw [parameter_implication]
    simp only [NullarySyntaxAlgebra.implicationConstructor, targetSubstitutionAlgebra,
      coprod.inl_desc, coprod.inr_desc]
    apply constantFamily_hom_ext
    have ha := interpretedFormulaPair_family S Q f
      (prod.fst : constantFamily S.substitutionParameters S.algebra.a.2 ⨯
        constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _)
    have hb := interpretedFormulaPair_family S Q f
      (prod.snd : constantFamily S.substitutionParameters S.algebra.a.2 ⨯
        constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _)
    simpa [-prod.lift_fst_comp_snd_comp, constantFamilyFunctor, parameterHom,
      constantProductComparison, ha, hb,
      parameterAlgebra, SyntaxPolynomial.algebraWithParameters,
      Over.comp_left, Category.assoc, prod.comp_lift_assoc, prod.lift_map_assoc] using
      interpreted_implication S Q f
        (constantFamily S.substitutionParameters S.algebra.a.2 ⨯
          constantFamily S.substitutionParameters S.algebra.a.2).hom
        ((prod.fst : constantFamily S.substitutionParameters S.algebra.a.2 ⨯
          constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _).left ≫ prod.snd)
        ((prod.snd : constantFamily S.substitutionParameters S.algebra.a.2 ⨯
          constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _).left ≫ prod.snd)
  · rw [parameter_quantifier]
    simp only [NullarySyntaxAlgebra.quantifierConstructor, targetSubstitutionAlgebra,
      coprod.inr_desc]
    apply constantFamily_hom_ext
    have ha := interpretedFormulaPair_family S Q f
      (prod.snd : constantFamily S.substitutionParameters V ⨯
        constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _)
    simpa [-prod.lift_fst_comp_snd_comp, constantFamilyFunctor, parameterHom,
      constantProductComparison, ha,
      parameterAlgebra, SyntaxPolynomial.algebraWithParameters,
      Over.comp_left, Category.assoc, prod.comp_lift_assoc, prod.lift_map_assoc] using
      interpreted_quantifier S Q f
        (constantFamily S.substitutionParameters V ⨯
          constantFamily S.substitutionParameters S.algebra.a.2).hom
        ((prod.fst : constantFamily S.substitutionParameters V ⨯
          constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _).left ≫ prod.snd)
        ((prod.snd : constantFamily S.substitutionParameters V ⨯
          constantFamily S.substitutionParameters S.algebra.a.2 ⟶ _).left ≫ prod.snd)

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
