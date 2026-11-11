/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainTransportData
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSubstitutionValues
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportValues

/-! # The actual plain substitution arrows through constructor comparisons -/

@[expose] public section

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
local notation "E" => (CategoryTheory.Equivalence.refl : PredicateCategory T ≌ PredicateCategory T)
local notation "S₀" => categoricalSyntax T V σ π d
local notation "S₁" => plainCategoricalSyntax T V σ π d

theorem plain_termSubstitution_comparison :
    (S₀).termSubstitution ≫ (syntaxPlainIso T V σ π d false).hom =
      (plainPublicInputIso T V σ π d false).hom ≫ (S₁).termSubstitution := by
  have h := SyntaxOperationsTransport.map_termSubstitution E V σ π d (S₀) (S₁)
    (plainTransportAlgebraIso T V σ π d) (plainTransportListIso T V σ π d)
    (plainTransport_nil T V σ π d) (plainTransport_singleton T V σ π d)
    (plainTransport_append T V σ π d) (plainTransport_deletion T V σ π d)
    (plainTransport_membership T V σ π d)
  erw [plainTransportTermPublicInputIso T V σ π d,
    plainTransportTermIso_hom T V σ π d] at h
  exact h

theorem plain_formulaSubstitutionOption_comparison :
    (S₀).formulaSubstitutionOption ≫ OptionSyntax.map (syntaxPlainIso T V σ π d true).hom =
      (plainPublicInputIso T V σ π d true).hom ≫ (S₁).formulaSubstitutionOption := by
  have h := SyntaxOperationsTransport.map_formulaSubstitutionOption E V σ π d (S₀) (S₁)
    (plainTransportAlgebraIso T V σ π d) (plainTransportListIso T V σ π d)
    (plainTransport_nil T V σ π d) (plainTransport_singleton T V σ π d)
    (plainTransport_append T V σ π d) (plainTransport_deletion T V σ π d)
    (plainTransport_membership T V σ π d)
  erw [plainTransportFormulaPublicInputIso T V σ π d,
    plainTransportFormulaIso T V σ π d,identity_optionIso_hom] at h
  exact h

theorem plain_termSubstitution_eq_computed :
    (S₁).termSubstitution =
      (prod.braiding (C := PredicateCategory T) (plainSyntaxCarrier V σ π d false) (S₁).substitutionParameters).hom ≫
        computedPlainTermResult T V V σ π d := by
  calc
    _ = (plainPublicInputIso T V σ π d false).inv ≫
        ((plainPublicInputIso T V σ π d false).hom ≫ (S₁).termSubstitution) := by simp
    _ = (plainPublicInputIso T V σ π d false).inv ≫
        ((S₀).termSubstitution ≫ (syntaxPlainIso T V σ π d false).hom) := by
      rw [plain_termSubstitution_comparison T V σ π d]
    _ = ((plainPublicInputIso T V σ π d false).inv ≫
        (prod.braiding (C := PredicateCategory T) (syntaxCarrier V σ π d false) (S₀).substitutionParameters).hom) ≫
          computedTermResult T V V σ π d ≫ (syntaxPlainIso T V σ π d false).hom := by
      erw [canonical_termSubstitution_eq_computed T V σ π d]
      simp only [Category.assoc]
    _ = ((prod.braiding (C := PredicateCategory T) (plainSyntaxCarrier V σ π d false) (S₁).substitutionParameters).hom ≫
        (plainInputIso T V V σ π d false).inv) ≫
          computedTermResult T V V σ π d ≫ (syntaxPlainIso T V σ π d false).hom := by
      erw [plainInputIso_braiding T V σ π d false]
    _ = _ := by simp only [computedPlainTermResult,Category.assoc]

theorem plain_formulaSubstitutionOption_eq_computed :
    (S₁).formulaSubstitutionOption =
      (prod.braiding (C := PredicateCategory T) (plainSyntaxCarrier V σ π d true) (S₁).substitutionParameters).hom ≫
        computedPlainFormulaResult T V V σ π d := by
  calc
    _ = (plainPublicInputIso T V σ π d true).inv ≫
        ((plainPublicInputIso T V σ π d true).hom ≫ (S₁).formulaSubstitutionOption) := by simp
    _ = (plainPublicInputIso T V σ π d true).inv ≫
        ((S₀).formulaSubstitutionOption ≫ OptionSyntax.map (syntaxPlainIso T V σ π d true).hom) := by
      rw [plain_formulaSubstitutionOption_comparison T V σ π d]
    _ = ((plainPublicInputIso T V σ π d true).inv ≫
        (prod.braiding (C := PredicateCategory T) (syntaxCarrier V σ π d true) (S₀).substitutionParameters).hom) ≫
          computedFormulaResult T V V σ π d ≫ OptionSyntax.map (syntaxPlainIso T V σ π d true).hom := by
      erw [canonical_formulaSubstitutionOption_eq_computed T V σ π d]
      simp only [Category.assoc]
    _ = ((prod.braiding (C := PredicateCategory T) (plainSyntaxCarrier V σ π d true) (S₁).substitutionParameters).hom ≫
        (plainInputIso T V V σ π d true).inv) ≫
          computedFormulaResult T V V σ π d ≫ OptionSyntax.map (syntaxPlainIso T V σ π d true).hom := by
      erw [plainInputIso_braiding T V σ π d true]
    _ = _ := by simp only [computedPlainFormulaResult,Category.assoc]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
