/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainResults
import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportInputs

/-! # Actual canonical-to-plain comparison data for substitution transport -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

section IdentityComparisons
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

omit [FinitaryExtensive C] in
/-- Identity base equivalence still uses genuine product comparisons;
product extensionality identifies the resulting isomorphism. -/
theorem identity_productIso {A B A' B' : C} (i : A ≅ A') (j : B ≅ B') :
    SyntaxOptionTransport.productIso (CategoryTheory.Equivalence.refl : C ≌ C) i j =
      prod.mapIso i j := by
  apply Iso.ext
  apply prod.hom_ext
  · simp only [SyntaxOptionTransport.productIso_fst,prod.mapIso_hom,prod.map_fst]
    rfl
  · simp only [SyntaxOptionTransport.productIso_snd,prod.mapIso_hom,prod.map_snd]
    rfl

/-- The option comparison for the identity functor is the actual
functorial option map, not a numerical carrier identification. -/
theorem identity_optionIso_hom {A B : C} (i : A ≅ B) :
    (SyntaxOptionTransport.optionIso (CategoryTheory.Equivalence.refl : C ≌ C) i).hom =
      OptionSyntax.map i.hom := by
  apply coprod.hom_ext
  · have h := SyntaxOptionTransport.optionIso_inl
      (CategoryTheory.Equivalence.refl : C ≌ C) i
    have ht : (DecidableVariables.Transport.terminalIso
        (CategoryTheory.Equivalence.refl : C ≌ C)).hom = 𝟙 (⊤_ C) :=
      SyntaxPolynomialTransport.terminalComparison_identity
    change coprod.inl ≫ (SyntaxOptionTransport.optionIso
      (CategoryTheory.Equivalence.refl : C ≌ C) i).hom = _ at h
    erw [ht,Category.id_comp] at h
    simpa only [OptionSyntax.map,coprod.inl_map,Category.id_comp] using h
  · have h := SyntaxOptionTransport.optionIso_inr
      (CategoryTheory.Equivalence.refl : C ≌ C) i
    change coprod.inr ≫ (SyntaxOptionTransport.optionIso
      (CategoryTheory.Equivalence.refl : C ≌ C) i).hom = _ at h
    simpa only [OptionSyntax.map,coprod.inr_map] using h

theorem identity_booleanIso_hom :
    (DecidableVariables.Transport.booleanIso (CategoryTheory.Equivalence.refl : C ≌ C)).hom =
      𝟙 (Two C) := by
  apply coprod.hom_ext
  · have h := SyntaxOperationsTransport.booleanIso_inl
      (CategoryTheory.Equivalence.refl : C ≌ C)
    change coprod.inl ≫ (DecidableVariables.Transport.booleanIso
      (CategoryTheory.Equivalence.refl : C ≌ C)).hom =
        terminalComparison (𝟭 C) ≫ coprod.inl at h
    erw [SyntaxPolynomialTransport.terminalComparison_identity,Category.id_comp] at h
    simpa only [Category.comp_id] using h
  · have h := DecidableVariables.Transport.booleanIso_inr
      (CategoryTheory.Equivalence.refl : C ≌ C)
    change coprod.inr ≫ (DecidableVariables.Transport.booleanIso
      (CategoryTheory.Equivalence.refl : C ≌ C)).hom =
        terminalComparison (𝟭 C) ≫ coprod.inr at h
    erw [SyntaxPolynomialTransport.terminalComparison_identity,Category.id_comp] at h
    simpa only [Category.comp_id] using h

end IdentityComparisons

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "E" => (CategoryTheory.Equivalence.refl : PredicateCategory T ≌ PredicateCategory T)
local notation "S₀" => categoricalSyntax T V σ π d
local notation "S₁" => plainCategoricalSyntax T V σ π d

/-- The comparison has the actual constructor square supplied by two
algebra isomorphisms; no fold or substitution equation is assumed. -/
def plainTransportAlgebraIso :
    SyntaxOperationsTransport.mappedSyntaxAlgebra E V σ π d (S₀) ≅ (S₁).algebra :=
  SyntaxOperationsTransport.languageIdentityIso V σ π d (S₀) ≪≫
    plainAlgebraIso T (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)

theorem plainTransportTermIso_hom :
    (SyntaxOperationsTransport.syntaxTermIso E V σ π d (S₀)
      (plainTransportAlgebraIso T V σ π d)).hom =
      (syntaxPlainIso T V σ π d false).hom := by
  change (𝟙 ((S₀).algebra.a.1)) ≫ (syntaxPlainIso T V σ π d false).hom = _
  exact Category.id_comp _

theorem plainTransportFormulaIso_hom :
    (SyntaxOperationsTransport.syntaxFormulaIso E V σ π d (S₀)
      (plainTransportAlgebraIso T V σ π d)).hom =
      (syntaxPlainIso T V σ π d true).hom := by
  change (𝟙 ((S₀).algebra.a.2)) ≫ (syntaxPlainIso T V σ π d true).hom = _
  exact Category.id_comp _

theorem plainTransportTermIso :
    SyntaxOperationsTransport.syntaxTermIso E V σ π d (S₀)
      (plainTransportAlgebraIso T V σ π d) = syntaxPlainIso T V σ π d false :=
  Iso.ext (plainTransportTermIso_hom T V σ π d)

theorem plainTransportFormulaIso :
    SyntaxOperationsTransport.syntaxFormulaIso E V σ π d (S₀)
      (plainTransportAlgebraIso T V σ π d) = syntaxPlainIso T V σ π d true :=
  Iso.ext (plainTransportFormulaIso_hom T V σ π d)

theorem plainTransportParameterIso :
    SyntaxOperationsTransport.substitutionParameterIso E V σ π d (S₀) (S₁)
      (plainTransportAlgebraIso T V σ π d) = plainParameterIso T V V σ π d := by
  unfold SyntaxOperationsTransport.substitutionParameterIso
  rw [plainTransportTermIso,identity_productIso]
  rfl

/-- Public substitution places the word before its parameter. -/
def plainPublicInputIso (formula : Bool) :
    CategoryTheory.Iso (C := PredicateCategory T)
      ((syntaxCarrier V σ π d formula : PredicateCategory T) ⨯
        (V ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)))
      ((plainSyntaxCarrier V σ π d formula : PredicateCategory T) ⨯
        (V ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))) :=
  prod.mapIso (syntaxPlainIso T V σ π d formula) (plainParameterIso T V V σ π d)

theorem plainTransportTermPublicInputIso :
    SyntaxOptionTransport.productIso E
      (SyntaxOperationsTransport.syntaxTermIso E V σ π d (S₀)
        (plainTransportAlgebraIso T V σ π d))
      (SyntaxOperationsTransport.substitutionParameterIso E V σ π d (S₀) (S₁)
        (plainTransportAlgebraIso T V σ π d)) = plainPublicInputIso T V σ π d false := by
  rw [plainTransportTermIso,plainTransportParameterIso,identity_productIso]
  rfl

theorem plainTransportFormulaPublicInputIso :
    SyntaxOptionTransport.productIso E
      (SyntaxOperationsTransport.syntaxFormulaIso E V σ π d (S₀)
        (plainTransportAlgebraIso T V σ π d))
      (SyntaxOperationsTransport.substitutionParameterIso E V σ π d (S₀) (S₁)
        (plainTransportAlgebraIso T V σ π d)) = plainPublicInputIso T V σ π d true := by
  rw [plainTransportFormulaIso,plainTransportParameterIso,identity_productIso]
  rfl

/-- The word-first and parameter-first comparisons commute with the
actual chosen product symmetry. -/
theorem plainInputIso_braiding (formula : Bool) :
    (plainPublicInputIso T V σ π d formula).inv ≫
      (prod.braiding (C := PredicateCategory T)
        (syntaxCarrier V σ π d formula) (S₀).substitutionParameters).hom =
      (prod.braiding (C := PredicateCategory T)
        (plainSyntaxCarrier V σ π d formula) (S₁).substitutionParameters).hom ≫
          (plainInputIso T V V σ π d formula).inv := by
  have h := SyntaxOperationsTransport.substitutionProductIso_braiding E
    (syntaxPlainIso T V σ π d formula) (plainParameterIso T V V σ π d)
  rw [identity_productIso,identity_productIso] at h
  change (prod.braiding (C := PredicateCategory T)
      (syntaxCarrier V σ π d formula) (S₀).substitutionParameters).hom ≫
        (plainInputIso T V V σ π d formula).hom =
      (plainPublicInputIso T V σ π d formula).hom ≫
        (prod.braiding (C := PredicateCategory T)
          (plainSyntaxCarrier V σ π d formula) (S₁).substitutionParameters).hom at h
  apply (cancel_mono (plainInputIso T V V σ π d formula).hom).mp
  have hh := congrArg (fun k => (plainPublicInputIso T V σ π d formula).inv ≫ k) h
  simpa only [Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id] using hh

/-- This local concrete FV square follows from the already proved
canonical and plain occurrence folds, independently of arbitrary-base
transport and independently of any substitution conclusion. -/
theorem plainTransport_termOccurrences :
    (S₀).termOccurrences = (syntaxPlainIso T V σ π d false).hom ≫ (S₁).termOccurrences := by
  rw [plain_termOccurrences_eq]
  change (S₀).termOccurrences = (syntaxPlainIso T V σ π d false).hom ≫
    (syntaxPlainIso T V σ π d false).inv ≫ occurrencesArrow T V σ π d false
  rw [Iso.hom_inv_id_assoc]
  exact termOccurrences_eq T V σ π d

theorem plainTransport_formulaOccurrences :
    (S₀).formulaOccurrences = (syntaxPlainIso T V σ π d true).hom ≫ (S₁).formulaOccurrences := by
  rw [plain_formulaOccurrences_eq]
  change (S₀).formulaOccurrences = (syntaxPlainIso T V σ π d true).hom ≫
    (syntaxPlainIso T V σ π d true).inv ≫ occurrencesArrow T V σ π d true
  rw [Iso.hom_inv_id_assoc]
  exact formulaOccurrences_eq T V σ π d

/-- The list object and its chosen recursive structure are shared by
the two actual syntax bundles. This is an algebra isomorphism, not an
identification inferred from numerical codes. -/
def plainTransportListIso :
    (E).functor.obj (S₀).lists.algebra.carrier ≅ (S₁).lists.algebra.carrier :=
  Iso.refl _

theorem plainTransport_nil :
    (E).functor.map (S₀).lists.algebra.nil ≫ (plainTransportListIso T V σ π d).hom =
      terminalComparison (E).functor ≫ (S₁).lists.algebra.nil := by
  change (S₁).lists.algebra.nil ≫ 𝟙 _ = terminalComparison (𝟭 (PredicateCategory T)) ≫ _
  rw [SyntaxPolynomialTransport.terminalComparison_identity]
  simp

theorem plainTransport_singleton :
    (E).functor.map (S₀).lists.singleton ≫ (plainTransportListIso T V σ π d).hom =
      ((E).counitIso.app V).hom ≫ (S₁).lists.singleton := by
  change (S₁).lists.singleton ≫ 𝟙 _ = 𝟙 _ ≫ _
  simp

theorem plainTransport_append :
    (E).functor.map (S₀).lists.append ≫ (plainTransportListIso T V σ π d).hom =
      (SyntaxOptionTransport.productIso E (plainTransportListIso T V σ π d)
        (plainTransportListIso T V σ π d)).hom ≫ (S₁).lists.append := by
  rw [identity_productIso]
  change (S₁).lists.append ≫ 𝟙 _ = prod.map (𝟙 _) (𝟙 _) ≫ (S₁).lists.append
  simp

theorem plainTransport_deletion :
    (E).functor.map ((S₀).lists.deletion (S₀).decidableVariables) ≫
      (plainTransportListIso T V σ π d).hom =
      (SyntaxOptionTransport.productIso E ((E).counitIso.app V)
        (plainTransportListIso T V σ π d)).hom ≫
          (S₁).lists.deletion (S₁).decidableVariables := by
  rw [identity_productIso]
  change ((S₁).lists.deletion (S₁).decidableVariables) ≫ 𝟙 _ =
    prod.map (𝟙 _) (𝟙 _) ≫ ((S₁).lists.deletion (S₁).decidableVariables)
  simp

theorem plainTransport_membership :
    (E).functor.map ((S₀).lists.membership (S₀).decidableVariables) ≫
      (DecidableVariables.Transport.booleanIso E).hom =
      (SyntaxOptionTransport.productIso E ((E).counitIso.app V)
        (plainTransportListIso T V σ π d)).hom ≫
          (S₁).lists.membership (S₁).decidableVariables := by
  rw [identity_booleanIso_hom,identity_productIso]
  change ((S₁).lists.membership (S₁).decidableVariables) ≫ 𝟙 _ =
    prod.map (𝟙 _) (𝟙 _) ≫ ((S₁).lists.membership (S₁).decidableVariables)
  simp

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
