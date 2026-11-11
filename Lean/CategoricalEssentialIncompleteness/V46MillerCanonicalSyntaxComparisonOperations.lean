/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonTranspose
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportValues
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSentences
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralNegation

/-! # Canonical occurrence, substitution and sentence charts

The existing equivalence transport is applied backwards, where its
inverse-image signature is exactly the explicit forward signature.
Every list comparison used below is derived in Transpose from the actual
mapped list operations. The unit transposes the resulting fold equations
to the forward presentation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
open SyntaxOperationsTransport
variable (a : Point) (V : PredicateCategory 𝗣𝗔)
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "F" => Syntax.predicateFunctor (P)
local notation "E" => Total.pointPresentation a
local notation "v" => CategoryTheory.Functor.obj (Syntax.predicateFunctor (Uniform.Family.ofPoint a)) V
local notation "s" => (fun n => CategoryTheory.Functor.obj (Syntax.predicateFunctor (Uniform.Family.ofPoint a)) (σ n))
local notation "r" => (fun n => CategoryTheory.Functor.obj (Syntax.predicateFunctor (Uniform.Family.ofPoint a)) (π n))
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d

def reverseAlgebraIso : mappedSyntaxAlgebra (E).symm (v) (s) (r) d (S₂) ≅ (S₁).algebra :=
  syntaxAlgebraIso (C := Total.CanonicalTotal a) (D := Total.TotalCategory (P))
    (E).symm (v) (s) (r) d (S₂) (S₁)

def reverseTermIso : (E).inverse.obj (S₂).algebra.a.1 ≅ (S₁).algebra.a.1 :=
  syntaxTermIso (C := Total.CanonicalTotal a) (D := Total.TotalCategory (P))
    (E).symm (v) (s) (r) d (S₂) («S₁» := (S₁)) (reverseAlgebraIso a V σ π d)

def reverseFormulaIso : (E).inverse.obj (S₂).algebra.a.2 ≅ (S₁).algebra.a.2 :=
  syntaxFormulaIso (C := Total.CanonicalTotal a) (D := Total.TotalCategory (P))
    (E).symm (v) (s) (r) d (S₂) («S₁» := (S₁)) (reverseAlgebraIso a V σ π d)

def reverseLists : (E).inverse.obj (S₂).lists.algebra.carrier ≅ (S₁).lists.algebra.carrier :=
  reverseListIso (E) (v) (S₁).lists

def termIso : (E).functor.obj (S₁).algebra.a.1 ≅ (S₂).algebra.a.1 :=
  transposeIso (E).symm (reverseTermIso a V σ π d)

def formulaIso : (E).functor.obj (S₁).algebra.a.2 ≅ (S₂).algebra.a.2 :=
  transposeIso (E).symm (reverseFormulaIso a V σ π d)

def listIso : (E).functor.obj (S₁).lists.algebra.carrier ≅ (S₂).lists.algebra.carrier :=
  transposeIso (E).symm (reverseLists a V σ π d)

theorem listIso_eq_refl : listIso a V σ π d = Iso.refl ((E).functor.obj (S₁).lists.algebra.carrier) :=
  transpose_unit_inverse (E) (S₁).lists.algebra.carrier

theorem reverse_nil :
    (E).inverse.map (S₂).lists.algebra.nil ≫ (reverseLists a V σ π d).hom =
      terminalComparison (E).inverse ≫ (S₁).lists.algebra.nil :=
  reverseList_nil (E) (v) (S₁).lists

theorem reverse_singleton :
    (E).inverse.map (S₂).lists.singleton ≫ (reverseLists a V σ π d).hom =
      ((E).symm.counitIso.app (v)).hom ≫ (S₁).lists.singleton :=
  reverseList_singleton (E) (v) (S₁).lists

theorem reverse_append :
    (E).inverse.map (S₂).lists.append ≫ (reverseLists a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E).symm (reverseLists a V σ π d)
        (reverseLists a V σ π d)).hom ≫ (S₁).lists.append :=
  reverseList_append (E) (v) (S₁).lists

theorem reverse_deletion :
    (E).inverse.map ((S₂).lists.deletion (S₂).decidableVariables) ≫
        (reverseLists a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E).symm ((E).symm.counitIso.app (v))
        (reverseLists a V σ π d)).hom ≫ (S₁).lists.deletion (S₁).decidableVariables :=
  reverseList_deletion (E) (v) (S₁).lists (S₁).decidableVariables (S₂).decidableVariables

theorem reverse_membership :
    (E).inverse.map ((S₂).lists.membership (S₂).decidableVariables) ≫
        (DecidableVariables.Transport.booleanIso (E).symm).hom =
      (SyntaxOptionTransport.productIso (E).symm ((E).symm.counitIso.app (v))
        (reverseLists a V σ π d)).hom ≫ (S₁).lists.membership (S₁).decidableVariables :=
  reverseList_membership (E) (v) (S₁).lists (S₁).decidableVariables (S₂).decidableVariables

theorem reverse_termOccurrences :
    (E).inverse.map (S₂).termOccurrences ≫ (reverseLists a V σ π d).hom =
      (reverseTermIso a V σ π d).hom ≫ (S₁).termOccurrences :=
  map_termOccurrences (E).symm (v) (s) (r) d (S₂) (S₁)
    (reverseLists a V σ π d) (reverse_nil a V σ π d) (reverse_singleton a V σ π d)
    (reverse_append a V σ π d) (reverse_deletion a V σ π d) (reverseAlgebraIso a V σ π d)

theorem reverse_formulaOccurrences :
    (E).inverse.map (S₂).formulaOccurrences ≫ (reverseLists a V σ π d).hom =
      (reverseFormulaIso a V σ π d).hom ≫ (S₁).formulaOccurrences :=
  map_formulaOccurrences (E).symm (v) (s) (r) d (S₂) (S₁)
    (reverseLists a V σ π d) (reverse_nil a V σ π d) (reverse_singleton a V σ π d)
    (reverse_append a V σ π d) (reverse_deletion a V σ π d) (reverseAlgebraIso a V σ π d)

theorem termOccurrences_comparison :
    (E).functor.map (S₁).termOccurrences ≫ (listIso a V σ π d).hom =
      (termIso a V σ π d).hom ≫ (S₂).termOccurrences :=
  transpose_square (E).symm (reverseTermIso a V σ π d) (reverseLists a V σ π d)
    (S₂).termOccurrences (S₁).termOccurrences (reverse_termOccurrences a V σ π d)

theorem formulaOccurrences_comparison :
    (E).functor.map (S₁).formulaOccurrences ≫ (listIso a V σ π d).hom =
      (formulaIso a V σ π d).hom ≫ (S₂).formulaOccurrences :=
  transpose_square (E).symm (reverseFormulaIso a V σ π d) (reverseLists a V σ π d)
    (S₂).formulaOccurrences (S₁).formulaOccurrences (reverse_formulaOccurrences a V σ π d)

theorem nil_comparison :
    (E).functor.map (S₁).lists.algebra.nil ≫ (listIso a V σ π d).hom =
      terminalComparison (E).functor ≫ (S₂).lists.algebra.nil := by
  have h := transpose_square (E).symm (DecidableVariables.Transport.terminalIso (E).symm)
    (reverseLists a V σ π d) (S₂).lists.algebra.nil (S₁).lists.algebra.nil (reverse_nil a V σ π d)
  rw [transpose_terminal (E).symm] at h
  change (E).functor.map (S₁).lists.algebra.nil ≫ (listIso a V σ π d).hom =
    terminalComparison (E).functor ≫ (S₂).lists.algebra.nil at h
  exact h

def reverseParameterIso : (E).inverse.obj (S₂).substitutionParameters ≅ (S₁).substitutionParameters :=
  substitutionParameterIso (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d)

def parameterIso : (E).functor.obj (S₁).substitutionParameters ≅ (S₂).substitutionParameters :=
  transposeIso (E).symm (reverseParameterIso a V σ π d)

theorem reverse_termSubstitution :
    (E).inverse.map (S₂).termSubstitution ≫ (reverseTermIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E).symm (reverseTermIso a V σ π d)
        (reverseParameterIso a V σ π d)).hom ≫ (S₁).termSubstitution :=
  map_termSubstitution (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d)
    (reverseLists a V σ π d) (reverse_nil a V σ π d) (reverse_singleton a V σ π d)
    (reverse_append a V σ π d) (reverse_deletion a V σ π d) (reverse_membership a V σ π d)

theorem termSubstitution_comparison :
    (E).functor.map (S₁).termSubstitution ≫ (termIso a V σ π d).hom =
      (SyntaxOptionTransport.productIso (E) (termIso a V σ π d)
        (parameterIso a V σ π d)).hom ≫ (S₂).termSubstitution := by
  have h := transpose_square (E).symm
    (SyntaxOptionTransport.productIso (E).symm (reverseTermIso a V σ π d)
      (reverseParameterIso a V σ π d)) (reverseTermIso a V σ π d)
    (S₂).termSubstitution (S₁).termSubstitution (reverse_termSubstitution a V σ π d)
  rw [transpose_product (E).symm] at h
  change (E).functor.map (S₁).termSubstitution ≫ (termIso a V σ π d).hom =
    (SyntaxOptionTransport.productIso (E) (termIso a V σ π d)
      (parameterIso a V σ π d)).hom ≫ (S₂).termSubstitution at h
  exact h

theorem reverse_formulaSubstitutionOption :
    (E).inverse.map (S₂).formulaSubstitutionOption ≫
        (SyntaxOptionTransport.optionIso (E).symm (reverseFormulaIso a V σ π d)).hom =
      (SyntaxOptionTransport.productIso (E).symm (reverseFormulaIso a V σ π d)
        (reverseParameterIso a V σ π d)).hom ≫ (S₁).formulaSubstitutionOption :=
  map_formulaSubstitutionOption (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d)
    (reverseLists a V σ π d) (reverse_nil a V σ π d) (reverse_singleton a V σ π d)
    (reverse_append a V σ π d) (reverse_deletion a V σ π d) (reverse_membership a V σ π d)

theorem formulaSubstitutionOption_comparison :
    (E).functor.map (S₁).formulaSubstitutionOption ≫
        (SyntaxOptionTransport.optionIso (E) (formulaIso a V σ π d)).hom =
      (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d)
        (parameterIso a V σ π d)).hom ≫ (S₂).formulaSubstitutionOption := by
  have h := transpose_square (E).symm
    (SyntaxOptionTransport.productIso (E).symm (reverseFormulaIso a V σ π d)
      (reverseParameterIso a V σ π d))
    (SyntaxOptionTransport.optionIso (E).symm (reverseFormulaIso a V σ π d))
    (S₂).formulaSubstitutionOption (S₁).formulaSubstitutionOption
    (reverse_formulaSubstitutionOption a V σ π d)
  rw [transpose_product (E).symm,transpose_option (E).symm] at h
  change (E).functor.map (S₁).formulaSubstitutionOption ≫
      (SyntaxOptionTransport.optionIso (E) (formulaIso a V σ π d)).hom =
    (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d)
      (parameterIso a V σ π d)).hom ≫ (S₂).formulaSubstitutionOption at h
  exact h

def admissibleIso : (E).functor.obj (S₁).admissibleSubstitution ≅ (S₂).admissibleSubstitution :=
  SyntaxOptionTransport.successIso (E)
    (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d) (parameterIso a V σ π d))
    (formulaIso a V σ π d) (S₁).formulaSubstitutionOption (S₂).formulaSubstitutionOption
    (formulaSubstitutionOption_comparison a V σ π d)

theorem admissibleIso_inclusion :
    (admissibleIso a V σ π d).hom ≫ (S₂).admissibleInclusion =
      (E).functor.map (S₁).admissibleInclusion ≫
        (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d) (parameterIso a V σ π d)).hom :=
  SyntaxOptionTransport.successIso_fst (E)
    (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d) (parameterIso a V σ π d))
    (formulaIso a V σ π d) (S₁).formulaSubstitutionOption (S₂).formulaSubstitutionOption
    (formulaSubstitutionOption_comparison a V σ π d)

theorem admissibleIso_result :
    (admissibleIso a V σ π d).hom ≫ (S₂).formulaSubstitution =
      (E).functor.map (S₁).formulaSubstitution ≫ (formulaIso a V σ π d).hom :=
  SyntaxOptionTransport.successIso_snd (E)
    (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d) (parameterIso a V σ π d))
    (formulaIso a V σ π d) (S₁).formulaSubstitutionOption (S₂).formulaSubstitutionOption
    (formulaSubstitutionOption_comparison a V σ π d)

theorem negation_comparison :
    (E).functor.map (S₁).negationConstructor ≫ (formulaIso a V σ π d).hom =
      (formulaIso a V σ π d).hom ≫ (S₂).negationConstructor :=
  transpose_square (E).symm (reverseFormulaIso a V σ π d) (reverseFormulaIso a V σ π d)
    (S₂).negationConstructor (S₁).negationConstructor
    (syntax_negation_constructor (E).symm (v) (s) (r) d (S₂) (S₁) (reverseAlgebraIso a V σ π d))

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
