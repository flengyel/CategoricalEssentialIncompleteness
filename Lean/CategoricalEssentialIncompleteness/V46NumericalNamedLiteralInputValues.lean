/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSubstitutionValues
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralVariables

/-! # The actual coordinates of numerical substitution inputs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport
local notation "E" => literalEquivalence
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ

def presentedProductIso {A B : PredicateCategory 𝗧𝗔} {X Y : NumericalTuples.Object}
    (i : (E).functor.obj A ≅ X) (j : (E).functor.obj B ≅ Y) :
    X ⨯ Y ≅ NumericalCoordinates.predicateObject (A ⨯ B) :=
  (SyntaxOptionTransport.productIso (E) i j).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (A ⨯ B)

theorem presentedProduct_fst_value {A B : PredicateCategory 𝗧𝗔}
    {X Y : NumericalTuples.Object} (i : (E).functor.obj A ≅ X) (j : (E).functor.obj B ≅ Y)
    (x : NumericalTuples.Point (X ⨯ Y)) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) A) ((presentedProductIso i j).hom.toFun x) =
      (i.symm ≪≫ NumericalCoordinates.predicatePresentationIso A).hom.toFun
        ((prod.fst : X ⨯ Y ⟶ X).toFun x) := by
  exact (predicate_operation_value (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) A) (prod.fst : X ⨯ Y ⟶ X)
    (presentedProductIso i j) (i.symm ≪≫ NumericalCoordinates.predicatePresentationIso A)
    (conjugate_operation ((E).functor.map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) A))
      (prod.fst : X ⨯ Y ⟶ X) (SyntaxOptionTransport.productIso (E) i j) i
      (NumericalCoordinates.predicatePresentationIso (A ⨯ B))
      (NumericalCoordinates.predicatePresentationIso A)
      (SyntaxOptionTransport.productIso_fst (E) i j).symm)
    id ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) A)) (fun _ => rfl) x).symm

theorem presentedProduct_snd_value {A B : PredicateCategory 𝗧𝗔}
    {X Y : NumericalTuples.Object} (i : (E).functor.obj A ≅ X) (j : (E).functor.obj B ≅ Y)
    (x : NumericalTuples.Point (X ⨯ Y)) :
    (F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) B) ((presentedProductIso i j).hom.toFun x) =
      (j.symm ≪≫ NumericalCoordinates.predicatePresentationIso B).hom.toFun
        ((prod.snd : X ⨯ Y ⟶ Y).toFun x) := by
  exact (predicate_operation_value (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) B) (prod.snd : X ⨯ Y ⟶ Y)
    (presentedProductIso i j) (j.symm ≪≫ NumericalCoordinates.predicatePresentationIso B)
    (conjugate_operation ((E).functor.map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) B))
      (prod.snd : X ⨯ Y ⟶ Y) (SyntaxOptionTransport.productIso (E) i j) j
      (NumericalCoordinates.predicatePresentationIso (A ⨯ B))
      (NumericalCoordinates.predicatePresentationIso B)
      (SyntaxOptionTransport.productIso_snd (E) i j).symm)
    id ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (A ⨯ B) B)) (fun _ => rfl) x).symm

variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V

def literalVariablePresentationIso : V ≅ NumericalCoordinates.predicateObject V₀ :=
  ((E).counitIso.app V).symm ≪≫ NumericalCoordinates.predicatePresentationIso V₀

theorem literalVariablePresentation_value (x : NumericalTuples.Point V) :
    ((literalVariablePresentationIso V).hom.toFun x).val = NumericalTuples.code V.dimension x.val :=
  coefficient_inverse_code x

def literalParameterPresentationIso : (S₁).substitutionParameters ≅
    NumericalCoordinates.predicateObject (S₀).substitutionParameters :=
  (literalParameterIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (S₀).substitutionParameters

theorem literalTermInput_word
    (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).substitutionParameters)) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.1)
        ((literalTermInputPresentationIso V σ π d).hom.toFun q) =
      (literalTermPresentationIso V σ π d).hom.toFun
        ((prod.fst : (S₁).algebra.a.1 ⨯ (S₁).substitutionParameters ⟶ (S₁).algebra.a.1).toFun q) :=
  @presentedProduct_fst_value (S₀).algebra.a.1 (S₀).substitutionParameters
    (S₁).algebra.a.1 (S₁).substitutionParameters
    (literalTermIso V σ π d) (literalParameterIso V σ π d) q

theorem literalFormulaInput_word
    (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).substitutionParameters)) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2)
        ((literalFormulaInputPresentationIso V σ π d).hom.toFun q) =
      (literalFormulaPresentationIso V σ π d).hom.toFun
        ((prod.fst : (S₁).algebra.a.2 ⨯ (S₁).substitutionParameters ⟶ (S₁).algebra.a.2).toFun q) :=
  @presentedProduct_fst_value (S₀).algebra.a.2 (S₀).substitutionParameters
    (S₁).algebra.a.2 (S₁).substitutionParameters
    (literalFormulaIso V σ π d) (literalParameterIso V σ π d) q

theorem literalTermInput_parameter
    (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).substitutionParameters)) :
    (F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)
        ((literalTermInputPresentationIso V σ π d).hom.toFun q) =
      (literalParameterPresentationIso V σ π d).hom.toFun
        ((prod.snd : (S₁).algebra.a.1 ⨯ (S₁).substitutionParameters ⟶ (S₁).substitutionParameters).toFun q) :=
  @presentedProduct_snd_value (S₀).algebra.a.1 (S₀).substitutionParameters
    (S₁).algebra.a.1 (S₁).substitutionParameters
    (literalTermIso V σ π d) (literalParameterIso V σ π d) q

theorem literalFormulaInput_parameter
    (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).substitutionParameters)) :
    (F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters)
        ((literalFormulaInputPresentationIso V σ π d).hom.toFun q) =
      (literalParameterPresentationIso V σ π d).hom.toFun
        ((prod.snd : (S₁).algebra.a.2 ⨯ (S₁).substitutionParameters ⟶ (S₁).substitutionParameters).toFun q) :=
  @presentedProduct_snd_value (S₀).algebra.a.2 (S₀).substitutionParameters
    (S₁).algebra.a.2 (S₁).substitutionParameters
    (literalFormulaIso V σ π d) (literalParameterIso V σ π d) q

theorem literalParameter_name (p : NumericalTuples.Point (S₁).substitutionParameters) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀)
      ((literalParameterPresentationIso V σ π d).hom.toFun p) =
    (literalVariablePresentationIso V).hom.toFun
      ((prod.fst : (S₁).substitutionParameters ⟶ V).toFun p) :=
  @presentedProduct_fst_value V₀ (S₀).algebra.a.1 V (S₁).algebra.a.1
    ((E).counitIso.app V) (literalTermIso V σ π d) p

theorem literalParameter_term (p : NumericalTuples.Point (S₁).substitutionParameters) :
    (F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (S₀).substitutionParameters (S₀).algebra.a.1)
      ((literalParameterPresentationIso V σ π d).hom.toFun p) =
    (literalTermPresentationIso V σ π d).hom.toFun
      ((prod.snd : (S₁).substitutionParameters ⟶ (S₁).algebra.a.1).toFun p) :=
  @presentedProduct_snd_value V₀ (S₀).algebra.a.1 V (S₁).algebra.a.1
    ((E).counitIso.app V) (literalTermIso V σ π d) p

theorem literalParameter_name_value (p : NumericalTuples.Point (S₁).substitutionParameters) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (S₀).substitutionParameters V₀)
      ((literalParameterPresentationIso V σ π d).hom.toFun p)).val =
    NumericalTuples.code V.dimension ((prod.fst : (S₁).substitutionParameters ⟶ V).toFun p).val :=
  (congrArg Subtype.val (literalParameter_name V σ π d p)).trans
    (literalVariablePresentation_value V ((prod.fst : (S₁).substitutionParameters ⟶ V).toFun p))

end CategoricalEssentialIncompleteness.V46.NumericalNamed
