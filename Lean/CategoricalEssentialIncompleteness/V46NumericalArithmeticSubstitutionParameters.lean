/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticOperationValues

/-! # Actual arithmetic substitution parameter and input comparisons -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionParameters
open Coordinates NamedArithmeticSignature
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax
local notation "F" => PredicateInterpretation.functor 𝗣𝗔 ℕ

def pairedIso {A B : PredicateCategory 𝗣𝗔} {X Y : NumericalTuples.Object}
    (i : X ≅ numericalInterpretation.obj A) (j : Y ≅ numericalInterpretation.obj B) :
    X ⨯ Y ≅ numericalInterpretation.obj (A ⨯ B) :=
  prod.mapIso i j ≪≫ (Geometry.productIso A B).symm

private theorem product_inv_fst (A B : PredicateCategory 𝗣𝗔) :
    (Geometry.productIso A B).inv ≫ numericalInterpretation.map (prod.fst : A ⨯ B ⟶ A) = prod.fst := by
  rw [← Geometry.product_fst,Iso.inv_hom_id_assoc]

private theorem product_inv_snd (A B : PredicateCategory 𝗣𝗔) :
    (Geometry.productIso A B).inv ≫ numericalInterpretation.map (prod.snd : A ⨯ B ⟶ B) = prod.snd := by
  rw [← Geometry.product_snd,Iso.inv_hom_id_assoc]

@[reassoc] theorem pairedIso_fst {A B : PredicateCategory 𝗣𝗔} {X Y : NumericalTuples.Object}
    (i : X ≅ numericalInterpretation.obj A) (j : Y ≅ numericalInterpretation.obj B) :
    (pairedIso i j).hom ≫ numericalInterpretation.map (prod.fst : A ⨯ B ⟶ A) = prod.fst ≫ i.hom := by
  simp only [pairedIso,Iso.trans_hom,Iso.symm_hom,prod.mapIso_hom]
  rw [Category.assoc,product_inv_fst,prod.map_fst]

@[reassoc] theorem pairedIso_snd {A B : PredicateCategory 𝗣𝗔} {X Y : NumericalTuples.Object}
    (i : X ≅ numericalInterpretation.obj A) (j : Y ≅ numericalInterpretation.obj B) :
    (pairedIso i j).hom ≫ numericalInterpretation.map (prod.snd : A ⨯ B ⟶ B) = prod.snd ≫ j.hom := by
  simp only [pairedIso,Iso.trans_hom,Iso.symm_hom,prod.mapIso_hom]
  rw [Category.assoc,product_inv_snd,prod.map_snd]

theorem pairedIso_fst_point {A B : PredicateCategory 𝗣𝗔} {X Y : NumericalTuples.Object}
    (i : X ≅ numericalInterpretation.obj A) (j : Y ≅ numericalInterpretation.obj B)
    (q : NumericalTuples.Point (X ⨯ Y)) :
    (F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : A ⨯ B ⟶ A) ((pairedIso i j).hom.toFun q) =
      i.hom.toFun ((prod.fst : X ⨯ Y ⟶ X).toFun q) := by
  have h := congrArg (fun f => f.toFun q) (pairedIso_fst i j)
  exact (numericalInterpretation_value (prod.fst : A ⨯ B ⟶ A) _).symm.trans h

theorem pairedIso_snd_point {A B : PredicateCategory 𝗣𝗔} {X Y : NumericalTuples.Object}
    (i : X ≅ numericalInterpretation.obj A) (j : Y ≅ numericalInterpretation.obj B)
    (q : NumericalTuples.Point (X ⨯ Y)) :
    (F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : A ⨯ B ⟶ B) ((pairedIso i j).hom.toFun q) =
      j.hom.toFun ((prod.snd : X ⨯ Y ⟶ Y).toFun q) := by
  have h := congrArg (fun f => f.toFun q) (pairedIso_snd i j)
  exact (numericalInterpretation_value (prod.snd : A ⨯ B ⟶ B) _).symm.trans h

def parameterIso : (S).substitutionParameters ≅ numericalInterpretation.obj (S₀).substitutionParameters :=
  pairedIso variableIso termIso
def termInputIso : (S).algebra.a.1 ⨯ (S).substitutionParameters ≅
    numericalInterpretation.obj ((S₀).algebra.a.1 ⨯ (S₀).substitutionParameters) :=
  pairedIso termIso parameterIso
def formulaInputIso : (S).algebra.a.2 ⨯ (S).substitutionParameters ≅
    numericalInterpretation.obj ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) :=
  pairedIso formulaIso parameterIso

theorem parameter_name (p : NumericalTuples.Point (S).substitutionParameters) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : (S₀).substitutionParameters ⟶ variableSymbols)
      (parameterIso.hom.toFun p)).val = OperationValues.name p := by
  exact congrArg Subtype.val (pairedIso_fst_point variableIso termIso p)

theorem parameter_term (p : NumericalTuples.Point (S).substitutionParameters) :
    ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).substitutionParameters ⟶ (S₀).algebra.a.1)
      (parameterIso.hom.toFun p)).val = OperationValues.replacement p := by
  exact congrArg Subtype.val (pairedIso_snd_point variableIso termIso p)

theorem termInput_name (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : (S₀).substitutionParameters ⟶ variableSymbols)
      ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).algebra.a.1 ⨯ (S₀).substitutionParameters ⟶ (S₀).substitutionParameters)
        (termInputIso.hom.toFun q))).val =
      OperationValues.name ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := pairedIso_snd_point termIso parameterIso q
  exact (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (S₀).substitutionParameters variableSymbols) p).val) hp).trans
        (parameter_name ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))

theorem termInput_replacement (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).substitutionParameters ⟶ (S₀).algebra.a.1)
      ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).algebra.a.1 ⨯ (S₀).substitutionParameters ⟶ (S₀).substitutionParameters)
        (termInputIso.hom.toFun q))).val =
      OperationValues.replacement ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := pairedIso_snd_point termIso parameterIso q
  exact (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (S₀).substitutionParameters (S₀).algebra.a.1) p).val) hp).trans
        (parameter_term ((prod.snd : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))

theorem termInput_word (q : NumericalTuples.Point ((S).algebra.a.1 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : (S₀).algebra.a.1 ⨯ (S₀).substitutionParameters ⟶ (S₀).algebra.a.1)
      (termInputIso.hom.toFun q)).val =
      (termIso.hom.toFun ((prod.fst : (S).algebra.a.1 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.1).toFun q)).val := by
  exact congrArg Subtype.val (pairedIso_fst_point termIso parameterIso q)

theorem formulaInput_name (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : (S₀).substitutionParameters ⟶ variableSymbols)
      ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).algebra.a.2 ⨯ (S₀).substitutionParameters ⟶ (S₀).substitutionParameters)
        (formulaInputIso.hom.toFun q))).val =
      OperationValues.name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := pairedIso_snd_point formulaIso parameterIso q
  exact (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (S₀).substitutionParameters variableSymbols) p).val) hp).trans
        (parameter_name ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))

theorem formulaInput_replacement (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).substitutionParameters ⟶ (S₀).algebra.a.1)
      ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : (S₀).algebra.a.2 ⨯ (S₀).substitutionParameters ⟶ (S₀).substitutionParameters)
        (formulaInputIso.hom.toFun q))).val =
      OperationValues.replacement ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q) := by
  have hp := pairedIso_snd_point formulaIso parameterIso q
  exact (congrArg (fun p : PredicateInterpretation.Obj ℕ (S₀).substitutionParameters =>
    ((F).map (prod.snd (C := PredicateCategory 𝗣𝗔) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (S₀).substitutionParameters (S₀).algebra.a.1) p).val) hp).trans
        (parameter_term ((prod.snd : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).substitutionParameters).toFun q))

theorem formulaInput_word (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    ((F).map (prod.fst (C := PredicateCategory 𝗣𝗔) : (S₀).algebra.a.2 ⨯ (S₀).substitutionParameters ⟶ (S₀).algebra.a.2)
      (formulaInputIso.hom.toFun q)).val =
      (formulaIso.hom.toFun ((prod.fst : (S).algebra.a.2 ⨯ (S).substitutionParameters ⟶ (S).algebra.a.2).toFun q)).val := by
  exact congrArg Subtype.val (pairedIso_fst_point formulaIso parameterIso q)

private theorem result_congr {x r w x' r' w' : ℕ}
    (hx : x = x') (hr : r = r') (hw : w = w') :
    ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound x r w =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound x' r' w' := by
  cases hx
  cases hr
  cases hw
  rfl

theorem term_substitution : termInputIso.hom ≫ numericalInterpretation.map (S₀).termSubstitution =
    (S).termSubstitution ≫ termIso.hom := by
  apply NumericalTuples.Map.ext
  funext q
  apply Subtype.ext
  have hm := numericalInterpretation_value (C := (S₀).algebra.a.1 ⨯ (S₀).substitutionParameters)
    (D := (S₀).algebra.a.1) (S₀).termSubstitution (termInputIso.hom.toFun q)
  have h := ConcreteNamedComparison.plain_termSubstitution_value
    𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ (termInputIso.hom.toFun q)
  exact (congrArg Subtype.val hm).trans
    (h.trans ((result_congr (termInput_name q) (termInput_replacement q) (termInput_word q)).trans
      (OperationValues.term_substitution_value q).symm))

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionParameters
