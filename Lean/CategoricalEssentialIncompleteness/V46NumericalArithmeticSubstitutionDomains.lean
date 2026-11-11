/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSubstitutionParameters
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # The actual arithmetic admissibility isomorphism and result square -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionDomains
open Coordinates SubstitutionParameters NamedArithmeticSignature
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax
local notation "F" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "U" => NumericalUnderlying.functor

/-- The inverse pullback projection is an actual numerical morphism.
Surjectivity here concerns the supplied points, including empty carriers. -/
theorem imageProjection_isIso {A B C : NumericalTuples.Object}
    (m : A ⟶ C) [Mono m] (g : B ⟶ C)
    (h : ∀ b : NumericalTuples.Point B, ∃ a, m.toFun a = g.toFun b) :
    IsIso (pullback.snd m g) := by
  have hi : Function.Injective ((U).map (pullback.snd m g)) :=
    (mono_iff_injective _).mp inferInstance
  have hs : Function.Surjective ((U).map (pullback.snd m g)) := by
    intro b
    obtain ⟨a,ha⟩ := h b
    obtain ⟨z,_,hz⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback m g).map (U)) a b ha
    exact ⟨z,hz⟩
  let _ : IsIso ((U).map (pullback.snd m g)) := (isIso_iff_bijective _).mpr ⟨hi,hs⟩
  exact isIso_of_reflects_iso (pullback.snd m g) (U)

def imageLift {A B C : NumericalTuples.Object}
    (m : A ⟶ C) [Mono m] (g : B ⟶ C)
    (h : ∀ b : NumericalTuples.Point B, ∃ a, m.toFun a = g.toFun b) : B ⟶ A := by
  let _ : IsIso (pullback.snd m g) := imageProjection_isIso m g h
  exact (asIso (pullback.snd m g)).inv ≫ pullback.fst m g

theorem imageLift_comp {A B C : NumericalTuples.Object}
    (m : A ⟶ C) [Mono m] (g : B ⟶ C)
    (h : ∀ b : NumericalTuples.Point B, ∃ a, m.toFun a = g.toFun b) :
    imageLift m g h ≫ m = g := by
  let _ : IsIso (pullback.snd m g) := imageProjection_isIso m g h
  change ((asIso (pullback.snd m g)).inv ≫ pullback.fst m g) ≫ m = g
  rw [Category.assoc,pullback.condition,← Category.assoc]
  change ((asIso (pullback.snd m g)).inv ≫ (asIso (pullback.snd m g)).hom) ≫ g = g
  rw [Iso.inv_hom_id,Category.id_comp]

private theorem free_for_congr {x r w x' r' w' : ℕ}
    (hx : x = x') (hr : r = r') (hw : w = w') :
    ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) variableSymbols functionSymbols relationSymbols bound x r w =
      ConcreteNamedSubstitution.substitutionFreeFor (M := ℕ) variableSymbols functionSymbols relationSymbols bound x' r' w' := by
  cases hx
  cases hr
  cases hw
  rfl

private theorem result_congr {x r w x' r' w' : ℕ}
    (hx : x = x') (hr : r = r') (hw : w = w') :
    ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound x r w =
      ConcreteNamedSubstitution.substitutionResult (M := ℕ) variableSymbols functionSymbols relationSymbols bound x' r' w' := by
  cases hx
  cases hr
  cases hw
  rfl

theorem admissible_image_iff
    (q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters)) :
    (∃ a, (S).admissibleInclusion.toFun a = q) ↔
      ∃ a : NumericalTuples.Point (numericalInterpretation.obj (S₀).admissibleSubstitution),
        (numericalInterpretation.map (S₀).admissibleInclusion).toFun a = formulaInputIso.hom.toFun q := by
  have h := ConcreteNamedComparison.plain_admissible_model_iff
    𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ (formulaInputIso.hom.toFun q)
  have hc := free_for_congr (formulaInput_name q) (formulaInput_replacement q) (formulaInput_word q)
  have hm := h.trans (Iff.of_eq (congrArg (fun n : ℕ => n = 1) hc))
  have hi :
      (∃ a : PredicateInterpretation.Obj ℕ (S₀).admissibleSubstitution,
        (F).map (S₀).admissibleInclusion a = formulaInputIso.hom.toFun q) ↔
      ∃ a : NumericalTuples.Point (numericalInterpretation.obj (S₀).admissibleSubstitution),
        (numericalInterpretation.map (S₀).admissibleInclusion).toFun a = formulaInputIso.hom.toFun q := by
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨a,(numericalInterpretation_value (S₀).admissibleInclusion a).trans ha⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,(numericalInterpretation_value (S₀).admissibleInclusion a).symm.trans ha⟩
  exact (OperationValues.admissible_iff q).trans (hm.symm.trans hi)

theorem forward_image (a : NumericalTuples.Point (S).admissibleSubstitution) :
    ∃ b, (numericalInterpretation.map (S₀).admissibleInclusion).toFun b =
      ((S).admissibleInclusion ≫ formulaInputIso.hom).toFun a :=
  (admissible_image_iff ((S).admissibleInclusion.toFun a)).mp ⟨a,rfl⟩

def forward : (S).admissibleSubstitution ⟶
    numericalInterpretation.obj (S₀).admissibleSubstitution :=
  imageLift (numericalInterpretation.map (S₀).admissibleInclusion)
    ((S).admissibleInclusion ≫ formulaInputIso.hom) forward_image

@[reassoc] theorem forward_inclusion : forward ≫ numericalInterpretation.map (S₀).admissibleInclusion =
    (S).admissibleInclusion ≫ formulaInputIso.hom :=
  imageLift_comp _ _ forward_image

theorem backward_image
    (a : NumericalTuples.Point (numericalInterpretation.obj (S₀).admissibleSubstitution)) :
    ∃ b, (S).admissibleInclusion.toFun b =
      (numericalInterpretation.map (S₀).admissibleInclusion ≫ formulaInputIso.inv).toFun a := by
  let q : NumericalTuples.Point ((S).algebra.a.2 ⨯ (S).substitutionParameters) :=
    formulaInputIso.inv.toFun ((numericalInterpretation.map (S₀).admissibleInclusion).toFun a)
  apply (admissible_image_iff q).mpr
  refine ⟨a,?_⟩
  exact (congrArg (fun f => f.toFun ((numericalInterpretation.map (S₀).admissibleInclusion).toFun a))
    formulaInputIso.inv_hom_id).symm

def backward : numericalInterpretation.obj (S₀).admissibleSubstitution ⟶ (S).admissibleSubstitution :=
  imageLift (S).admissibleInclusion
    (numericalInterpretation.map (S₀).admissibleInclusion ≫ formulaInputIso.inv) backward_image

@[reassoc] theorem backward_inclusion : backward ≫ (S).admissibleInclusion =
    numericalInterpretation.map (S₀).admissibleInclusion ≫ formulaInputIso.inv :=
  imageLift_comp _ _ backward_image

/-- The comparison is constructed from the actual success domain and
the independently proved arithmetic admissibility flag. -/
def admissibleIso : (S).admissibleSubstitution ≅ numericalInterpretation.obj (S₀).admissibleSubstitution where
  hom := forward
  inv := backward
  hom_inv_id := by
    apply (cancel_mono (S).admissibleInclusion).1
    rw [Category.assoc,backward_inclusion,← Category.assoc,forward_inclusion]
    simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (numericalInterpretation.map (S₀).admissibleInclusion)).1
    rw [Category.assoc,forward_inclusion,← Category.assoc,backward_inclusion]
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id,Category.id_comp]

theorem admissible_result : admissibleIso.hom ≫ numericalInterpretation.map (S₀).formulaSubstitution =
    (S).formulaSubstitution ≫ formulaIso.hom := by
  apply NumericalTuples.Map.ext
  funext a
  apply Subtype.ext
  have hv := numericalInterpretation_value (S₀).formulaSubstitution (forward.toFun a)
  let q := (S).admissibleInclusion.toFun a
  have hq : (F).map (S₀).admissibleInclusion (forward.toFun a) = formulaInputIso.hom.toFun q :=
    (numericalInterpretation_value (S₀).admissibleInclusion _).symm.trans
      (congrArg (fun f => f.toFun a) forward_inclusion)
  have hx := (congrArg (fun t : PredicateInterpretation.Obj ℕ
      (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).substitutionParameters) =>
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (S₀).substitutionParameters variableSymbols)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
        ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters) t)).val) hq).trans
          (formulaInput_name q)
  have hr := (congrArg (fun t : PredicateInterpretation.Obj ℕ
      (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).substitutionParameters) =>
    ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (S₀).substitutionParameters (S₀).algebra.a.1)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
        ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).substitutionParameters) t)).val) hq).trans
          (formulaInput_replacement q)
  have hw := (congrArg (fun t : PredicateInterpretation.Obj ℕ
      (Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).substitutionParameters) =>
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      ((S₀).algebra.a.2 ⨯ (S₀).substitutionParameters) (S₀).algebra.a.2) t).val) hq).trans
        (formulaInput_word q)
  have h := ConcreteNamedComparison.plain_formulaSubstitution_value
    𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ (forward.toFun a)
  exact (congrArg Subtype.val hv).trans
    (h.trans ((congrArg (fun n : ℕ => π₁ n) (result_congr hx hr hw)).trans
      (OperationValues.formula_substitution_value a).symm))

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionDomains
