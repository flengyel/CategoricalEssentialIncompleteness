/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertCoordinates
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Constructor values on actual named-rule parameter points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open SyntacticSyntax NamedFiniteSyntax NamedPostfixEncoding ConcreteNamedComparison

section ModelGeometry
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem lift_point {A B C : PredicateCategory T} (f : A ⟶ B) (g : A ⟶ C) (a : Obj T M A) :
    (F T M).map (prod.lift f g) a =
      pairPoint T M ((F T M).map f a) ((F T M).map g a) := by
  apply modelProduct_ext T M
  · exact (model_lift_fst T M f g a).trans (pairPoint_fst T M _ _).symm
  · exact (model_lift_snd T M f g a).trans (pairPoint_snd T M _ _).symm

theorem pullback_point_exists {A B C : PredicateCategory T}
    (f : A ⟶ C) (g : B ⟶ C) (a : Obj T M A) (b : Obj T M B)
    (h : (F T M).map f a = (F T M).map g b) :
    ∃ z : Obj T M (pullback f g),
      (F T M).map (pullback.fst f g) z = a ∧ (F T M).map (pullback.snd f g) z = b :=
  Types.exists_of_isPullback ((IsPullback.of_hasPullback f g).map (F T M)) a b h

/-- Every genuine Boolean fiber point is obtained from its equalizing
model point, using preservation of the actual equalizer. -/
theorem booleanFiber_point_exists {A : PredicateCategory T}
    (f : A ⟶ Two (PredicateCategory T)) (b : Bool) (a : Obj T M A)
    (h : (F T M).map f a = (F T M).map (Two.constant A b) a) :
    ∃ z : Obj T M (Two.Fiber f b),
      (F T M).map (Two.fiberι f b) z = a := by
  have hi := isLimitForkMapOfIsLimit (F T M)
    (equalizer.condition f (Two.constant A b))
    (equalizerIsEqualizer f (Two.constant A b))
  obtain ⟨z,hz,_⟩ := Types.unique_of_type_equalizer
    ((F T M).map (Two.fiberι f b)) _ hi a h
  exact ⟨z,hz⟩

end ModelGeometry

variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "G" => F 𝗣𝗔 ℕ

theorem implication_at {A : PredicateCategory 𝗣𝗔} (f g : A ⟶ Y) (a : Obj 𝗣𝗔 ℕ A)
    (φ ψ : Fm) (hf : (G).map f a = formulaPoint σ π d φ)
    (hg : (G).map g a = formulaPoint σ π d ψ) :
    (G).map (prod.lift f g ≫ (S).implicationConstructor) a = formulaPoint σ π d (.imp φ ψ) := by
  calc
    _ = (G).map (S).implicationConstructor ((G).map (prod.lift f g) a) :=
      (G).map_comp_apply _ _ a
    _ = (G).map (S).implicationConstructor
        (pairPoint 𝗣𝗔 ℕ ((G).map f a) ((G).map g a)) :=
      congrArg ((G).map (S).implicationConstructor) (lift_point 𝗣𝗔 ℕ f g a)
    _ = (G).map (S).implicationConstructor
        (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) :=
      congrArg ((G).map (S).implicationConstructor)
        (congrArg₂ (pairPoint 𝗣𝗔 ℕ) hf hg)
    _ = _ := implication_point σ π d φ ψ

theorem negation_at {A : PredicateCategory 𝗣𝗔} (f : A ⟶ Y) (a : Obj 𝗣𝗔 ℕ A)
    (φ : Fm) (hf : (G).map f a = formulaPoint σ π d φ) :
    (G).map (f ≫ (S).negationConstructor) a = formulaPoint σ π d (.neg φ) := by
  exact ((G).map_comp_apply f (S).negationConstructor a).trans
    ((congrArg ((G).map (S).negationConstructor) hf).trans (negation_point σ π d φ))

theorem equality_at {A : PredicateCategory 𝗣𝗔} (f g : A ⟶ X) (a : Obj 𝗣𝗔 ℕ A)
    (u t : Tm) (hf : (G).map f a = termPoint σ π d u)
    (hg : (G).map g a = termPoint σ π d t) :
    (G).map (prod.lift f g ≫ (S).equalityConstructor) a = formulaPoint σ π d (.equal u t) := by
  exact ((G).map_comp_apply _ _ a).trans
    ((congrArg ((G).map (S).equalityConstructor) (lift_point 𝗣𝗔 ℕ f g a)).trans
      ((congrArg ((G).map (S).equalityConstructor)
        (congrArg₂ (pairPoint 𝗣𝗔 ℕ) hf hg)).trans (equality_point σ π d u t)))

theorem quantifier_at {A : PredicateCategory 𝗣𝗔}
    (f : A ⟶ variableCarrier) (g : A ⟶ Y) (a : Obj 𝗣𝗔 ℕ A)
    (x : ℕ) (φ : Fm) (hf : (G).map f a = namePoint x)
    (hg : (G).map g a = formulaPoint σ π d φ) :
    (G).map (prod.lift f g ≫ (S).quantifierConstructor) a = formulaPoint σ π d (.all x φ) := by
  exact ((G).map_comp_apply _ _ a).trans
    ((congrArg ((G).map (S).quantifierConstructor) (lift_point 𝗣𝗔 ℕ f g a)).trans
      ((congrArg ((G).map (S).quantifierConstructor)
        (congrArg₂ (pairPoint 𝗣𝗔 ℕ) hf hg)).trans (quantifier_point σ π d x φ)))

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
