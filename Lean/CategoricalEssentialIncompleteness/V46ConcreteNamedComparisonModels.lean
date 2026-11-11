/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import CategoricalEssentialIncompleteness.TwoBoolean
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Finite model geometry for concrete named-operation comparisons -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem model_lift_fst {X A B : PredicateCategory T} (f : X ⟶ A) (g : X ⟶ B)
    (x : Obj T M X) :
    (F T M).map (prod.fst : A ⨯ B ⟶ A) ((F T M).map (prod.lift f g) x) =
      (F T M).map f x := by
  rw [← Functor.map_comp_apply, prod.lift_fst]

@[simp] theorem model_lift_snd {X A B : PredicateCategory T} (f : X ⟶ A) (g : X ⟶ B)
    (x : Obj T M X) :
    (F T M).map (prod.snd : A ⨯ B ⟶ B) ((F T M).map (prod.lift f g) x) =
      (F T M).map g x := by
  rw [← Functor.map_comp_apply, prod.lift_snd]

@[simp] theorem model_map_fst {A B C D : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ D)
    (x : Obj T M (A ⨯ B)) :
    (F T M).map (prod.fst : C ⨯ D ⟶ C) ((F T M).map (prod.map f g) x) =
      (F T M).map f ((F T M).map (prod.fst : A ⨯ B ⟶ A) x) := by
  rw [← Functor.map_comp_apply, prod.map_fst, Functor.map_comp_apply]

@[simp] theorem model_map_snd {A B C D : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ D)
    (x : Obj T M (A ⨯ B)) :
    (F T M).map (prod.snd : C ⨯ D ⟶ D) ((F T M).map (prod.map f g) x) =
      (F T M).map g ((F T M).map (prod.snd : A ⨯ B ⟶ B) x) := by
  rw [← Functor.map_comp_apply, prod.map_snd, Functor.map_comp_apply]

theorem model_sum_map_inl {A B C D : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ D)
    (x : Obj T M A) :
    (F T M).map (coprod.map f g) ((F T M).map (coprod.inl : A ⟶ A ⨿ B) x) =
      (F T M).map (coprod.inl : C ⟶ C ⨿ D) ((F T M).map f x) := by
  have h := congrArg (fun k => (F T M).map k x) (coprod.inl_map f g)
  simpa only [Functor.map_comp_apply] using h

theorem model_sum_map_inr {A B C D : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ D)
    (x : Obj T M B) :
    (F T M).map (coprod.map f g) ((F T M).map (coprod.inr : B ⟶ A ⨿ B) x) =
      (F T M).map (coprod.inr : D ⟶ C ⨿ D) ((F T M).map g x) := by
  have h := congrArg (fun k => (F T M).map k x) (coprod.inr_map f g)
  simpa only [Functor.map_comp_apply] using h

/-- A model point in a true or false equalizer fiber evaluates the
actual categorical conditional by that branch. Only preserved finite
geometry is used; no interpretation of initiality in Set is assumed. -/
theorem model_branch {X Y : PredicateCategory T} (χ : X ⟶ Two (PredicateCategory T))
    (f g : X ⟶ Y) (x : Obj T M X) (b : Bool)
    (hb : (F T M).map χ x = (F T M).map (Two.constant X b) x) :
    (F T M).map (Two.branch χ f g) x =
      (F T M).map (if b then g else f) x := by
  have hi := isLimitForkMapOfIsLimit (F T M)
    (equalizer.condition χ (Two.constant X b))
    (equalizerIsEqualizer χ (Two.constant X b))
  obtain ⟨q, hq, _⟩ := Types.unique_of_type_equalizer
    ((F T M).map (Two.fiberι χ b)) _ hi x hb
  have he := congrArg (fun k => (F T M).map k q) (Two.fiberι_branch χ f g b)
  simpa only [Functor.map_comp_apply, hq] using he

theorem model_unary {X : PredicateCategory T} (op : Bool → Bool)
    (f : X ⟶ Two (PredicateCategory T)) (x : Obj T M X) (b : Bool)
    (hf : (F T M).map f x = (F T M).map (Two.constant X b) x) :
    (F T M).map (Two.unary op f) x = (F T M).map (Two.constant X (op b)) x := by
  change (F T M).map (f ≫ coprod.desc (Two.point (op false)) (Two.point (op true))) x = _
  rw [Functor.map_comp_apply, hf, ← Functor.map_comp_apply]
  change (F T M).map (Two.unary op (Two.constant X b)) x = _
  rw [Two.unary_constant]

theorem model_binary {X : PredicateCategory T} (op : Bool → Bool → Bool)
    (f g : X ⟶ Two (PredicateCategory T)) (x : Obj T M X) (a b : Bool)
    (hf : (F T M).map f x = (F T M).map (Two.constant X a) x)
    (hg : (F T M).map g x = (F T M).map (Two.constant X b) x) :
    (F T M).map (Two.binary op f g) x =
      (F T M).map (Two.constant X (op a b)) x := by
  have hp : (F T M).map (prod.lift f g) x =
      (F T M).map (prod.lift (Two.constant X a) (Two.constant X b)) x := by
    apply modelProduct_ext T M
    · simpa only [model_lift_fst] using hf
    · simpa only [model_lift_snd] using hg
  change (F T M).map (prod.lift f g ≫ Two.binaryArrow op) x = _
  rw [Functor.map_comp_apply, hp, ← Functor.map_comp_apply]
  change (F T M).map (Two.binary op (Two.constant X a) (Two.constant X b)) x = _
  rw [Two.binary_constant]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
