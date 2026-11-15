/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanValuation

/-! # Boolean computation with a shared internal parameter -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

/-- A value with a specified parameter, as a morphism in the parameter slice. -/
def frame {W P X : D} (p : W ⟶ P) (f : W ⟶ X) : Over.mk p ⟶ constantFamily P X :=
  Over.homMk (prod.lift p f) (prod.lift_fst p f)

omit [FinitaryExtensive D] in
@[reassoc] theorem frame_map {W P X Y : D} (p : W ⟶ P) (f : W ⟶ X) (g : X ⟶ Y) :
    frame p f ≫ (constantFamilyFunctor P).map g = frame p (f ≫ g) := by
  apply Over.OverMorphism.ext
  change prod.lift p f ≫ prod.map (𝟙 P) g = prod.lift p (f ≫ g)
  rw [prod.lift_map, Category.comp_id]

omit [FinitaryExtensive D] in
@[reassoc] theorem frame_product {W P X Y : D} (p : W ⟶ P) (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift (frame p f) (frame p g) ≫ constantProductComparison P X Y =
      frame p (prod.lift f g) := by
  apply constantFamily_hom_ext
  simp only [Over.comp_left, constantProductComparison, Over.homMk_left,
    prod.lift_snd, prod.comp_lift, SliceProductCoordinates.lift_fst_assoc,
    SliceProductCoordinates.lift_snd_assoc, frame]

@[reassoc] theorem family_unary_value {P : D} {W : Over P}
    (f : W ⟶ constantFamily P (Two D)) (op : Bool → Bool) :
    (f ≫ (constantFamilyFunctor P).map (Two.unary op (𝟙 (Two D)))).left ≫ prod.snd =
      Two.unary op (f.left ≫ prod.snd) := by
  simp [Over.comp_left, constantFamilyFunctor, Two.unary, Category.assoc]

@[reassoc] theorem family_binary_value {P : D} {W : Over P}
    (f g : W ⟶ constantFamily P (Two D)) (op : Bool → Bool → Bool) :
    (prod.lift f g ≫ constantProductComparison P (Two D) (Two D) ≫
      (constantFamilyFunctor P).map (Two.binaryArrow op)).left ≫ prod.snd =
        Two.binary op (f.left ≫ prod.snd) (g.left ≫ prod.snd) := by
  simp only [Over.comp_left, constantFamilyFunctor, Over.homMk_left, Two.binary,
    constantProductComparison, Category.assoc, prod.map_snd, prod.lift_snd_assoc]
  rw [← Category.assoc, prod.comp_lift]
  simp only [SliceProductCoordinates.lift_fst_assoc, SliceProductCoordinates.lift_snd_assoc]


variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
variable {W : D}

def evaluate (p : W ⟶ P) (f : W ⟶ S.algebra.a.2) : W ⟶ Two D :=
  prod.lift p f ≫ value S P d

theorem frame_evaluate (p : W ⟶ P) (f : W ⟶ S.algebra.a.2) :
    (frame p f ≫ valuation S P d).left ≫ prod.snd = evaluate S P d p f := by
  simp [frame, evaluate, value, Over.comp_left, Category.assoc]

@[reassoc] theorem evaluate_equality (p : W ⟶ P) (a b : W ⟶ S.algebra.a.1) :
    evaluate S P d p (prod.lift a b ≫ S.equalityConstructor) = Two.constant W true := by
  have h := congrArg (fun k => prod.lift (frame p a) (frame p b) ≫ k)
    (equality_value S P d)
  simp only [← Category.assoc, frame_product, frame_map, comp_constant] at h
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simpa only [frame_evaluate, constant_value, Over.mk_left] using hh

@[reassoc] theorem evaluate_atom (p : W ⟶ P) (a : W ⟶ X) :
    evaluate S P d p (a ≫ NullaryInterpretation.atomFormula S) =
      prod.lift p a ≫ d.left ≫ prod.snd := by
  have h := congrArg (fun k => frame p a ≫ k) (atom_value S P d)
  rw [← Category.assoc, frame_map] at h
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simpa only [frame_evaluate, Over.comp_left, frame, Over.homMk_left, Category.assoc,
    evaluate, value, Over.mk_left] using hh

@[reassoc] theorem evaluate_negation (p : W ⟶ P) (f : W ⟶ S.algebra.a.2) :
    evaluate S P d p (f ≫ S.negationConstructor) =
      Two.unary Bool.not (evaluate S P d p f) := by
  have h := congrArg (fun k => frame p f ≫ k) (negation_value S P d)
  rw [← Category.assoc, frame_map] at h
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simpa only [← Category.assoc, frame_evaluate, family_unary_value] using hh

@[reassoc] theorem evaluate_implication (p : W ⟶ P) (f g : W ⟶ S.algebra.a.2) :
    evaluate S P d p (prod.lift f g ≫ S.implicationConstructor) =
      Two.binary NullaryBooleanValuation.implies
        (evaluate S P d p f) (evaluate S P d p g) := by
  have h := congrArg (fun k => prod.lift (frame p f) (frame p g) ≫ k)
    (implication_value S P d)
  simp only [← Category.assoc, frame_product, frame_map, prod.lift_map] at h
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  simpa only [Category.assoc, family_binary_value, frame_evaluate, Over.mk_left] using hh

@[reassoc] theorem evaluate_quantifier (p : W ⟶ P) (v : W ⟶ V) (f : W ⟶ S.algebra.a.2) :
    evaluate S P d p (prod.lift v f ≫ S.quantifierConstructor) = evaluate S P d p f := by
  have h := congrArg (fun k => prod.lift (frame p v) (frame p f) ≫ k)
    (quantifier_value S P d)
  simp only [← Category.assoc, frame_product, frame_map, prod.lift_snd] at h
  simpa only [frame_evaluate, Over.mk_left] using congrArg (fun k => k.left ≫ prod.snd) h

/-- The implication law for an arbitrary morphism into its product of inputs. -/
theorem evaluate_implication_input (p : W ⟶ P)
    (a : W ⟶ S.algebra.a.2 ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.implicationConstructor) =
      Two.binary NullaryBooleanValuation.implies
        (evaluate S P d p (a ≫ prod.fst)) (evaluate S P d p (a ≫ prod.snd)) := by
  simpa only [parameterPair_eta] using evaluate_implication S P d p
    (a ≫ prod.fst) (a ≫ prod.snd)

/-- The quantifier law for an arbitrary morphism into its input object. -/
theorem evaluate_quantifier_input (p : W ⟶ P) (a : W ⟶ V ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.quantifierConstructor) =
      evaluate S P d p (a ≫ prod.snd) := by
  simpa only [parameterPair_eta] using evaluate_quantifier S P d p
    (a ≫ prod.fst) (a ≫ prod.snd)

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
