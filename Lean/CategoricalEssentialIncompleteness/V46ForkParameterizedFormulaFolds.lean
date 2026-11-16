/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkFormulaTransitionSquares

/-! # Natural formula folds for arbitrary fork parameter families

Target operations are componentwise relative polynomial operations whose
constructor squares commute with the actual fork transitions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkParameterizedFormulaFolds
open ForkFirstOrderFormula
local instance (X : C) : Regular (Over X) := RegularSlices.regular X
variable (D P : Object)

abbrev component (X : Over P) (j : WalkingSpan) : Over (P.obj j) := Over.mk (X.hom.app j)

abbrev componentHom {X Y : Over P} (m : X ⟶ Y) (j : WalkingSpan) :
    component P X j ⟶ component P Y j :=
  Over.homMk (m.left.app j) (congrArg (fun n => n.app j) (Over.w m))

abbrev carrierTransition (X : Over P) {j l : WalkingSpan} (f : j ⟶ l) :
    (Over.map (P.map f)).obj (component P X j) ⟶ component P X l :=
  Over.homMk (X.left.map f) (X.hom.naturality f)

abbrev polynomial (j : WalkingSpan) :=
  ForkFormulaParameterComponents.polynomial (numbers.obj j) (D.obj j) (P.obj j)

/-- A target consists of an arbitrary family over P and natural operations
for the five printed constructors, with relative products in each slice. -/
structure Algebra where
  carrier : Over P
  str : ∀ j, (polynomial D P j).obj (component P carrier j) ⟶ component P carrier j
  naturality : ∀ {j l : WalkingSpan} (f : j ⟶ l),
    (ForkFormulaParameterChange.comparison (numbers.obj j) (P.map f) (D.map f)).app
        (component P carrier j) ≫
      (polynomial D P l).map (carrierTransition P carrier f) ≫ str l =
      (Over.map (P.map f)).map (str j) ≫ carrierTransition P carrier f

namespace Algebra
@[ext] structure Hom (A B : Algebra D P) where
  f : A.carrier ⟶ B.carrier
  h : ∀ j, (polynomial D P j).map (componentHom P f j) ≫ B.str j =
    A.str j ≫ componentHom P f j

instance : Category (Algebra D P) where
  Hom := Hom D P
  id A := {
    f := 𝟙 A.carrier
    h j := by
      change (polynomial D P j).map (𝟙 (component P A.carrier j)) ≫ A.str j = A.str j ≫ 𝟙 _
      simp }
  comp f g := {
    f := f.f ≫ g.f
    h j := by
      change (polynomial D P j).map (componentHom P f.f j ≫ componentHom P g.f j) ≫ _ = _
      rw [CategoryTheory.Functor.map_comp, Category.assoc, g.h, ← Category.assoc, f.h, Category.assoc]
      rfl }
  id_comp f := Hom.ext (Category.id_comp f.f)
  comp_id f := Hom.ext (Category.comp_id f.f)
  assoc f g h := Hom.ext (Category.assoc f.f g.f h.f)

@[simp] theorem id_f (A : Algebra D P) : (𝟙 A : A ⟶ A).f = 𝟙 A.carrier := rfl
@[simp] theorem comp_f {A B E : Algebra D P} (f : A ⟶ B) (g : B ⟶ E) :
    (f ≫ g).f = f.f ≫ g.f := rfl
end Algebra

/-- The literal pointwise product retains its parameter at every transition. -/
def parameterCarrierFunctor : Object where
  obj j := P.obj j ⨯ (ForkFirstOrderFormula.algebra D).a.obj j
  map f := prod.map (P.map f) ((ForkFirstOrderFormula.algebra D).a.map f)
  map_id j := by
    rw [P.map_id j, (ForkFirstOrderFormula.algebra D).a.map_id j, prod.map_id_id]
  map_comp f g := by
    rw [P.map_comp f g, (ForkFirstOrderFormula.algebra D).a.map_comp f g, prod.map_map]

def parameterProjection : parameterCarrierFunctor D P ⟶ P where
  app _ := prod.fst
  naturality {_ _} f := prod.map_fst (P.map f) ((ForkFirstOrderFormula.algebra D).a.map f)

def parameterCarrier : Over P := Over.mk (parameterProjection D P)

def algebra : Algebra D P where
  carrier := parameterCarrier D P
  str j := (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j)).str
  naturality {_ _} f := ForkFormulaTransitionSquares.fork_source_square D P f

def componentAlgebra (B : Algebra D P) (j : WalkingSpan) :
    Endofunctor.Algebra (polynomial D P j) := ⟨component P B.carrier j, B.str j⟩

def componentFold (B : Algebra D P) (j : WalkingSpan) :
    ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j) ⟶
      componentAlgebra D P B j :=
  ForkFormulaParameterComponents.fold (numbers.obj j) (D.obj j) (P.obj j)
    (componentAlgebra D P B j)

/-- Both concrete constructor squares are discharged: the source square
is proved, and the target square is the naturality of its operations. -/
theorem fold_natural (B : Algebra D P) {j l : WalkingSpan} (f : j ⟶ l) :
    (parameterCarrierFunctor D P).map f ≫ (componentFold D P B l).f.left =
      (componentFold D P B j).f.left ≫ B.carrier.left.map f := by
  have h := LaxAlgebraAdjunction.fold_natural (Over.mapPullbackAdj (P.map f))
    (ForkFormulaParameterChange.comparison (numbers.obj j) (P.map f) (D.map f))
    (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j))
    (componentAlgebra D P B j)
    (ForkFormulaParameterComponents.initial (numbers.obj j) (D.obj j) (P.obj j))
    (ForkFormulaParameterComponents.algebra (numbers.obj l) (D.obj l) (P.obj l))
    (componentAlgebra D P B l)
    (ForkFormulaTransitionSquares.parameterMap (numbers.obj j)
      (D.obj j) (D.obj l) (P.obj j) (P.obj l) (P.map f)
      ((ForkFirstOrderFormula.algebra D).a.map f))
    (carrierTransition P B.carrier f)
    (ForkFormulaTransitionSquares.fork_source_square D P f) (B.naturality f)
    (componentFold D P B j) (componentFold D P B l)
  exact congrArg Over.Hom.left h

def foldCarrier (B : Algebra D P) : parameterCarrierFunctor D P ⟶ B.carrier.left where
  app j := (componentFold D P B j).f.left
  naturality {_ _} f := fold_natural D P B f

def fold (B : Algebra D P) : algebra D P ⟶ B where
  f := Over.homMk (foldCarrier D P B) (by
    apply NatTrans.ext
    funext j
    exact Over.w (componentFold D P B j).f)
  h j := (componentFold D P B j).h

/-- Uniqueness includes every natural computable carrier morphism over P. -/
def initial : IsInitial (algebra D P) :=
  IsInitial.ofUniqueHom (fold D P) (by
    intro B m
    apply Algebra.Hom.ext
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext j
    exact congrArg (fun n => n.f.left)
      ((ForkFormulaParameterComponents.initial (numbers.obj j) (D.obj j) (P.obj j)).hom_ext
        (⟨componentHom P m.f j, m.h j⟩ :
          ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j) ⟶
            componentAlgebra D P B j)
        (componentFold D P B j)))

/-- The other projection of the literal pointwise parameter product. -/
def formulaProjection : parameterCarrierFunctor D P ⟶ (ForkFirstOrderFormula.algebra D).a where
  app _ := prod.snd
  naturality {_ _} f := prod.map_snd (P.map f) ((ForkFirstOrderFormula.algebra D).a.map f)

def toConstant : parameterCarrier D P ⟶
    constantFamily P (ForkFirstOrderFormula.algebra D).a :=
  Over.homMk (prod.lift (parameterProjection D P) (formulaProjection D P))
    (prod.lift_fst _ _)

def fromConstantLeft : P ⨯ (ForkFirstOrderFormula.algebra D).a ⟶ parameterCarrierFunctor D P where
  app j := prod.lift
    ((prod.fst : P ⨯ (ForkFirstOrderFormula.algebra D).a ⟶ P).app j)
    ((prod.snd : P ⨯ (ForkFirstOrderFormula.algebra D).a ⟶
      (ForkFirstOrderFormula.algebra D).a).app j)
  naturality {j l} f := by
    dsimp only [parameterCarrierFunctor]
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, prod.lift_fst_assoc]
      exact (prod.fst : P ⨯ (ForkFirstOrderFormula.algebra D).a ⟶ P).naturality f
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc]
      exact (prod.snd : P ⨯ (ForkFirstOrderFormula.algebra D).a ⟶
        (ForkFirstOrderFormula.algebra D).a).naturality f

def fromConstant : constantFamily P (ForkFirstOrderFormula.algebra D).a ⟶ parameterCarrier D P :=
  Over.homMk (fromConstantLeft D P) (by
    apply NatTrans.ext
    funext j
    exact prod.lift_fst _ _)

/-- The pointwise carrier is the specified constant family up to its
canonical product isomorphism over P. -/
def parameterCarrierIso : parameterCarrier D P ≅
    constantFamily P (ForkFirstOrderFormula.algebra D).a where
  hom := toConstant D P
  inv := fromConstant D P
  hom_inv_id := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext j
    apply prod.hom_ext
    · change ((prod.lift (parameterProjection D P) (formulaProjection D P)).app j ≫
        (fromConstantLeft D P).app j) ≫ prod.fst = (𝟙 _ : _ ⟶ _) ≫ prod.fst
      rw [Category.assoc, fromConstantLeft, prod.lift_fst, Category.id_comp]
      exact congrArg (fun m => m.app j) (prod.lift_fst (parameterProjection D P) (formulaProjection D P))
    · change ((prod.lift (parameterProjection D P) (formulaProjection D P)).app j ≫
        (fromConstantLeft D P).app j) ≫ prod.snd = (𝟙 _ : _ ⟶ _) ≫ prod.snd
      rw [Category.assoc, fromConstantLeft, prod.lift_snd, Category.id_comp]
      exact congrArg (fun m => m.app j) (prod.lift_snd (parameterProjection D P) (formulaProjection D P))
  inv_hom_id := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · change fromConstantLeft D P ≫ prod.lift (parameterProjection D P) (formulaProjection D P) ≫
        prod.fst = 𝟙 _ ≫ prod.fst
      rw [prod.lift_fst, Category.id_comp]
      apply NatTrans.ext
      funext j
      exact prod.lift_fst _ _
    · change fromConstantLeft D P ≫ prod.lift (parameterProjection D P) (formulaProjection D P) ≫
        prod.snd = 𝟙 _ ≫ prod.snd
      rw [prod.lift_snd, Category.id_comp]
      apply NatTrans.ext
      funext j
      exact prod.lift_snd _ _

theorem fold_over (B : Algebra D P) :
    (fold D P B).f.left ≫ B.carrier.hom = (parameterCarrier D P).hom := Over.w _

theorem fold_constructor (B : Algebra D P) (j : WalkingSpan) :
    (polynomial D P j).map (componentHom P (fold D P B).f j) ≫ B.str j =
      (algebra D P).str j ≫ componentHom P (fold D P B).f j := (fold D P B).h j

/-- Every underlying natural morphism over P with the constructor equations
is the constructed fold. -/
theorem fold_underlying_unique (B : Algebra D P) (m : (algebra D P).carrier ⟶ B.carrier)
    (hm : ∀ j, (polynomial D P j).map (componentHom P m j) ≫ B.str j =
      (algebra D P).str j ≫ componentHom P m j) : m = (fold D P B).f :=
  congrArg Algebra.Hom.f ((initial D P).hom_ext (⟨m, hm⟩ : algebra D P ⟶ B) _)

end CategoricalEssentialIncompleteness.V46.ForkParameterizedFormulaFolds
