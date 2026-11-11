/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphsFunctor
public import CategoricalEssentialIncompleteness.V46NumericalUnderlying
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationCoproducts

/-! # The actual arithmetic finite-product, sum and pullback comparisons -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Geometry

/-- The components are identity maps on the literal standard carrier.
Naturality uses the proved values of the represented graph programs. -/
def standardComparison : numericalInterpretation ⋙ NumericalUnderlying.functor ≅
    PredicateInterpretation.functor 𝗣𝗔 ℕ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro C D f
    apply ConcreteCategory.hom_ext
    intro x
    change (numericalInterpretation.map f).toFun x =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map f x
    exact numericalInterpretation_value f x)

instance preservesFiniteLimits : PreservesFiniteLimits numericalInterpretation := by
  let _ : PreservesFiniteLimits (numericalInterpretation ⋙ NumericalUnderlying.functor) :=
    preservesFiniteLimits_of_natIso standardComparison.symm
  exact preservesFiniteLimits_of_reflects_of_preserves numericalInterpretation NumericalUnderlying.functor

instance preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) numericalInterpretation := by
  let _ : ReflectsColimitsOfShape (Discrete WalkingPair) NumericalUnderlying.functor :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  let _ : PreservesColimitsOfShape (Discrete WalkingPair)
      (numericalInterpretation ⋙ NumericalUnderlying.functor) :=
    preservesColimitsOfShape_of_natIso standardComparison.symm
  exact preservesColimitsOfShape_of_reflects_of_preserves
    numericalInterpretation NumericalUnderlying.functor

/-- The comparison itself is a morphism in the numerical category,
so each direction has a partial-recursive carrier-total realizer. -/
def productIso (C D : PredicateCategory 𝗣𝗔) :
    numericalInterpretation.obj (C ⨯ D) ≅
      numericalInterpretation.obj C ⨯ numericalInterpretation.obj D :=
  asIso (prodComparison numericalInterpretation C D)

@[reassoc (attr := simp)] theorem product_fst (C D : PredicateCategory 𝗣𝗔) :
    (productIso C D).hom ≫ prod.fst = numericalInterpretation.map (prod.fst : C ⨯ D ⟶ C) :=
  prodComparison_fst numericalInterpretation C D

@[reassoc (attr := simp)] theorem product_snd (C D : PredicateCategory 𝗣𝗔) :
    (productIso C D).hom ≫ prod.snd = numericalInterpretation.map (prod.snd : C ⨯ D ⟶ D) :=
  prodComparison_snd numericalInterpretation C D

def coproductIso (C D : PredicateCategory 𝗣𝗔) :
    numericalInterpretation.obj (C ⨿ D) ≅
      numericalInterpretation.obj C ⨿ numericalInterpretation.obj D :=
  (asIso (coprodComparison numericalInterpretation C D)).symm

@[reassoc (attr := simp)] theorem coproduct_inl (C D : PredicateCategory 𝗣𝗔) :
    numericalInterpretation.map (coprod.inl : C ⟶ C ⨿ D) ≫ (coproductIso C D).hom = coprod.inl :=
  map_inl_inv_coprodComparison numericalInterpretation

@[reassoc (attr := simp)] theorem coproduct_inr (C D : PredicateCategory 𝗣𝗔) :
    numericalInterpretation.map (coprod.inr : D ⟶ C ⨿ D) ≫ (coproductIso C D).hom = coprod.inr :=
  map_inr_inv_coprodComparison numericalInterpretation

def pullbackIso {A B C : PredicateCategory 𝗣𝗔} (f : A ⟶ C) (g : B ⟶ C) :
    numericalInterpretation.obj (pullback f g) ≅
      pullback (numericalInterpretation.map f) (numericalInterpretation.map g) :=
  PreservesPullback.iso numericalInterpretation f g

@[reassoc (attr := simp)] theorem pullback_fst {A B C : PredicateCategory 𝗣𝗔}
    (f : A ⟶ C) (g : B ⟶ C) :
    (pullbackIso f g).hom ≫ pullback.fst _ _ = numericalInterpretation.map (pullback.fst f g) :=
  PreservesPullback.iso_hom_fst numericalInterpretation f g

@[reassoc (attr := simp)] theorem pullback_snd {A B C : PredicateCategory 𝗣𝗔}
    (f : A ⟶ C) (g : B ⟶ C) :
    (pullbackIso f g).hom ≫ pullback.snd _ _ = numericalInterpretation.map (pullback.snd f g) :=
  PreservesPullback.iso_hom_snd numericalInterpretation f g

/-- In standard coordinates these morphisms recover the original ordered
product entries, rather than an arbitrary bijection of label sets. -/
theorem product_fst_value (C D : PredicateCategory 𝗣𝗔)
    (x : NumericalTuples.Point (numericalInterpretation.obj (C ⨯ D))) :
    (prod.fst : numericalInterpretation.obj C ⨯ numericalInterpretation.obj D ⟶ _).toFun
        ((productIso C D).hom.toFun x) =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map prod.fst x := by
  exact (congrArg (fun k => k.toFun x) (product_fst C D)).trans
    (numericalInterpretation_value (prod.fst : C ⨯ D ⟶ C) x)

theorem product_snd_value (C D : PredicateCategory 𝗣𝗔)
    (x : NumericalTuples.Point (numericalInterpretation.obj (C ⨯ D))) :
    (prod.snd : numericalInterpretation.obj C ⨯ numericalInterpretation.obj D ⟶ _).toFun
        ((productIso C D).hom.toFun x) =
      (PredicateInterpretation.functor 𝗣𝗔 ℕ).map prod.snd x := by
  exact (congrArg (fun k => k.toFun x) (product_snd C D)).trans
    (numericalInterpretation_value (prod.snd : C ⨯ D ⟶ D) x)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Geometry
