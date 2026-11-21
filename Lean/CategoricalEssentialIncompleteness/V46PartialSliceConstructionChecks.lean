/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MonicSpanValues
public import CategoricalEssentialIncompleteness.V46MonicPartialMapEquivalence
public import CategoricalEssentialIncompleteness.V46AmbientPartialSlice
public import CategoricalEssentialIncompleteness.V46PartialSliceEquivalence
public import CategoricalEssentialIncompleteness.V46AmbientSliceTuring
public import CategoricalEssentialIncompleteness.V46PartialSliceTuring

/-! # Span comparison, partial slices and their universal computations -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects

section Restriction

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

example {X Y : C} (m : X ⟶ Y) (r s : Y ⟶ X)
    (hmr : m ≫ r = 𝟙 X) (hrm : r ≫ m = rst r)
    (hms : m ≫ s = 𝟙 X) (hsm : s ≫ m = rst s) : r = s :=
  MonicSpanValues.partial_inverse_unique m r s hmr hrm hms hsm

example (inverses : MonoInverses C) {X Y : C} (s t : PartialSpans.Span X Y) :
    s.Isomorphic t ↔ MonicSpanValues.value inverses s = MonicSpanValues.value inverses t :=
  MonicSpanValues.isomorphic_iff_value_eq inverses s t

example [Splits C] (inverses : MonoInverses C) {X Y : C} (f : X ⟶ Y) :
    ∃ s : PartialSpans.Span X Y, MonicSpanValues.value inverses s = f :=
  MonicSpanValues.exists_value inverses f

example [Splits C] [HasPullbacks (Tot C)] (inverses : MonoInverses C) :
    PartialMaps.Par (Tot C) ≌ C := MonicPartialMapEquivalence.selfEquivalence inverses

example [Splits C] [HasPullbacks (Tot C)] (inverses : MonoInverses C) (T : Tot C) :
    PartialMaps.Par (Over T) ≌ AmbientPartialSlice.Family T.obj :=
  PartialSliceEquivalence.equivalence inverses T

example [Splits C] [HasPullbacks (Tot C)] (inverses : MonoInverses C) (T : Tot C)
    {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    (PartialSliceEquivalence.functor inverses T).map (rst f) =
      rst ((PartialSliceEquivalence.functor inverses T).map f) ∧
    (isTotal ((PartialSliceEquivalence.functor inverses T).map f) ↔ isTotal f) :=
  ⟨PartialSliceEquivalence.preserves_restrictions inverses T f,
    PartialSliceEquivalence.total_iff inverses T f⟩

example {T : C} {X Y : AmbientPartialSlice.Family T} (f : X ⟶ Y) :
    f ≫ AmbientPartialSlice.terminate Y = rst f ≫ AmbientPartialSlice.terminate X :=
  AmbientPartialSlice.terminate_naturality f

end Restriction

section Turing

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [Splits C] [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

example {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ PartialSliceTuring.constantObject T Q) :
    rst (PartialSliceTuring.tensorPair inverses T f g) = rst f ≫ rst g ∧
      PartialSliceTuring.tensorPair inverses T f g ≫
        PartialSliceTuring.tensorFst inverses T Q X = rst g ≫ f ∧
      PartialSliceTuring.tensorPair inverses T f g ≫
        PartialSliceTuring.tensorSnd inverses T Q X = rst f ≫ g :=
  ⟨PartialSliceTuring.tensorPair_restriction inverses T f g,
    PartialSliceTuring.tensorPair_fst inverses T f g,
    PartialSliceTuring.tensorPair_snd inverses T f g⟩

example {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ PartialSliceTuring.constantObject T Q)
    (hf : isTotal f) (hg : isTotal g) :
    ∃! h : V ⟶ (PartialSliceTuring.tensorFunctor inverses T Q).obj X, isTotal h ∧
      h ≫ PartialSliceTuring.tensorFst inverses T Q X = f ∧
      h ≫ PartialSliceTuring.tensorSnd inverses T Q X = g :=
  PartialSliceTuring.tensor_product_existsUnique inverses T f g hf hg

example {Q : C} (τ : nearProd Q Q ⟶ Q) (hτ : RecursionCategory.IsTuringMorphism τ)
    (X : PartialMaps.Par (Over T))
    (φ : (PartialSliceTuring.tensorFunctor inverses T Q).obj X ⟶
      PartialSliceTuring.constantObject T Q) :
    ∃ a : X ⟶ PartialSliceTuring.constantObject T Q, isTotal a ∧
      (PartialSliceTuring.tensorFunctor inverses T Q).map a ≫
        PartialSliceTuring.evaluator inverses T τ = φ :=
  PartialSliceTuring.parameterization inverses T τ hτ X φ

example {Q : C} (τ : nearProd Q Q ⟶ Q) :
    ((PartialSliceEquivalence.functor inverses T).map
      (PartialSliceTuring.evaluator inverses T τ)).hom =
        assoc T.obj Q Q ≫ nearProd_map (𝟙 T.obj) τ :=
  PartialSliceTuring.evaluator_value inverses T τ

end Turing

section Splitting

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

example : @Splits (SplitObject R) inferInstance
    (@PCategory.inducedRestriction (SplitObject R) inferInstance
      SplitObject.productData SplitObject.productLaws) := SplitObject.productSplits

example (h : MonoInverses (SplitObject R)) :
    @MonoInverses (SplitObject R) inferInstance
      (@PCategory.inducedRestriction (SplitObject R) inferInstance
        SplitObject.productData SplitObject.productLaws) := by
  rw [SplitObject.productRestriction_eq]
  exact h

example [HasPullbacks (Tot (SplitObject R))] :
    HasPullbacks (@Tot (SplitObject R) inferInstance
      (@PCategory.inducedRestriction (SplitObject R) inferInstance
        SplitObject.productData SplitObject.productLaws)) := by
  rw [SplitObject.productRestriction_eq]
  infer_instance

end Splitting

#print axioms PartialSpans.partial_pullback_lift
#print axioms MonicSpanValues.partial_inverse_unique
#print axioms MonicSpanValues.inverse_comp
#print axioms MonicSpanValues.value_eq_of_isomorphic
#print axioms MonicSpanValues.isomorphic_of_value_eq
#print axioms MonicSpanValues.exists_value
#print axioms MonicSpanValues.inverse_pullback_snd
#print axioms MonicSpanValues.value_pullbackComp
#print axioms MonicPartialMapEquivalence.equivalence
#print axioms MonicPartialMapEquivalence.selfEquivalence
#print axioms MonicPartialMapEquivalence.preserves_restrictions
#print axioms AmbientPartialSlice.terminate_naturality
#print axioms PartialSliceEquivalence.equivalence
#print axioms PartialSliceEquivalence.preserves_restrictions
#print axioms PartialSliceEquivalence.inverse_preserves_restrictions
#print axioms PartialSliceEquivalence.total_iff
#print axioms AmbientSliceTuring.tensorPair_restriction
#print axioms AmbientSliceTuring.tensorPair_fst
#print axioms AmbientSliceTuring.tensorPair_snd
#print axioms AmbientSliceTuring.tensorPair_proj
#print axioms AmbientSliceTuring.tensor_product_existsUnique
#print axioms PartialSliceTuring.tensor_product_existsUnique
#print axioms PartialSliceTuring.tensorPair_restriction
#print axioms PartialSliceTuring.tensorPair_fst
#print axioms PartialSliceTuring.tensorPair_snd
#print axioms PartialSliceTuring.tensorPair_proj
#print axioms PartialSliceTuring.tensorFunctor_restriction
#print axioms AmbientSliceTuring.tensorMap_eq_pair
#print axioms PartialSliceTuring.evaluator_value
#print axioms PartialSliceTuring.parameterization
#print axioms SplitObject.productRestriction_eq
#print axioms SplitObject.productSplits
