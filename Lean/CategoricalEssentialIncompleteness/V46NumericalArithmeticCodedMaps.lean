/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralVariables
import CategoricalEssentialIncompleteness.V46NumericalCoordinatesValues
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateCoordinates

/-! # The actual coded graph and image predicate of a numerical morphism -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.CodedMaps
private abbrev E := NumericalNamed.literalEquivalence
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ
variable {X Y : NumericalTuples.Object}

def encodedMap (f : X ⟶ Y) : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
    (NumericalCoordinates.codedPredicate X) (NumericalCoordinates.codedPredicate Y) :=
  E.inverse.map f

/-- The chosen inverse presentation is decoded by the already proved
coefficient chart; no inverse-equivalence label is identified by fiat. -/
theorem decode_natural (f : X ⟶ Y) :
    NumericalCoordinates.predicateMap (encodedMap f) ≫ (NumericalCoordinates.codedObjectIso Y).hom =
      (NumericalCoordinates.codedObjectIso X).hom ≫ f := by
  apply (cancel_epi (NumericalCoordinates.predicatePresentationIso
    (NumericalCoordinates.codedPredicate X)).hom).1
  have h := E.counitIso.hom.naturality f
  change E.functor.map (encodedMap f) ≫ (NumericalCoordinates.coefficientIso Y).hom =
    (NumericalCoordinates.coefficientIso X).hom ≫ f at h
  calc
    (NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate X)).hom ≫
        (NumericalCoordinates.predicateMap (encodedMap f) ≫ (NumericalCoordinates.codedObjectIso Y).hom) =
      (E.functor.map (encodedMap f) ≫
        (NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate Y)).hom) ≫
          (NumericalCoordinates.codedObjectIso Y).hom := by
            rw [← Category.assoc,← NumericalCoordinates.predicatePresentationIso_natural]
            rfl
    _ = E.functor.map (encodedMap f) ≫ (NumericalCoordinates.coefficientIso Y).hom := by
      simp only [NumericalCoordinates.coefficientIso,Iso.trans_hom,Category.assoc]
    _ = (NumericalCoordinates.coefficientIso X).hom ≫ f := h
    _ = (NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate X)).hom ≫
        ((NumericalCoordinates.codedObjectIso X).hom ≫ f) := by
      simp only [NumericalCoordinates.coefficientIso,Iso.trans_hom,Category.assoc]

theorem encodedMap_value (f : X ⟶ Y)
    (x : PredicateInterpretation.Obj ℕ (NumericalCoordinates.codedPredicate X)) :
    ((F).map (encodedMap f) x).val = NumericalTuples.code Y.dimension
      (f.toFun ((NumericalCoordinates.codedObjectIso X).hom.toFun x)).val := by
  have hn := congrArg (fun g => g.toFun x) (decode_natural f)
  exact (congrArg Subtype.val (NumericalCoordinates.predicateMap_value (encodedMap f) x)).symm.trans
    ((NumericalCoordinates.codedObjectIso_hom_value Y
      ((NumericalCoordinates.predicateMap (encodedMap f)).toFun x)).symm.trans
        (congrArg (fun z => NumericalTuples.code Y.dimension z.val) hn))

def graph (f : X ⟶ Y) : FailureOfComposition.ProofSearch.Graph :=
  (chosenGraph 𝗧𝗔 (encodedMap f)).graph

/-- Tuple decoding is guarded at its real dimension, including zero. -/
theorem graph_eval (f : X ⟶ Y) (a b : ℕ) :
    (graph f).val.Evalb ![a,b] ↔ ∃ x : NumericalTuples.Point X,
      NumericalTuples.code X.dimension x.val = a ∧
      NumericalTuples.code Y.dimension (f.toFun x).val = b := by
  constructor
  · intro h
    have hs := (chosenGraph 𝗧𝗔 (encodedMap f)).support_model ℕ a b h
    let z : PredicateInterpretation.Obj ℕ (NumericalCoordinates.codedPredicate X) := ⟨a,hs.1⟩
    have hv : ((F).map (encodedMap f) z).val = b :=
      (ConcreteNamedComparison.chosenGraph_value_iff 𝗧𝗔 ℕ (encodedMap f) z b).mp h
    refine ⟨(NumericalCoordinates.codedObjectIso X).hom.toFun z,
      NumericalCoordinates.codedObjectIso_hom_value X z,?_⟩
    exact (encodedMap_value f z).symm.trans hv
  · rintro ⟨x,rfl,rfl⟩
    let z := NumericalCoordinates.encodePoint X x
    have hd : (NumericalCoordinates.codedObjectIso X).hom.toFun z = x :=
      congrArg (fun g => g.toFun x) (NumericalCoordinates.codedObjectIso X).inv_hom_id
    apply (ConcreteNamedComparison.chosenGraph_value_iff 𝗧𝗔 ℕ (encodedMap f) z _).mpr
    exact (encodedMap_value f z).trans
      (congrArg (fun y => NumericalTuples.code Y.dimension (f.toFun y).val) hd)

def imagePredicate (f : X ⟶ Y) : Carrier := imageCarrier (graph f)

theorem imagePredicate_eval (f : X ⟶ Y) (b : ℕ) :
    (imagePredicate f).val.Evalb ![b] ↔
      ∃ x : NumericalTuples.Point X, NumericalTuples.code Y.dimension (f.toFun x).val = b := by
  rw [imagePredicate,imageCarrier_eval]
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨x,_,hx⟩ := (graph_eval f a b).mp ha
    exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨NumericalTuples.code X.dimension x.val,(graph_eval f _ b).mpr ⟨x,rfl,hx⟩⟩

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.CodedMaps
