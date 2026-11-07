/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalCoordinatesCoding
import CategoricalEssentialIncompleteness.V46SyntacticLists

/-! # The actual values of the computable predicate-coordinate charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NumericalCoordinates

private abbrev K := NumericalTuples.classicalTotalEquivalence.functor
private abbrev L := realization 𝗧𝗔 ⋙ NumericalStableLists.standardTotalEquivalence.functor

private def scalarObject (e : Idem ClassicalPrograms.U) :
    PartialSpans.Total (SplitObject ClassicalPrograms.Rec) := ⟨⟨ClassicalPrograms.U,e⟩⟩

private def scalar {a b : Idem ClassicalPrograms.U}
    (f : scalarObject a ⟶ scalarObject b) : ℕ → Part ℕ :=
  ClassicalPrograms.J.map f.hom.hom

private theorem scalarObject_injective : Function.Injective scalarObject := by
  intro a b h
  have hs := congrArg (fun X : PartialSpans.Total (SplitObject ClassicalPrograms.Rec) => X.obj) h
  cases hs
  rfl

private theorem scalar_transport {a b c d : Idem ClassicalPrograms.U}
    (hs : scalarObject a = scalarObject b) (ht : scalarObject c = scalarObject d)
    (f : scalarObject a ⟶ scalarObject c) (g : scalarObject b ⟶ scalarObject d)
    (hv : scalar f = scalar g) : f ≫ eqToHom ht = eqToHom hs ≫ g := by
  have hab : a = b := scalarObject_injective hs
  have hcd : c = d := scalarObject_injective ht
  subst b
  subst d
  have hs' : hs = rfl := Subsingleton.elim _ _
  have ht' : ht = rfl := Subsingleton.elim _ _
  rw [hs',ht',eqToHom_refl,Category.comp_id]
  change f = (𝟙 (scalarObject a)) ≫ g
  rw [Category.id_comp]
  apply WideSubcategory.hom_ext
  apply SplitObject.Hom.ext
  exact ClassicalPrograms.J.map_injective hv

private def predicateProgram {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) : ℕ → Part ℕ :=
  (SyntacticModel.modelFunctor 𝗧𝗔 ℕ).map ((realization 𝗧𝗔).map f).hom.hom

private theorem predicateProgram_partrec {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    Partrec (predicateProgram f) :=
  ClassicalPrograms.omegaArrow_partrec
    (StandardTrueTheory.comparison.map ((realization 𝗧𝗔).map f).hom.hom)

private theorem predicateProgram_graph {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) (x y : ℕ) :
    y ∈ predicateProgram f x ↔ relation 𝗧𝗔 f ℕ x y := by
  have hm := SyntacticModel.mem_model 𝗧𝗔 ℕ ((realization 𝗧𝗔).map f).hom.hom x y
  have ha := SyntacticModel.mem_arrow 𝗧𝗔 ℕ ((realization 𝗧𝗔).map f).hom.hom
    (SyntacticModel.codingEquiv 𝗧𝗔 ℕ (objectCode (omegaObject 𝗧𝗔)) x)
    (SyntacticModel.codingEquiv 𝗧𝗔 ℕ (objectCode (omegaObject 𝗧𝗔)) y)
  exact hm.trans ha

/-- A direct implementation computes the standard graph value on every
carrier input; the representing program may remain partial elsewhere. -/
private def literalMap {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    predicateObject C ⟶ predicateObject D where
  toFun x := (PredicateInterpretation.functor 𝗧𝗔 ℕ).map f x
  represented := ⟨predicateProgram f,predicateProgram_partrec f,by
    intro x
    apply Part.eq_some_iff.mpr
    apply (predicateProgram_graph f x.val _).mpr
    exact (SyntacticLists.map_eq_iff_relation 𝗧𝗔 ℕ f x
      ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map f x)).mp rfl⟩

private theorem standard_scalar {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    scalar (L.map f) = predicateProgram f := rfl

private theorem literal_scalar_graph {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) (x y : ℕ) :
    y ∈ scalar (K.map (literalMap f)) x ↔ relation 𝗧𝗔 f ℕ x y := by
  change y ∈ EnumerableCarriers.val (NumericalTuples.comparisonMap (literalMap f)).hom x ↔ _
  rw [NumericalTuples.comparisonMap_graph]
  change (∃ z : PredicateInterpretation.Obj ℕ C,
    z.val = x ∧ ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map f z).val = y) ↔ _
  constructor
  · rintro ⟨z,hx,hy⟩
    have hr := (SyntacticLists.map_eq_iff_relation 𝗧𝗔 ℕ f z
      ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map f z)).mp rfl
    simpa only [hx,hy] using hr
  · intro hr
    let z : PredicateInterpretation.Obj ℕ C := ⟨x,(relation_support 𝗧𝗔 f ℕ x y hr).1⟩
    let w : PredicateInterpretation.Obj ℕ D := ⟨y,(relation_support 𝗧𝗔 f ℕ x y hr).2⟩
    have h := (SyntacticLists.map_eq_iff_relation 𝗧𝗔 ℕ f z w).mpr hr
    exact ⟨z,rfl,congrArg Subtype.val h⟩

private theorem standard_natural {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    L.map f ≫ eqToHom (standardPredicate_object D) =
      eqToHom (standardPredicate_object C) ≫ K.map (literalMap f) := by
  apply scalar_transport (standardPredicate_object C) (standardPredicate_object D)
  funext x
  apply Part.ext
  intro y
  exact ((by rw [standard_scalar]; exact predicateProgram_graph f x y) :
    y ∈ scalar (L.map f) x ↔ relation 𝗧𝗔 f ℕ x y).trans (literal_scalar_graph f x y).symm

/-- The predicate presentation is an actual numerical isomorphism. -/
def predicateMap {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    predicateObject C ⟶ predicateObject D :=
  (predicatePresentationIso C).inv ≫ NumericalSyntax.predicateEquivalence.functor.map f ≫
    (predicatePresentationIso D).hom

private theorem presentation_map {C : PredicateCategory 𝗧𝗔} :
    K.map (predicatePresentationIso C).hom =
      NumericalTuples.classicalTotalEquivalence.counitIso.hom.app (L.obj C) ≫
        eqToHom (standardPredicate_object C) := by
  simp [predicatePresentationIso]

private theorem presentation_natural_literal {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    NumericalSyntax.predicateEquivalence.functor.map f ≫ (predicatePresentationIso D).hom =
      (predicatePresentationIso C).hom ≫ literalMap f := by
  apply K.map_injective
  rw [Functor.map_comp,Functor.map_comp,presentation_map,presentation_map]
  change K.map (NumericalTuples.classicalTotalEquivalence.inverse.map (L.map f)) ≫
      (NumericalTuples.classicalTotalEquivalence.counitIso.hom.app (L.obj D) ≫
        eqToHom (standardPredicate_object D)) =
    (NumericalTuples.classicalTotalEquivalence.counitIso.hom.app (L.obj C) ≫
      eqToHom (standardPredicate_object C)) ≫ K.map (literalMap f)
  have hn := NumericalTuples.classicalTotalEquivalence.counit_naturality (L.map f)
  change K.map (NumericalTuples.classicalTotalEquivalence.inverse.map (L.map f)) ≫
      NumericalTuples.classicalTotalEquivalence.counitIso.hom.app (L.obj D) =
    NumericalTuples.classicalTotalEquivalence.counitIso.hom.app (L.obj C) ≫ L.map f at hn
  calc
    _ = (NumericalTuples.classicalTotalEquivalence.counitIso.hom.app (L.obj C) ≫
        L.map f) ≫ eqToHom (standardPredicate_object D) := by
      rw [← Category.assoc,hn]
    _ = _ := by rw [Category.assoc,standard_natural,← Category.assoc]

private theorem predicateMap_eq_literal {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    predicateMap f = literalMap f := by
  apply (cancel_epi (predicatePresentationIso C).hom).mp
  simp only [predicateMap,Iso.hom_inv_id_assoc]
  exact presentation_natural_literal f

/-- Point equality fixes both the coordinate and its carrier membership. -/
theorem predicateMap_value {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (predicateObject C)) :
    (predicateMap f).toFun x = (PredicateInterpretation.functor 𝗧𝗔 ℕ).map f x := by
  rw [predicateMap_eq_literal]
  rfl

@[simp] theorem predicateMap_val {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (predicateObject C)) :
    ((predicateMap f).toFun x).val = ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map f x).val :=
  congrArg Subtype.val (predicateMap_value f x)

/-- The diagram uses the actual presentation maps and their actual values. -/
theorem predicatePresentationIso_natural {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    NumericalSyntax.predicateEquivalence.functor.map f ≫ (predicatePresentationIso D).hom =
      (predicatePresentationIso C).hom ≫ predicateMap f := by
  rw [predicateMap_eq_literal]
  exact presentation_natural_literal f

theorem predicatePresentationIso_natural_apply {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D)
    (x : NumericalTuples.Point (NumericalSyntax.predicateEquivalence.functor.obj C)) :
    (predicatePresentationIso D).hom.toFun
      ((NumericalSyntax.predicateEquivalence.functor.map f).toFun x) =
        (PredicateInterpretation.functor 𝗧𝗔 ℕ).map f ((predicatePresentationIso C).hom.toFun x) := by
  have h := congrArg (fun k => k.toFun x) (predicatePresentationIso_natural f)
  simpa only [NumericalTuples.composition_apply,predicateMap_value] using h

end CategoricalEssentialIncompleteness.V46.NumericalCoordinates
