/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionTransport
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionModels
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralConstructorValues

/-! # The exact numerical distribution domain in literal word coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionValues
open SyntaxOperationsTransport
local notation "E" => NumericalNamed.literalEquivalence
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ

/-- Both directions of the point-image comparison use numerical isomorphisms, rather than
an assumed equality of chosen syntax carriers. -/
theorem presented_image_iff {A B : NumericalTuples.Object}
    (C D : PredicateCategory 𝗧𝗔) (f : A ⟶ B) (g : C ⟶ D)
    (i : A ≅ NumericalCoordinates.predicateObject C)
    (j : B ≅ NumericalCoordinates.predicateObject D)
    (h : f ≫ j.hom = i.hom ≫ NumericalCoordinates.predicateMap g)
    (x : NumericalTuples.Point B) :
    (∃ a, f.toFun a = x) ↔ ∃ c : PredicateInterpretation.Obj ℕ C, (F).map g c = j.hom.toFun x := by
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨i.hom.toFun a,?_⟩
    have hp := congrArg (fun m => m.toFun a) h
    exact (NumericalCoordinates.predicateMap_value g _).symm.trans
      (hp.symm.trans (congrArg j.hom.toFun ha))
  · rintro ⟨c,hc⟩
    let a := i.inv.toFun c
    refine ⟨a,?_⟩
    have hi : i.hom.toFun a = c := congrArg (fun m => m.toFun c) i.inv_hom_id
    have hp := congrArg (fun m => m.toFun a) h
    have he : j.hom.toFun (f.toFun a) = j.hom.toFun x :=
      hp.trans ((congrArg (NumericalCoordinates.predicateMap g).toFun hi).trans
        ((NumericalCoordinates.predicateMap_value g c).trans hc))
    exact (congrArg (fun m => m.toFun (f.toFun a)) j.hom_inv_id).symm.trans
      ((congrArg j.inv.toFun he).trans (congrArg (fun m => m.toFun x) j.hom_inv_id))

section Presented
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
variable (R₀ : CategoricalSyntax ((E).inverse.obj V)
  (fun n => (E).inverse.obj (σ n)) (fun n => (E).inverse.obj (π n)) d)
variable (R₁ : CategoricalSyntax V σ π d)
variable (hLists : R₁.lists = SyntacticLists.Transport.mappedStableListAlgebra (E)
  ((E).inverse.obj V) V ((E).counitIso.app V) R₀.lists)
variable (c : mappedSyntaxAlgebra (E) V σ π d R₀ ≅ R₁.algebra)

abbrev presentedSourceBase : PredicateCategory 𝗧𝗔 := Limits.prod (C := PredicateCategory 𝗧𝗔)
  ((E).inverse.obj V) (Limits.prod (C := PredicateCategory 𝗧𝗔) R₀.algebra.a.2 R₀.algebra.a.2)
abbrev presentedTargetBase : NumericalTuples.Object := V ⨯ (R₁.algebra.a.2 ⨯ R₁.algebra.a.2)

/-- The whole coordinate comparison is checked with opaque syntax records
before either record is instantiated with a chosen initial algebra. -/
def presentedBase : presentedTargetBase V σ π d R₁ ≅
    NumericalCoordinates.predicateObject (presentedSourceBase V σ π d R₀) :=
  (DistributionTransport.baseIso (E) V σ π d R₀ R₁ c).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (presentedSourceBase V σ π d R₀)

include hLists in
def presentedFiber : R₁.distributionParameters ≅ NumericalCoordinates.predicateObject R₀.distributionParameters :=
  (DistributionTransport.fiberIso (E) V σ π d R₀ R₁ hLists c).symm ≪≫
    NumericalCoordinates.predicatePresentationIso R₀.distributionParameters

include hLists in
theorem presented_inclusion_square :
    R₁.distributionInclusion ≫ (presentedBase V σ π d R₀ R₁ c).hom =
      (presentedFiber V σ π d R₀ R₁ hLists c).hom ≫
        NumericalCoordinates.predicateMap R₀.distributionInclusion :=
  NumericalNamed.conjugate_operation ((E).functor.map R₀.distributionInclusion)
    R₁.distributionInclusion (DistributionTransport.fiberIso (E) V σ π d R₀ R₁ hLists c)
    (DistributionTransport.baseIso (E) V σ π d R₀ R₁ c)
    (NumericalCoordinates.predicatePresentationIso R₀.distributionParameters)
    (NumericalCoordinates.predicatePresentationIso (presentedSourceBase V σ π d R₀))
    (DistributionTransport.fiberIso_inclusion (E) V σ π d R₀ R₁ hLists c).symm

theorem presentedBase_name (q : NumericalTuples.Point (presentedTargetBase V σ π d R₁)) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (presentedSourceBase V σ π d R₀) ((E).inverse.obj V))
      ((presentedBase V σ π d R₀ R₁ c).hom.toFun q) =
        (NumericalNamed.literalVariablePresentationIso V).hom.toFun
          ((prod.fst : presentedTargetBase V σ π d R₁ ⟶ V).toFun q) :=
  @NumericalNamed.presentedProduct_fst_value ((E).inverse.obj V)
    (Limits.prod (C := PredicateCategory 𝗧𝗔) R₀.algebra.a.2 R₀.algebra.a.2)
    V (R₁.algebra.a.2 ⨯ R₁.algebra.a.2) ((E).counitIso.app V)
    (SyntaxOptionTransport.productIso (E)
      (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
      (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)) q

theorem presentedBase_formula (q : NumericalTuples.Point (presentedTargetBase V σ π d R₁)) :
    (F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (Limits.prod (C := PredicateCategory 𝗧𝗔) R₀.algebra.a.2 R₀.algebra.a.2) R₀.algebra.a.2)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        (presentedSourceBase V σ π d R₀)
        (Limits.prod (C := PredicateCategory 𝗧𝗔) R₀.algebra.a.2 R₀.algebra.a.2))
          ((presentedBase V σ π d R₀ R₁ c).hom.toFun q)) =
      (NumericalNamed.presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun
        ((prod.fst : R₁.algebra.a.2 ⨯ R₁.algebra.a.2 ⟶ R₁.algebra.a.2).toFun
          ((prod.snd : presentedTargetBase V σ π d R₁ ⟶ R₁.algebra.a.2 ⨯ R₁.algebra.a.2).toFun q)) := by
  have ho := @NumericalNamed.presentedProduct_snd_value ((E).inverse.obj V)
    (Limits.prod (C := PredicateCategory 𝗧𝗔) R₀.algebra.a.2 R₀.algebra.a.2)
    V (R₁.algebra.a.2 ⨯ R₁.algebra.a.2) ((E).counitIso.app V)
    (SyntaxOptionTransport.productIso (E)
      (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
      (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)) q
  have hi := @NumericalNamed.presentedProduct_fst_value R₀.algebra.a.2 R₀.algebra.a.2
    R₁.algebra.a.2 R₁.algebra.a.2
    (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
    (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
    ((prod.snd : presentedTargetBase V σ π d R₁ ⟶ R₁.algebra.a.2 ⨯ R₁.algebra.a.2).toFun q)
  exact (congrArg ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
    (Limits.prod (C := PredicateCategory 𝗧𝗔) R₀.algebra.a.2 R₀.algebra.a.2) R₀.algebra.a.2)) ho).trans hi
end Presented

section Actual
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => NumericalNamed.literalSourceSyntax V σ π d
local notation "S₁" => NumericalNamed.literalCategoricalSyntax V σ π d

abbrev sourceBase : PredicateCategory 𝗧𝗔 := presentedSourceBase V σ π d (S₀)
abbrev targetBase : NumericalTuples.Object := presentedTargetBase V σ π d (S₁)

abbrev literalBaseIso := DistributionTransport.baseIso (E) V σ π d (S₀) (S₁)
  (NumericalNamed.literalAlgebraIso V σ π d)
abbrev literalFiberIso := DistributionTransport.fiberIso (E) V σ π d (S₀) (S₁)
  (NumericalNamed.literalListsEquality V σ π d) (NumericalNamed.literalAlgebraIso V σ π d)

def basePresentation := presentedBase V σ π d (S₀) (S₁) (NumericalNamed.literalAlgebraIso V σ π d)
def fiberPresentation := presentedFiber V σ π d (S₀) (S₁)
  (NumericalNamed.literalListsEquality V σ π d) (NumericalNamed.literalAlgebraIso V σ π d)

abbrev inclusion_square := presented_inclusion_square V σ π d (S₀) (S₁)
  (NumericalNamed.literalListsEquality V σ π d) (NumericalNamed.literalAlgebraIso V σ π d)

/-- The binder coordinate is the guarded tuple code. -/
theorem base_name_value (q : NumericalTuples.Point (targetBase V σ π d)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
      (sourceBase V σ π d) (NumericalCoordinates.codedPredicate V))
      ((basePresentation V σ π d).hom.toFun q)).val =
      NumericalTuples.code V.dimension ((prod.fst : targetBase V σ π d ⟶ V).toFun q).val :=
  (congrArg Subtype.val
    (presentedBase_name V σ π d (S₀) (S₁) (NumericalNamed.literalAlgebraIso V σ π d) q)).trans
      (NumericalNamed.literalVariablePresentation_value V
        ((prod.fst : targetBase V σ π d ⟶ V).toFun q))

/-- The absence test concerns the first of the two formula entries. -/
theorem base_formula_value (q : NumericalTuples.Point (targetBase V σ π d)) :
    ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2) (S₀).algebra.a.2)
      ((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
        (sourceBase V σ π d)
        (Limits.prod (C := PredicateCategory 𝗧𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2))
          ((basePresentation V σ π d).hom.toFun q))).val =
      ((NumericalNamed.literalFormulaPresentationIso V σ π d).hom.toFun
        ((prod.fst : (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun
          ((prod.snd : targetBase V σ π d ⟶ (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2).toFun q))).val :=
  congrArg Subtype.val
    (presentedBase_formula V σ π d (S₀) (S₁) (NumericalNamed.literalAlgebraIso V σ π d) q)

/-- The numerical label fiber is characterized by the independently proved named
membership flag at the input word coordinates. -/
abbrev parameter_image_iff (q : NumericalTuples.Point (targetBase V σ π d)) :=
  (presented_image_iff (S₀).distributionParameters (sourceBase V σ π d)
    (S₁).distributionInclusion (S₀).distributionInclusion
    (fiberPresentation V σ π d) (basePresentation V σ π d) (inclusion_square V σ π d) q).trans
    (DistributionModels.parameter_image_iff 𝗧𝗔 (NumericalCoordinates.codedPredicate V)
      (fun k => NumericalCoordinates.codedPredicate (σ k))
      (fun k => NumericalCoordinates.codedPredicate (π k)) d ℕ
      ((basePresentation V σ π d).hom.toFun q))
end Actual
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionValues
