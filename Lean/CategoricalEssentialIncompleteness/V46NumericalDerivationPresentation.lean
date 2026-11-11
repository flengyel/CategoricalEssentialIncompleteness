/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivation
public import CategoricalEssentialIncompleteness.V46NumericalSyntaxTreeChart
public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesValues
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessTransport

/-! # Successful derivations as unary numerical code carriers

The code carrier is the successful-tree predicate. Its output and computation
witnesses are existential. The constructor-preserving comparison is proved by
the original successful pullback, and transports the universal property.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivation
open SyntacticDerivation
abbrev codeEquivalence := NumericalNamed.literalEquivalence
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)

theorem rule_label_iff (i : Fin (N + 1)) (n : ℕ) :
    (codeEquivalence.inverse.obj (PolynomialComparison.coefficients R i.val)).val.Evalb ![n] ↔
      ∃ x : NumericalTuples.Tuple (R.instances i).dimension, x ∈ (R.instances i).support ∧
        NumericalTuples.code (R.instances i).dimension x = n := by
  rw [PolynomialComparison.coefficients_fin]
  exact NumericalSyntaxTreeChart.coefficient_label_iff (R.instances i) n

abbrev rawTreePredicate : PredicateCategory 𝗧𝗔 :=
  NumericalSyntaxTreeChart.treePredicate (PolynomialComparison.coefficients R) N

def literalOrdinaryTree : Endofunctor.Algebra (PolynomialComparison.ordinary R) :=
  PolynomialComparison.mappedAlgebra R
    (NumericalSyntaxTreeChart.literalOneSort (PolynomialComparison.coefficients R) N)

def literalOrdinaryTreeInitial : IsInitial (literalOrdinaryTree R) :=
  PolynomialComparison.mappedInitial R _
    (NumericalSyntaxTreeChart.literalOneSortInitial (PolynomialComparison.coefficients R) N)

def ordinaryWordAlgebraIso : ordinaryTree R ≅ literalOrdinaryTree R :=
  (AlgebraTransport.functor (CategoryTheory.Equivalence.refl :
      NumericalTuples.Object ≌ NumericalTuples.Object)
    (PolynomialComparison.endofunctorComparison R)).mapIso
      (NumericalSyntaxTreeChart.literalOneSortIso (PolynomialComparison.coefficients R) N)

theorem ordinaryWord_constructor :
    (PolynomialComparison.ordinary R).map (ordinaryWordAlgebraIso R).hom.f ≫
        (literalOrdinaryTree R).str =
      (ordinaryTree R).str ≫ (ordinaryWordAlgebraIso R).hom.f :=
  (ordinaryWordAlgebraIso R).hom.h

/-- The raw source is exactly the plain postfix tree predicate. The
comparison is the underlying map of the proved ordinary-tree algebra iso. -/
def rawTreeIso : codeEquivalence.functor.obj (rawTreePredicate R) ≅
    (ordinaryTree R).a :=
  NumericalSyntaxTreeChart.wordPresentationIso (rawTreePredicate R) ≪≫
    ((Endofunctor.Algebra.forget (PolynomialComparison.ordinary R)).mapIso
      (ordinaryWordAlgebraIso R)).symm

def predicateValidator :
    @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (rawTreePredicate R)
      (OptionSyntax.obj (codeEquivalence.inverse.obj F)) :=
  codeEquivalence.functor.preimage
    ((rawTreeIso R).hom ≫ (validatorFold R).f ≫
      (SuccessTransport.mappedOptionCounit codeEquivalence F).inv)

theorem predicateValidator_comparison :
    codeEquivalence.functor.map (predicateValidator R) ≫
        (SuccessTransport.mappedOptionCounit codeEquivalence F).hom =
      (rawTreeIso R).hom ≫ (validatorFold R).f := by
  rw [predicateValidator,Functor.map_preimage]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

def successfulCodes : Carrier := SuccessCarrier.carrier (predicateValidator R)

def codeObject : NumericalTuples.Object := NumericalCoordinates.predicateObject (successfulCodes R)

@[simp] theorem codeObject_dimension : (codeObject R).dimension = 1 := rfl

/-- Membership keeps the original input code; no validator value is stored in it. -/
theorem successfulCodes_mem (d : ℕ) :
    (successfulCodes R).val.Evalb ![d] ↔
      ∃ z : ℕ, (SuccessCarrier.valueGraph (predicateValidator R)).val.Evalb ![d,z] :=
  SuccessCarrier.carrier_eval (predicateValidator R) ℕ d

theorem successfulCodes_word (d : ℕ) (hd : (successfulCodes R).val.Evalb ![d]) :
    (rawTreePredicate R).val.Evalb ![d] := by
  obtain ⟨z,hz⟩ := (successfulCodes_mem R d).mp hd
  exact ((SuccessCarrier.valueGraph_eval (predicateValidator R) ℕ d z).mp hz).1

def codeConclusion : codeObject R ⟶ F :=
  (NumericalSyntaxTreeChart.wordPresentationIso (successfulCodes R)).inv ≫
    codeEquivalence.functor.map
      (representedArrow 𝗧𝗔 (SuccessCarrier.conclusion (predicateValidator R))) ≫
    codeEquivalence.counitIso.hom.app F

def codeTreeInclusion : codeObject R ⟶ (ordinaryTree R).a :=
  (NumericalSyntaxTreeChart.wordPresentationIso (successfulCodes R)).inv ≫
    codeEquivalence.functor.map
      (representedArrow 𝗧𝗔 (SuccessCarrier.inclusion (predicateValidator R))) ≫
    (rawTreeIso R).hom

/-- The inclusion into the literal word carrier fixes every input code. -/
def codeWordInclusion : codeObject R ⟶
    NumericalSyntaxTreeChart.treeObject (PolynomialComparison.coefficients R) N :=
  (NumericalSyntaxTreeChart.wordPresentationIso (successfulCodes R)).inv ≫
    codeEquivalence.functor.map
      (representedArrow 𝗧𝗔 (SuccessCarrier.inclusion (predicateValidator R))) ≫
    (NumericalSyntaxTreeChart.wordPresentationIso (rawTreePredicate R)).hom

theorem codeWordInclusion_value (x : NumericalTuples.Point (codeObject R)) :
    ((codeWordInclusion R).toFun x).val = x.val := by
  change ((NumericalCoordinates.predicateMap
    (representedArrow 𝗧𝗔 (SuccessCarrier.inclusion (predicateValidator R)))).toFun x).val = _
  rw [NumericalCoordinates.predicateMap_val]
  have h := (PredicateInterpretation.map_class_eq_iff 𝗧𝗔 ℕ
    (SuccessCarrier.inclusion (predicateValidator R)) x
    ((SyntacticLists.F 𝗧𝗔 ℕ).map
      (representedArrow 𝗧𝗔 (SuccessCarrier.inclusion (predicateValidator R))) x)).mp rfl
  exact ((SuccessCarrier.inclusionGraph_eval (predicateValidator R) ℕ _ _).mp h).2.symm

/-- The output coordinate is the actual tuple code of the conclusion. -/
def codeEncodedConclusion : codeObject R ⟶
    NumericalCoordinates.predicateObject (codeEquivalence.inverse.obj F) :=
  codeConclusion R ≫ (codeEquivalence.counitIso.app F).inv ≫
    (NumericalSyntaxTreeChart.wordPresentationIso (codeEquivalence.inverse.obj F)).hom

theorem codeEncodedConclusion_value (x : NumericalTuples.Point (codeObject R)) :
    ((codeEncodedConclusion R).toFun x).val =
      NumericalTuples.code F.dimension ((codeConclusion R).toFun x).val :=
  NumericalSyntaxTreeChart.coefficient_input_code F ((codeConclusion R).toFun x)

theorem codeEncodedConclusion_arrow : codeEncodedConclusion R =
    NumericalCoordinates.predicateMap
      (representedArrow 𝗧𝗔 (SuccessCarrier.conclusion (predicateValidator R))) := by
  change (NumericalSyntaxTreeChart.wordPresentationIso (successfulCodes R)).inv ≫
      codeEquivalence.functor.map
        (representedArrow 𝗧𝗔 (SuccessCarrier.conclusion (predicateValidator R))) ≫
      (codeEquivalence.counitIso.app F).hom ≫ (codeEquivalence.counitIso.app F).inv ≫
        (NumericalSyntaxTreeChart.wordPresentationIso (codeEquivalence.inverse.obj F)).hom = _
  simp only [Iso.hom_inv_id_assoc]
  rfl

theorem codeConclusion_graph (x : NumericalTuples.Point (codeObject R)) :
    (SuccessCarrier.valueGraph (predicateValidator R)).val.Evalb (M := ℕ)
      ![x.val,NumericalTuples.code F.dimension ((codeConclusion R).toFun x).val] := by
  rw [← codeEncodedConclusion_value R x,codeEncodedConclusion_arrow R,
    NumericalCoordinates.predicateMap_val]
  exact (PredicateInterpretation.map_class_eq_iff 𝗧𝗔 ℕ
    (SuccessCarrier.conclusion (predicateValidator R)) x
    ((SyntacticLists.F 𝗧𝗔 ℕ).map
      (representedArrow 𝗧𝗔 (SuccessCarrier.conclusion (predicateValidator R))) x)).mp rfl

/-- Both comparisons and the original success square commute. -/
theorem code_isPullback :
    IsPullback (codeTreeInclusion R) (codeConclusion R) (validatorFold R).f
      (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  let E := codeEquivalence
  let u := predicateValidator R
  let : IsIso (SuccessCarrier.comparison u) := SuccessCarrier.comparison_isIso u
  have hp : IsPullback (representedArrow 𝗧𝗔 (SuccessCarrier.inclusion u))
      (representedArrow 𝗧𝗔 (SuccessCarrier.conclusion u)) u coprod.inr :=
    IsPullback.of_iso_pullback ⟨SuccessCarrier.square u⟩
      (asIso (SuccessCarrier.comparison u)) (by simp [SuccessCarrier.comparison])
      (by simp [SuccessCarrier.comparison])
  have hm := hp.map E.functor
  apply hm.of_iso (NumericalSyntaxTreeChart.wordPresentationIso (successfulCodes R))
    (rawTreeIso R) (E.counitIso.app F)
    (SuccessTransport.mappedOptionCounit E F)
  · simp [codeTreeInclusion,E,u]
  · simp [codeConclusion,E,u]
  · exact predicateValidator_comparison R
  · exact SuccessTransport.some_mappedOptionCounit E F

def codeOverIso : Over.mk (codeConclusion R) ≅ (derivationAlgebra R).a :=
  Over.isoMk (code_isPullback R).isoPullback (by simp [derivationAlgebra,
    AlgebraAdjunction.leftAlgebra,validatedSlice,SliceInitial.algebra,validatorFold])

@[simp,reassoc] theorem codeOverIso_tree :
    (codeOverIso R).hom.left ≫ treeInclusion R = codeTreeInclusion R := by
  simp [codeOverIso,treeInclusion]

def codeAlgebra : Endofunctor.Algebra R.inference where
  a := Over.mk (codeConclusion R)
  str := R.inference.map (codeOverIso R).hom ≫ (derivationAlgebra R).str ≫ (codeOverIso R).inv

def codeAlgebraIso : codeAlgebra R ≅ derivationAlgebra R :=
  Endofunctor.Algebra.isoMk (codeOverIso R) (by simp [codeAlgebra,Category.assoc])

def codeInitial : IsInitial (codeAlgebra R) := (derivationInitial R).ofIso (codeAlgebraIso R).symm

/-- The comparison is an algebra morphism for the original inference functor. -/
theorem code_constructor_comparison :
    R.inference.map (codeAlgebraIso R).hom.f ≫ (derivationAlgebra R).str =
      (codeAlgebra R).str ≫ (codeAlgebraIso R).hom.f := (codeAlgebraIso R).hom.h

@[simp,reassoc] theorem code_conclusion_comparison :
    (codeAlgebraIso R).hom.f.left ≫ conclusion R = codeConclusion R :=
  Over.w (codeAlgebraIso R).hom.f

/-- Ordered premises and the original rule label survive unary code presentation. -/
theorem code_constructor_tree :
    (codeAlgebra R).str.left ≫ codeTreeInclusion R =
      InputGeometry.forget R (codeAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map (codeTreeInclusion R) ≫ (ordinaryTree R).str := by
  let e := codeOverIso R
  have hi : e.inv.left ≫ codeTreeInclusion R = treeInclusion R := by
    rw [← codeOverIso_tree R,← Category.assoc]
    simp [e]
  change ((R.inference.map e.hom).left ≫ (derivationAlgebra R).str.left ≫ e.inv.left) ≫ _ = _
  simp only [Category.assoc,hi]
  rw [constructor_tree R]
  have he := congrArg (fun k => k ≫
      (PolynomialComparison.ordinary R).map (treeInclusion R) ≫ (ordinaryTree R).str)
    (InputGeometry.forget_natural R e.hom)
  have hf : (PolynomialComparison.ordinary R).map e.hom.left ≫
      (PolynomialComparison.ordinary R).map (treeInclusion R) ≫ (ordinaryTree R).str =
      (PolynomialComparison.ordinary R).map (codeTreeInclusion R) ≫ (ordinaryTree R).str := by
    rw [← Category.assoc,← Functor.map_comp,codeOverIso_tree R]
  simpa only [Category.assoc,hf,codeAlgebra] using he

def codeFold (B : Endofunctor.Algebra R.inference) : codeAlgebra R ⟶ B := (codeInitial R).to B

theorem codeFold_conclusion (B : Endofunctor.Algebra R.inference) :
    (codeFold R B).f.left ≫ B.a.hom = codeConclusion R := Over.w (codeFold R B).f

theorem codeFold_constructor (B : Endofunctor.Algebra R.inference) :
    (codeAlgebra R).str ≫ (codeFold R B).f = R.inference.map (codeFold R B).f ≫ B.str :=
  (codeFold R B).h.symm

theorem codeFold_unique (B : Endofunctor.Algebra R.inference) (f : codeAlgebra R ⟶ B) :
    f = codeFold R B := (codeInitial R).hom_ext f _

end CategoricalEssentialIncompleteness.V46.NumericalDerivation
