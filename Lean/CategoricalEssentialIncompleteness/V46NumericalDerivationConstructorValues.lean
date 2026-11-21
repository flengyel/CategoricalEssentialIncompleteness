/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationWordConstructors
public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation
public import CategoricalEssentialIncompleteness.V46NumericalNamedValueCertificate

/-! # The numerical finite-rule tree constructor

The numerical input comparison is made from the ordered polynomial comparison and the
tuple-code coefficient counits. Its value is the postfix constructor, with no
comparison hypothesis.
-/

@[expose] public section
noncomputable section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
theorem literalChart_natural {C D : PredicateCategory 𝗧𝗔} (f : C ⟶ D) :
    E.functor.map f ≫ (wordPresentationIso D).hom =
      (wordPresentationIso C).hom ≫ NumericalCoordinates.predicateMap f :=
  NumericalCoordinates.predicatePresentationIso_natural f

variable (R : ℕ → NumericalTuples.Object) (N : ℕ)

abbrev treeTermPolynomial := (SyntaxPolynomial.constructors R N).mapCoefficients E.inverse.obj
abbrev treeFormulaPolynomial (_R : ℕ → NumericalTuples.Object) (_N : ℕ) := (SyntaxPolynomial.unit : SyntaxPolynomial NumericalTuples.Object).mapCoefficients E.inverse.obj
abbrev treeInputPredicate : PredicateCategory 𝗧𝗔 :=
  ((SyntaxPolynomial.jointFunctor (treeTermPolynomial R N) (treeFormulaPolynomial R N)).obj
    (oneSortRaw R N).a).1

/-- Projection, coefficient reindexing, and the polynomial comparison are all
isomorphisms, including the nullary product. -/
def rawTreeInputIso :
    (SyntacticSyntax.constructorFunctor R N).obj (oneSortNormalized R N).a ≅
      E.functor.obj (treeInputPredicate R N) :=
  (asIso (SyntacticSyntax.constructorProjection R N (oneSortMapped R N))).symm ≪≫
    ((CategoryTheory.Prod.fst NumericalTuples.Object NumericalTuples.Object).mapIso
      ((reindexComparison
        (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.constructors R N))
        (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.unit : SyntaxPolynomial NumericalTuples.Object))).app
          (mappedPair (SyntaxPolynomial.constructors R N) .unit).a)).symm ≪≫
      (SyntaxPolynomialTransport.component E E.inverse.obj id
        (fun X => E.counitIso.app X) (SyntaxPolynomial.constructors R N)
        (oneSortRaw R N).a).symm

theorem rawTreeInputIso_hom : (rawTreeInputIso R N).hom = rawConstructorInput R N := rfl

def treeConstructorInputIso :
    (SyntacticSyntax.constructorFunctor R N).obj (treeObject R N) ≅
      NumericalCoordinates.predicateObject (treeInputPredicate R N) :=
  (SyntacticSyntax.constructorFunctor R N).mapIso
      (wordPresentationIso (treePredicate R N)).symm ≪≫
    rawTreeInputIso R N ≪≫ wordPresentationIso (treeInputPredicate R N)

/-- The commuting square is derived from the checked raw constructor and the proved
naturality of the predicate coordinate chart. -/
theorem treeConstructor_square :
    (literalOneSort R N).str ≫ (Iso.refl (treeObject R N)).hom =
      (treeConstructorInputIso R N).hom ≫
        NumericalCoordinates.predicateMap (oneSortRaw R N).str.1 := by
  let c := (SyntacticSyntax.constructorFunctor R N).map
    (wordPresentationIso (treePredicate R N)).inv
  have h0 := congrArg (fun f => c ≫ f ≫ (wordPresentationIso (treePredicate R N)).hom)
    (normalized_raw_constructor R N)
  have hn := literalChart_natural (oneSortRaw R N).str.1
  have h1 := congrArg (fun f => c ≫ rawConstructorInput R N ≫ f) hn
  change (literalOneSort R N).str = _
  exact h0.trans (by simpa only [treeConstructorInputIso,Iso.trans_hom,Functor.mapIso_hom,
    Iso.symm_hom,rawTreeInputIso_hom,Category.assoc,c,treeInputPredicate,
    treeTermPolynomial,treeFormulaPolynomial,oneSortRaw,rawPairAlgebra,
    SyntacticSyntax.plainPostfixAlgebra,treePredicate] using h1)

/-- The root word is the postfix constructor of its ordered raw polynomial input, for
every numerical coefficient family. -/
theorem treeConstructor_value
    (x : NumericalTuples.Point ((SyntacticSyntax.constructorFunctor R N).obj (treeObject R N))) :
    ((literalOneSort R N).str.toFun x).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) false (treeTermPolynomial R N)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map
          (plainRawInput 𝗧𝗔 (treeTermPolynomial R N) (treeFormulaPolynomial R N))
            ((treeConstructorInputIso R N).hom.toFun x)).val) :=
  NumericalNamed.predicate_operation_value (oneSortRaw R N).str.1 (literalOneSort R N).str
    (treeConstructorInputIso R N) (Iso.refl (treeObject R N)) (treeConstructor_square R N)
    (fun y => y.val)
    (fun y => SyntacticSyntax.Coding.constructor (M := ℕ) false (treeTermPolynomial R N)
      (((SyntacticLists.F 𝗧𝗔 ℕ).map
        (plainRawInput 𝗧𝗔 (treeTermPolynomial R N) (treeFormulaPolynomial R N)) y).val))
    (plainTerm_constructor_value 𝗧𝗔 (treeTermPolynomial R N) (treeFormulaPolynomial R N) ℕ) x

end CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart

namespace CategoricalEssentialIncompleteness.V46.NumericalDerivation
open SyntacticDerivation NumericalSyntaxTreeChart

theorem constructor_transport {D : Type u} [Category.{v} D] (S : D ⥤ D)
    {Z I : D} {A B : Endofunctor.Algebra S} (i : A ≅ B)
    (c : I ⟶ Z) (input : I ⟶ S.obj Z) (t : Z ⟶ A.a) (s : Z ⟶ B.a)
    (ht : t ≫ i.hom.f = s) (hc : c ≫ t = input ≫ S.map t ≫ A.str) :
    c ≫ s = input ≫ S.map s ≫ B.str := by
  rw [← ht,← Category.assoc,hc]
  simp only [Category.assoc,i.hom.h.symm,S.map_comp]

variable {F : NumericalTuples.Object} {N : ℕ} (Q : RulePresentation F N)

abbrev ordinaryWordCarrierIso : (ordinaryTree Q).a ≅ (literalOrdinaryTree Q).a :=
  (Endofunctor.Algebra.forget (PolynomialComparison.ordinary Q)).mapIso (ordinaryWordAlgebraIso Q)

theorem algebra_forgetIso_hom {D : Type u} [Category.{v} D] {G : D ⥤ D}
    {A B : Endofunctor.Algebra G} (i : A ≅ B) :
    ((Endofunctor.Algebra.forget G).mapIso i).hom = i.hom.f := rfl

theorem cancel_into_iso {D : Type u} [Category.{v} D] {X A B : D}
    (f : X ⟶ B) (i : A ≅ B) : f ≫ i.inv ≫ i.hom = f := by
  simp only [Iso.inv_hom_id,Category.comp_id]

theorem codeWordInclusion_tree :
    codeTreeInclusion Q ≫ (ordinaryWordAlgebraIso Q).hom.f = codeWordInclusion Q := by
  have h := cancel_into_iso
    (show codeObject Q ⟶ (literalOrdinaryTree Q).a from codeWordInclusion Q)
    (ordinaryWordCarrierIso Q)
  simpa only [codeTreeInclusion,rawTreeIso,Iso.trans_hom,Iso.symm_hom,
    ordinaryWordCarrierIso,algebra_forgetIso_hom,Category.assoc,codeWordInclusion,codeObject] using h

/-- The successful constructor is compared to the ordinary-tree constructor with the
original coefficient and ordered child inclusions. -/
theorem code_constructor_word :
    (codeAlgebra Q).str.left ≫ codeWordInclusion Q =
      InputGeometry.forget Q (codeAlgebra Q).a ≫
        (PolynomialComparison.ordinary Q).map (codeWordInclusion Q) ≫
          (literalOrdinaryTree Q).str := by
  exact constructor_transport (PolynomialComparison.ordinary Q) (ordinaryWordAlgebraIso Q)
    (codeAlgebra Q).str.left (InputGeometry.forget Q (codeAlgebra Q).a)
    (codeTreeInclusion Q) (codeWordInclusion Q) (codeWordInclusion_tree Q) (code_constructor_tree Q)

/-- This is the inference input: each child conclusion is matched to its prescribed
premise by the original pullback before forgetting. -/
def successfulNodeInput
    (u : NumericalTuples.Point ((Q.inference.obj (codeAlgebra Q).a).left)) :
    NumericalTuples.Point ((PolynomialComparison.ordinary Q).obj (literalOrdinaryTree Q).a) :=
  ((InputGeometry.forget Q (codeAlgebra Q).a ≫
    (PolynomialComparison.ordinary Q).map (codeWordInclusion Q)).toFun u)

def ordinaryNodeInput
    (x : NumericalTuples.Point ((PolynomialComparison.ordinary Q).obj (literalOrdinaryTree Q).a)) :
    NumericalTuples.Point ((SyntacticSyntax.constructorFunctor (PolynomialComparison.coefficients Q) N).obj
      (NumericalSyntaxTreeChart.treeObject (PolynomialComparison.coefficients Q) N)) :=
  ((PolynomialComparison.endofunctorComparison Q).inv.app
    (NumericalSyntaxTreeChart.literalOneSort (PolynomialComparison.coefficients Q) N).a).toFun x

theorem literalOrdinaryTree_value
    (x : NumericalTuples.Point ((PolynomialComparison.ordinary Q).obj (literalOrdinaryTree Q).a)) :
    ((literalOrdinaryTree Q).str.toFun x).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) false
        (treeTermPolynomial (PolynomialComparison.coefficients Q) N)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map
          (plainRawInput 𝗧𝗔 (treeTermPolynomial (PolynomialComparison.coefficients Q) N)
            (treeFormulaPolynomial (PolynomialComparison.coefficients Q) N))
              ((treeConstructorInputIso (PolynomialComparison.coefficients Q) N).hom.toFun
                (ordinaryNodeInput Q x))).val) :=
  treeConstructor_value (PolynomialComparison.coefficients Q) N (ordinaryNodeInput Q x)

/-- A successful inference node has exactly the root word. Output and computation
witnesses remain existential properties of that word. -/
theorem code_node
    (u : NumericalTuples.Point ((Q.inference.obj (codeAlgebra Q).a).left)) :
    ((codeAlgebra Q).str.left.toFun u).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) false
        (treeTermPolynomial (PolynomialComparison.coefficients Q) N)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map
          (plainRawInput 𝗧𝗔 (treeTermPolynomial (PolynomialComparison.coefficients Q) N)
            (treeFormulaPolynomial (PolynomialComparison.coefficients Q) N))
              ((treeConstructorInputIso (PolynomialComparison.coefficients Q) N).hom.toFun
                (ordinaryNodeInput Q (successfulNodeInput Q u)))).val) := by
  have h := congrArg (fun k => (k.toFun u).val) (code_constructor_word Q)
  exact (codeWordInclusion_value Q ((codeAlgebra Q).str.left.toFun u)).symm.trans
    (h.trans (literalOrdinaryTree_value Q (successfulNodeInput Q u)))

end CategoricalEssentialIncompleteness.V46.NumericalDerivation
