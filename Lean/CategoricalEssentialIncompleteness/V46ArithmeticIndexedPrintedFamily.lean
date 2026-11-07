/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedAxiomsExponential
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersPresentation

/-! # The printed exponential coefficient and the actual indexed initial algebra

The proved coefficient mono square induces a comparison of the original
ordered rules. Initiality, numeral fibers and sentence images are then
transported with their constructor and conclusion equations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPrintedFamily
open ArithmeticIndexedFibers

namespace Signature
variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]

omit [HasFiniteCoproducts C] in
private theorem power_refl (F : C) (n : ℕ) :
    (InferenceTransport.power (CategoryTheory.Equivalence.refl (C := C)) F n).hom = 𝟙 (finitePower F n) := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [InferenceTransport.power,Iso.trans_hom,asIso_hom,prod.mapIso_hom,Iso.refl_hom,ih]
      change prodComparison (𝟭 C) (finitePower F (n + 1)) F ≫
        prod.map (𝟙 (finitePower F (n + 1))) (𝟙 F) = 𝟙 (finitePower F (n + 1) ⨯ F)
      apply prod.hom_ext <;> simp [prodComparison,prod.map]

variable (E : C) {V F L S A A' : C}
variable (logical : L ⟶ F) (sentence : S ⟶ F)
variable (axioms : A ⟶ E ⨯ S) (axioms' : A' ⟶ E ⨯ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) (a : A ≅ A')

private def coefficient : ∀ i : Fin 3,
    (ArithmeticIndexedRules.rules E logical sentence axioms all imp).instances i ≅
      (ArithmeticIndexedRules.rules E logical sentence axioms' all imp).instances i :=
  Fin.cases (coprod.mapIso (Iso.refl _) a)
    (Fin.cases (Iso.refl _) (Fin.cases (Iso.refl _) (fun i => Fin.elim0 i)))

/-- Only an original coefficient square is supplied; every ordered rule
and conclusion equation of the inference comparison is proved here. -/
def data (h : a.hom ≫ axioms' = axioms) :
    InferenceTransport.Data (CategoryTheory.Equivalence.refl (C := C))
      (ArithmeticIndexedRules.rules E logical sentence axioms all imp)
      (ArithmeticIndexedRules.rules E logical sentence axioms' all imp) where
  coefficient := coefficient E logical sentence axioms axioms' all imp a
  premises i := by
    change (ArithmeticIndexedRules.rules E logical sentence axioms all imp).premises i ≫
        (InferenceTransport.power (CategoryTheory.Equivalence.refl (C := C)) (E ⨯ F) i.val).hom = _
    rw [power_refl,Category.comp_id]
    fin_cases i
    · exact terminal.hom_ext _ _
    · change prod.lift prod.fst (prod.snd ≫ prod.snd) =
        𝟙 (E ⨯ (V ⨯ F)) ≫ prod.lift prod.fst (prod.snd ≫ prod.snd)
      exact (Category.id_comp _).symm
    · change prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
          (prod.lift prod.fst (prod.snd ≫ imp)) =
        𝟙 (E ⨯ (F ⨯ F)) ≫ prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
          (prod.lift prod.fst (prod.snd ≫ imp))
      exact (Category.id_comp _).symm
  conclusion i := by
    fin_cases i
    · change coprod.desc (prod.map (𝟙 E) logical) (axioms ≫ prod.map (𝟙 E) sentence) =
        (coprod.mapIso (Iso.refl (E ⨯ L)) a).hom ≫
          coprod.desc (prod.map (𝟙 E) logical) (axioms' ≫ prod.map (𝟙 E) sentence)
      apply coprod.hom_ext
      · simp only [coprod.inl_desc,coprod.mapIso_hom,
          coprod.inl_map_assoc,Iso.refl_hom,Category.id_comp,coprod.inl_desc]
      · simp only [coprod.inr_desc,coprod.mapIso_hom,coprod.inr_map_assoc]
        rw [← Category.assoc,h]
    · change prod.map (𝟙 E) all = 𝟙 _ ≫ prod.map (𝟙 E) all
      exact (Category.id_comp _).symm
    · change prod.map (𝟙 E) (prod.snd : F ⨯ F ⟶ F) =
        𝟙 _ ≫ prod.map (𝟙 E) (prod.snd : F ⨯ F ⟶ F)
      exact (Category.id_comp _).symm
end Signature

/-- The printed A₀ coefficient is used directly in the manuscript rule signature. -/
def rules (AxPA : Carrier) : RulePresentation
    (ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.formula) 2 :=
  ArithmeticIndexedRules.rules ArithmeticIndexedFamily.parameter ArithmeticIndexedFamily.logical
    ArithmeticIndexedFamily.sentenceInclusion (ArithmeticIndexedAxioms.Exponential.printedAxioms AxPA)
    ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication

/-- The actual source/realized mono square supplies the concrete data. -/
def coefficientData (AxPA : Carrier) : InferenceTransport.Data (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔))
    (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) :=
  Signature.data ArithmeticIndexedFamily.parameter ArithmeticIndexedFamily.logical
    ArithmeticIndexedFamily.sentenceInclusion (ArithmeticIndexedAxioms.axioms AxPA)
    (ArithmeticIndexedAxioms.Exponential.printedAxioms AxPA)
    ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication
    ((realization 𝗣𝗔).mapIso (ArithmeticIndexedAxioms.Exponential.carrierIso AxPA))
    (ArithmeticIndexedAxioms.Exponential.realized_square AxPA)

def inferenceComparison (AxPA : Carrier) :=
  InferenceTransport.comparison (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔))
    (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) (coefficientData AxPA)

def algebraEquivalence (AxPA : Carrier) :=
  InferenceTransport.algebraEquivalence (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔))
    (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) (coefficientData AxPA)

/-- The printed algebra is constructed by arbitrary-rule initiality. -/
def algebra (AxPA : Carrier) : Endofunctor.Algebra (rules AxPA).inference :=
  ArithmeticIndexedRules.algebra 𝗣𝗔 ArithmeticIndexedFamily.parameter ArithmeticIndexedFamily.logical
    ArithmeticIndexedFamily.sentenceInclusion (ArithmeticIndexedAxioms.Exponential.printedAxioms AxPA)
    ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication

def initial (AxPA : Carrier) : IsInitial (algebra AxPA) :=
  ArithmeticIndexedRules.initial 𝗣𝗔 ArithmeticIndexedFamily.parameter ArithmeticIndexedFamily.logical
    ArithmeticIndexedFamily.sentenceInclusion (ArithmeticIndexedAxioms.Exponential.printedAxioms AxPA)
    ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication

def transportedRaw (AxPA : Carrier) : Endofunctor.Algebra (rules AxPA).inference :=
  (algebraEquivalence AxPA).functor.obj (ArithmeticIndexedFamily.algebra AxPA)

def transportedRawInitial (AxPA : Carrier) : IsInitial (transportedRaw AxPA) :=
  InferenceTransport.mappedInitial (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔))
    (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) (coefficientData AxPA)
    (ArithmeticIndexedFamily.algebra AxPA) (ArithmeticIndexedFamily.initial AxPA)

/-- This is an isomorphism of inference algebras, including all constructors. -/
def algebraIso (AxPA : Carrier) : algebra AxPA ≅ transportedRaw AxPA :=
  (initial AxPA).uniqueUpToIso (transportedRawInitial AxPA)

def carrierIso (AxPA : Carrier) : (algebra AxPA).a.left ≅
    (ArithmeticIndexedFamily.algebra AxPA).a.left :=
  InferenceTransport.carrierIso (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔))
    (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) (coefficientData AxPA)
    (ArithmeticIndexedFamily.algebra AxPA) (algebra AxPA) (algebraIso AxPA)

def conclusion (AxPA : Carrier) : (algebra AxPA).a.left ⟶
    ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.formula := (algebra AxPA).a.hom

@[reassoc] theorem carrierIso_conclusion (AxPA : Carrier) :
    (carrierIso AxPA).hom ≫ ArithmeticIndexedFamily.conclusion AxPA = conclusion AxPA :=
  InferenceTransport.carrierIso_conclusion (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔))
    (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) (coefficientData AxPA)
    (ArithmeticIndexedFamily.algebra AxPA) (algebra AxPA) (algebraIso AxPA)

section GenericTransport
variable {C : Type u} [Category.{v} C] [Regular C]
private theorem pullbackSquare {P Q X Y : C} (f : P ⟶ X) (g : Q ⟶ X) (j : Y ⟶ X)
    (i : P ≅ Q) (h : i.hom ≫ g = f) :
    IsPullback (pullback.fst f j ≫ i.hom) (pullback.snd f j) g j := by
  apply (IsPullback.of_hasPullback f j).of_iso (Iso.refl _) i (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simpa only [Iso.refl_hom,Category.comp_id] using h.symm
  · simp

private def pullbackIso {P Q X Y : C} (f : P ⟶ X) (g : Q ⟶ X) (j : Y ⟶ X)
    (i : P ≅ Q) (h : i.hom ≫ g = f) : pullback f j ≅ pullback g j :=
  (pullbackSquare f g j i h).isoPullback

@[reassoc] private theorem pullbackIso_snd {P Q X Y : C}
    (f : P ⟶ X) (g : Q ⟶ X) (j : Y ⟶ X) (i : P ≅ Q) (h : i.hom ≫ g = f) :
    (pullbackIso f g j i h).hom ≫ pullback.snd g j = pullback.snd f j :=
  (pullbackSquare f g j i h).isoPullback_hom_snd

private def carriedAlgebra {H : C ⥤ C} (A : Endofunctor.Algebra H) {X : C} (i : X ≅ A.a) :
    Endofunctor.Algebra H where
  a := X
  str := H.map i.hom ≫ A.str ≫ i.inv

private def carriedIso {H : C ⥤ C} (A : Endofunctor.Algebra H) {X : C} (i : X ≅ A.a) :
    carriedAlgebra A i ≅ A :=
  Endofunctor.Algebra.isoMk i (by simp only [carriedAlgebra,Category.assoc,Iso.inv_hom_id,Category.comp_id])

omit [Regular C] in
@[reassoc] private theorem iso_inv_conclusion {P Q X : C} (i : P ≅ Q)
    (f : Q ⟶ X) (f' : P ⟶ X) (h : i.hom ≫ f = f') : i.inv ≫ f' = f := by
  have hh := congrArg (fun k => i.inv ≫ k) h
  simpa only [Iso.inv_hom_id_assoc] using hh.symm

omit [Regular C] in
private theorem presentation_change {A P Q X Y : C} (a : A ⟶ Q)
    (i : P ≅ Q) (f : Q ⟶ X) (f' : P ⟶ X) (g : X ⟶ Y)
    (h : i.hom ≫ f = f') : a ≫ i.inv ≫ f' ≫ g = a ≫ f ≫ g := by
  rw [iso_inv_conclusion_assoc i f f' h]

omit [Regular C] in
private theorem changeRight {P X X' Y Z : C} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (p : IsPullback a b f g)
    (i : X' ≅ X) (f' : X' ⟶ Z) (h : i.hom ≫ f = f') :
    IsPullback (a ≫ i.inv) b f' g := by
  have hi : i.inv ≫ f' = f := by
    have hh := congrArg (fun k => i.inv ≫ k) h
    simpa only [Iso.inv_hom_id_assoc] using hh.symm
  exact p.of_iso (Iso.refl _) i.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa only [Iso.symm_hom,Iso.refl_hom,Category.comp_id] using hi.symm) (by simp)
end GenericTransport

def fiberCarrierIso (AxPA : Carrier) (e : ℕ) :
    pullback (conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula) ≅
      pullback (ArithmeticIndexedFamily.conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula) :=
  pullbackIso (conclusion AxPA) (ArithmeticIndexedFamily.conclusion AxPA)
    (fiberMap e ArithmeticIndexedFamily.formula) (carrierIso AxPA) (carrierIso_conclusion AxPA)

def fiberOverIso (AxPA : Carrier) (e : ℕ) :
    Over.mk (pullback.snd (conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula)) ≅
      (ArithmeticIndexedFibers.fiberAlgebra AxPA e).a :=
  Over.isoMk (fiberCarrierIso AxPA e)
    (pullbackIso_snd (conclusion AxPA) (ArithmeticIndexedFamily.conclusion AxPA)
      (fiberMap e ArithmeticIndexedFamily.formula) (carrierIso AxPA) (carrierIso_conclusion AxPA))

def fiberAlgebra (AxPA : Carrier) (e : ℕ) :
    Endofunctor.Algebra (ArithmeticIndexedFibers.singleRules AxPA e).inference :=
  carriedAlgebra (ArithmeticIndexedFibers.fiberAlgebra AxPA e) (fiberOverIso AxPA e)

def fiberInitial (AxPA : Carrier) (e : ℕ) : IsInitial (fiberAlgebra AxPA e) :=
  (ArithmeticIndexedFibers.fiberInitial AxPA e).ofIso
    (carriedIso (ArithmeticIndexedFibers.fiberAlgebra AxPA e) (fiberOverIso AxPA e)).symm

/-- Constructor-preserving comparison with the original actual numeral fiber. -/
def fiberAlgebraIso (AxPA : Carrier) (e : ℕ) :
    fiberAlgebra AxPA e ≅ ArithmeticIndexedFibers.fiberAlgebra AxPA e :=
  carriedIso (ArithmeticIndexedFibers.fiberAlgebra AxPA e) (fiberOverIso AxPA e)

def individualFiberAlgebraIso (AxPA : Carrier) (e : ℕ) :
    ArithmeticIndexedFibers.individualAlgebra AxPA e ≅ fiberAlgebra AxPA e :=
  (ArithmeticIndexedFibers.individualInitial AxPA e).uniqueUpToIso (fiberInitial AxPA e)

@[simp] theorem fiberAlgebra_carrier (AxPA : Carrier) (e : ℕ) :
    (fiberAlgebra AxPA e).a =
      Over.mk (pullback.snd (conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula)) := rfl

def sentenceProof (AxPA : Carrier) : TotalSplit 𝗣𝗔 :=
  pullback (conclusion AxPA) (prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion)

def sentenceConclusion (AxPA : Carrier) : sentenceProof AxPA ⟶
    ArithmeticIndexedFamily.parameter ⨯ ArithmeticIndexedFamily.sentence := pullback.snd _ _

def sentenceIso (AxPA : Carrier) : sentenceProof AxPA ≅ ArithmeticIndexedFamily.sentenceProof AxPA :=
  pullbackIso (conclusion AxPA) (ArithmeticIndexedFamily.conclusion AxPA)
    (prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion)
    (carrierIso AxPA) (carrierIso_conclusion AxPA)

@[reassoc] theorem sentenceIso_conclusion (AxPA : Carrier) :
    (sentenceIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA = sentenceConclusion AxPA :=
  pullbackIso_snd (conclusion AxPA) (ArithmeticIndexedFamily.conclusion AxPA)
    (prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion)
    (carrierIso AxPA) (carrierIso_conclusion AxPA)

/-- The same selected predicate P₀ presents the printed family sentence proofs. -/
def proofPresentationIso (AxPA : Carrier) :
    (realization 𝗣𝗔).obj (ArithmeticIndexedProvability.proofCarrier AxPA) ≅ sentenceProof AxPA :=
  ArithmeticIndexedProvability.proofPresentationIso AxPA ≪≫ (sentenceIso AxPA).symm

/-- The printed source conclusion is compared to the initial algebra using
its printed coefficient, not only to the intermediate raw family. -/
theorem printedConclusion_realization (AxPA : Carrier) :
    (realization 𝗣𝗔).map (ArithmeticIndexedProvability.printedConclusion AxPA) =
      (proofPresentationIso AxPA).hom ≫ sentenceConclusion AxPA ≫
        ArithmeticIndexedProvability.printedProductIso.inv := by
  have h := presentation_change (ArithmeticIndexedProvability.proofPresentationIso AxPA).hom
    (sentenceIso AxPA) (ArithmeticIndexedFamily.sentenceConclusion AxPA)
    (sentenceConclusion AxPA) ArithmeticIndexedProvability.printedProductIso.inv
    (sentenceIso_conclusion AxPA)
  exact (ArithmeticIndexedProvability.printedConclusion_realization AxPA).trans (by
    simpa only [proofPresentationIso,Iso.trans_hom,Iso.symm_hom,Category.assoc] using h.symm)

def sentenceMap (AxPA : Carrier) (e : ℕ) : ArithmeticIndexedFibers.individualSentenceProof AxPA e ⟶
    sentenceProof AxPA := ArithmeticIndexedFibers.sentenceMap AxPA e ≫ (sentenceIso AxPA).inv

theorem sentence_pullback (AxPA : Carrier) (e : ℕ) :
    IsPullback (sentenceMap AxPA e) (ArithmeticIndexedFibers.individualSentenceConclusion AxPA e)
      (sentenceConclusion AxPA) (fiberMap e ArithmeticIndexedFamily.sentence) :=
  changeRight (ArithmeticIndexedFibers.sentence_pullback AxPA e)
    (sentenceIso AxPA) (sentenceConclusion AxPA) (sentenceIso_conclusion AxPA)

theorem sentenceTheory_fiber (AxPA : Carrier) (e : ℕ) :
    imageSubobject (ArithmeticIndexedFibers.individualSentenceConclusion AxPA e) =
      (Subobject.pullback (fiberMap e ArithmeticIndexedFamily.sentence)).obj
        (imageSubobject (sentenceConclusion AxPA)) :=
  ArithmeticIndexedFibers.pullback_image (sentence_pullback AxPA e)

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPrintedFamily
