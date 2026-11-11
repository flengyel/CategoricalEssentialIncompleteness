/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersConstructors

/-! # Initial numeral fibers and the arithmetic sentence-theory pullback

Both comparisons of inference functors are derived from the actual rule
coefficients. The extensive slice equivalence then transports the full
family algebra to a product of algebras, whose first component is initial.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
variable (AxPA : Carrier) (e : ℕ)

def complementRules : RulePresentation (complement e ⨯ ArithmeticIndexedFamily.formula) 2 :=
  parameterRules (ArithmeticIndexedFamily.rules AxPA) (complementInclusion e)

def complementInferenceComparison :
    (ArithmeticIndexedFamily.rules AxPA).inference ⋙
        Over.pullback (complementMap e ArithmeticIndexedFamily.formula) ≅
      Over.pullback (complementMap e ArithmeticIndexedFamily.formula) ⋙
        (complementRules AxPA e).inference :=
  parameterInferenceComparisonAlong (ArithmeticIndexedFamily.rules AxPA) (complementInclusion e)
    (familyParameterPreserving ArithmeticIndexedFamily.parameter ArithmeticIndexedFamily.logical
      ArithmeticIndexedFamily.sentenceInclusion (ArithmeticIndexedAxioms.axioms AxPA)
      ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication)
    (complementMap e ArithmeticIndexedFamily.formula)
    (complementMap_primitive e ArithmeticIndexedFamily.formula)

/-- The inference natural isomorphism over the actual two pullback
functors follows from the constructor comparisons already proved. -/
def inferenceComparison :
    (ArithmeticIndexedFamily.rules AxPA).inference ⋙
        (sliceEquivalence e ArithmeticIndexedFamily.formula).functor ≅
      (sliceEquivalence e ArithmeticIndexedFamily.formula).functor ⋙
        ((singleRules AxPA e).inference.prod (complementRules AxPA e).inference) :=
  NatIso.ofComponents
    (fun Q => Iso.prod ((numeralInferenceComparison AxPA e).app Q)
      ((complementInferenceComparison AxPA e).app Q))
    (by
      intro Q R f
      exact Prod.ext ((numeralInferenceComparison AxPA e).hom.naturality f)
        ((complementInferenceComparison AxPA e).hom.naturality f))

/-- The extensive equivalence on the stated inference algebras. It is
constructed, rather than an extra universal-property premise. -/
def algebraEquivalence :
    Endofunctor.Algebra (ArithmeticIndexedFamily.rules AxPA).inference ≌
      Endofunctor.Algebra (singleRules AxPA e).inference ×
        Endofunctor.Algebra (complementRules AxPA e).inference :=
  (AlgebraTransport.equivalence (sliceEquivalence e ArithmeticIndexedFamily.formula)
    (inferenceComparison AxPA e)).trans
      (ArithmeticIndexedAlgebraSplit.equivalence (singleRules AxPA e).inference
        (complementRules AxPA e).inference)

/-- The first transported algebra is on the actual pullback of the
full derivation conclusion, not a relabeled evaluator carrier. -/
def fiberAlgebra : Endofunctor.Algebra (singleRules AxPA e).inference :=
  ((algebraEquivalence AxPA e).functor.obj (ArithmeticIndexedFamily.algebra AxPA)).1

@[simp] theorem fiberAlgebra_carrier :
    (fiberAlgebra AxPA e).a =
      (Over.pullback (fiberMap e ArithmeticIndexedFamily.formula)).obj
        (ArithmeticIndexedFamily.algebra AxPA).a := rfl

/-- Proposition 7.5's formula-level fiber universal property. All algebra
morphisms are covered by the transported extensive equivalence. -/
def fiberInitial : IsInitial (fiberAlgebra AxPA e) :=
  ArithmeticIndexedAlgebraSplit.productInitialFirst _
    (IsInitial.isInitialObj (algebraEquivalence AxPA e).functor
      (ArithmeticIndexedFamily.algebra AxPA) (ArithmeticIndexedFamily.initial AxPA))

/-- The independent Γ_e derivation algebra has precisely the ordinary
nullary, Gen and ordered MP rules with the numeral-fiber axiom predicate. -/
def individualAlgebra : Endofunctor.Algebra (singleRules AxPA e).inference :=
  SyntacticDerivation.totalDerivationAlgebra 𝗣𝗔 (singleRules AxPA e)

def individualInitial : IsInitial (individualAlgebra AxPA e) :=
  SyntacticDerivation.totalDerivationInitial 𝗣𝗔 (singleRules AxPA e)

/-- Initiality supplies the unique constructor-preserving comparison. -/
def individualFiberAlgebraIso : individualAlgebra AxPA e ≅ fiberAlgebra AxPA e :=
  (individualInitial AxPA e).uniqueUpToIso (fiberInitial AxPA e)

def individualFiberIso : (individualAlgebra AxPA e).a.left ≅
    pullback (ArithmeticIndexedFamily.conclusion AxPA)
      (fiberMap e ArithmeticIndexedFamily.formula) :=
  (Over.forget ArithmeticIndexedFamily.formula).mapIso
    ((Endofunctor.Algebra.forget (singleRules AxPA e).inference).mapIso
      (individualFiberAlgebraIso AxPA e))

@[reassoc] theorem individualFiberIso_conclusion :
    (individualFiberIso AxPA e).hom ≫ pullback.snd
        (ArithmeticIndexedFamily.conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula) =
      (individualAlgebra AxPA e).a.hom :=
  Over.w (individualFiberAlgebraIso AxPA e).hom.f

def derivationMap : (individualAlgebra AxPA e).a.left ⟶
    (ArithmeticIndexedFamily.algebra AxPA).a.left :=
  (individualFiberIso AxPA e).hom ≫ pullback.fst
    (ArithmeticIndexedFamily.conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula)

/-- The full derivation-object fiber is the actual cartesian square
compatible with the conclusion and all rule constructors. -/
theorem derivation_pullback :
    IsPullback (derivationMap AxPA e) (individualAlgebra AxPA e).a.hom
      (ArithmeticIndexedFamily.conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula) := by
  apply IsPullback.of_iso_pullback ?_ (individualFiberIso AxPA e) rfl
    (individualFiberIso_conclusion AxPA e)
  constructor
  change ((individualFiberIso AxPA e).hom ≫ pullback.fst
      (ArithmeticIndexedFamily.conclusion AxPA) (fiberMap e ArithmeticIndexedFamily.formula)) ≫
      ArithmeticIndexedFamily.conclusion AxPA = _
  rw [Category.assoc,pullback.condition,← Category.assoc,individualFiberIso_conclusion]

def individualSentenceProof : TotalSplit 𝗣𝗔 :=
  pullback (individualAlgebra AxPA e).a.hom ArithmeticIndexedFamily.sentenceInclusion

def individualSentenceConclusion : individualSentenceProof AxPA e ⟶ ArithmeticIndexedFamily.sentence :=
  pullback.snd (individualAlgebra AxPA e).a.hom ArithmeticIndexedFamily.sentenceInclusion

theorem sentence_outer :
    IsPullback
      (pullback.fst (individualAlgebra AxPA e).a.hom ArithmeticIndexedFamily.sentenceInclusion ≫
        derivationMap AxPA e) (individualSentenceConclusion AxPA e)
      (ArithmeticIndexedFamily.conclusion AxPA)
      (fiberMap e ArithmeticIndexedFamily.sentence ≫
        prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion) := by
  have h := (IsPullback.of_hasPullback (individualAlgebra AxPA e).a.hom
    ArithmeticIndexedFamily.sentenceInclusion).paste_horiz (derivation_pullback AxPA e)
  have hn : ArithmeticIndexedFamily.sentenceInclusion ≫ fiberMap e ArithmeticIndexedFamily.formula =
      fiberMap e ArithmeticIndexedFamily.sentence ≫
        prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion :=
    (fiberMap_natural e ArithmeticIndexedFamily.sentenceInclusion).symm
  rw [← hn]
  exact h

def sentenceMap : individualSentenceProof AxPA e ⟶ ArithmeticIndexedFamily.sentenceProof AxPA :=
  pullback.lift
    (pullback.fst (individualAlgebra AxPA e).a.hom ArithmeticIndexedFamily.sentenceInclusion ≫
      derivationMap AxPA e)
    (individualSentenceConclusion AxPA e ≫ fiberMap e ArithmeticIndexedFamily.sentence)
    (by simpa only [Category.assoc] using (sentence_outer AxPA e).w)

/-- The printed square on sentence derivations is obtained by pullback
pasting, after the proved inference-algebra comparison. -/
theorem sentence_pullback :
    IsPullback (sentenceMap AxPA e) (individualSentenceConclusion AxPA e)
      (ArithmeticIndexedFamily.sentenceConclusion AxPA) (fiberMap e ArithmeticIndexedFamily.sentence) := by
  have ho : IsPullback
      (sentenceMap AxPA e ≫ pullback.fst (ArithmeticIndexedFamily.conclusion AxPA)
        (prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion))
      (individualSentenceConclusion AxPA e) (ArithmeticIndexedFamily.conclusion AxPA)
      (fiberMap e ArithmeticIndexedFamily.sentence ≫
        prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion) := by
    simpa only [sentenceMap,pullback.lift_fst] using sentence_outer AxPA e
  exact ho.of_right (by
    change sentenceMap AxPA e ≫ pullback.snd _ _ = _
    simp only [sentenceMap,pullback.lift_snd])
    (IsPullback.of_hasPullback (ArithmeticIndexedFamily.conclusion AxPA)
      (prod.map (𝟙 ArithmeticIndexedFamily.parameter) ArithmeticIndexedFamily.sentenceInclusion))

/-- Regular images commute with any proved pullback square. -/
theorem pullback_image {D : Type u} [Category.{v} D] [Regular D]
    {P X Y Z : D} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) :
    imageSubobject b = (Subobject.pullback g).obj (imageSubobject f) := by
  calc
    imageSubobject b = imageSubobject (h.isoPullback.hom ≫ pullback.snd f g) :=
      congrArg (fun k : P ⟶ Y => imageSubobject k) h.isoPullback_hom_snd.symm
    _ = imageSubobject (pullback.snd f g) := imageSubobject_iso_comp _ _
    _ = _ := sentenceImage_subobject f g

/-- The Γ_e sentence theorem subobject is the numeral pullback of the
single constructed indexed sentence-theory subobject. -/
theorem sentenceTheory_fiber :
    imageSubobject (individualSentenceConclusion AxPA e) =
      (Subobject.pullback (fiberMap e ArithmeticIndexedFamily.sentence)).obj
        (ArithmeticIndexedFamily.sentenceTheory AxPA) :=
  pullback_image (sentence_pullback AxPA e)

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
