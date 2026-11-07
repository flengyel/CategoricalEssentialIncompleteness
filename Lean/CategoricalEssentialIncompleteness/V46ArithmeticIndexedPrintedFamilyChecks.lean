import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPrintedFamily
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPrintedFamily
example (AxPA : Carrier) :
    rules AxPA = ArithmeticIndexedRules.rules ArithmeticIndexedFamily.parameter
      ArithmeticIndexedFamily.logical ArithmeticIndexedFamily.sentenceInclusion
      (ArithmeticIndexedAxioms.Exponential.printedAxioms AxPA)
      ArithmeticIndexedFamily.generalization ArithmeticIndexedFamily.implication := rfl
example (AxPA : Carrier) : ArithmeticIndexedFibers.InferenceTransport.Data
    (CategoryTheory.Equivalence.refl (C := TotalSplit 𝗣𝗔)) (ArithmeticIndexedFamily.rules AxPA) (rules AxPA) :=
  coefficientData AxPA
example (AxPA : Carrier) : IsInitial (algebra AxPA) := initial AxPA
example (AxPA : Carrier) : algebra AxPA ≅ transportedRaw AxPA := algebraIso AxPA
example (AxPA : Carrier) : (carrierIso AxPA).hom ≫ ArithmeticIndexedFamily.conclusion AxPA =
    conclusion AxPA := carrierIso_conclusion AxPA
example (AxPA : Carrier) (e : ℕ) : IsInitial (fiberAlgebra AxPA e) := fiberInitial AxPA e
example (AxPA : Carrier) (e : ℕ) :
    (fiberAlgebra AxPA e).a = Over.mk (pullback.snd (conclusion AxPA)
      (ArithmeticIndexedFibers.fiberMap e ArithmeticIndexedFamily.formula)) := fiberAlgebra_carrier AxPA e
example (AxPA : Carrier) (e : ℕ) :
    ArithmeticIndexedFibers.individualAlgebra AxPA e ≅ fiberAlgebra AxPA e := individualFiberAlgebraIso AxPA e
example (AxPA : Carrier) : (sentenceIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA =
    sentenceConclusion AxPA := sentenceIso_conclusion AxPA
example (AxPA : Carrier) :
    (realization 𝗣𝗔).map (ArithmeticIndexedProvability.printedConclusion AxPA) =
      (proofPresentationIso AxPA).hom ≫ sentenceConclusion AxPA ≫
        ArithmeticIndexedProvability.printedProductIso.inv := printedConclusion_realization AxPA
example (AxPA : Carrier) (e : ℕ) :
    IsPullback (sentenceMap AxPA e) (ArithmeticIndexedFibers.individualSentenceConclusion AxPA e)
      (sentenceConclusion AxPA) (ArithmeticIndexedFibers.fiberMap e ArithmeticIndexedFamily.sentence) :=
  sentence_pullback AxPA e
example (AxPA : Carrier) (e : ℕ) :
    imageSubobject (ArithmeticIndexedFibers.individualSentenceConclusion AxPA e) =
      (Subobject.pullback (ArithmeticIndexedFibers.fiberMap e ArithmeticIndexedFamily.sentence)).obj
        (imageSubobject (sentenceConclusion AxPA)) := sentenceTheory_fiber AxPA e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPrintedFamily
