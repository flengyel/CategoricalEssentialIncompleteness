import CategoricalEssentialIncompleteness.V46SyntacticPredicates

/-! Explicit predicate-presentation types for Lemma 5.3. -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.ProofSearch FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PredicateCategory T ≌
      WideSubcategory (isTotal (C := SplitObject (CodedProgramCategory T))) :=
  predicateEquivalence T

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (C D : Carrier) (F : Graph)
    (hs : T ⊢ supportSentence C D F) (ht : T ⊢ totalSentence C F) :
    interpretedObject T C ⟶ interpretedObject T D :=
  (GraphMorphism.mk F hs ht).toTotal

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : (realization T).Full := inferInstance

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : (realization T).Faithful := inferInstance

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : (realization T).EssSurj := inferInstance

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (C D : Carrier)
    (f g : GraphMorphism T C D) :
    classOfGraph T f = classOfGraph T g ↔ T ⊢ uniformSentence f.graph g.graph :=
  classOfGraph_eq_iff T f g
