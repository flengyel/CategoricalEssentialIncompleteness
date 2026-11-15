/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationFiniteSupport

/-! # Independent checks on canonical signed positive supports -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SignedDerivation

section Lookup
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (n labels : M) :
    ConcreteNamedSubstitution.member n labels = ArithmeticFiniteLookup.lookup n labels :=
  member_eq_lookup n labels

example (out n labels : M) :
    ConcreteNamedSubstitution.memberGraph.val.Evalb ![out, labels, n] ↔
      ArithmeticFiniteLookup.graph.val.Evalb ![out, n, labels] :=
  membership_graph_comparison out n labels

example : 𝗣𝗔 ⊢ membershipComparisonSentence := membership_comparison_PA
end Lookup

section CanonicalAlgebra
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {L A B V S F : PredicateCategory T}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⨿ B ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

example : (SyntacticDerivation.derivationAlgebra T
      (firstOrderRules logical sentence axioms all imp)).a.left ⟶
    (SyntacticLists.stableListAlgebra T A).algebra.carrier :=
  positiveSupport T logical sentence axioms all imp

example :
    (coprod.inl ≫ coprod.inr ≫ SyntacticDerivation.nullaryDerivation T
        (firstOrderRules logical sentence axioms all imp)) ≫
      positiveSupport T logical sentence axioms all imp =
        (SyntacticLists.stableListAlgebra T A).singleton :=
  canonical_positive_collect T logical sentence axioms all imp

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (p : SyntacticLists.Obj T M (SyntacticDerivation.derivationAlgebra T
      (firstOrderRules logical sentence axioms all imp)).a.left) :
    (FiniteSigmaOne.allEntriesCondition A).Evalb
      ![((PredicateInterpretation.functor T M).map
        (positiveSupport T logical sentence axioms all imp) p).val] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact canonical_support T logical sentence axioms all imp p

end CanonicalAlgebra

section ArithmeticPair
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {L V S F : PredicateCategory 𝗣𝗔}
variable (logical : L ⟶ F) (sentence : S ⟶ F)
variable (axioms : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
  (Limits.coprod (C := PredicateCategory 𝗣𝗔) ArithmeticDiagonalCodes.alpha
    ArithmeticDiagonalCodes.beta) S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

example (p q : SyntacticLists.Obj 𝗣𝗔 M (SyntacticDerivation.derivationAlgebra 𝗣𝗔
      (firstOrderRules logical sentence axioms all imp)).a.left)
    (n : M) (hn : ArithmeticDiagonalCodes.beta.val.Evalb ![n]) :
    ArithmeticFiniteLookup.graph.val.Evalb ![0, n, SyntacticSyntax.Words.append
      ((PredicateInterpretation.functor 𝗣𝗔 M).map
        (positiveSupport 𝗣𝗔 logical sentence axioms all imp) p).val
      ((PredicateInterpretation.functor 𝗣𝗔 M).map
        (positiveSupport 𝗣𝗔 logical sentence axioms all imp) q).val] :=
  canonical_negative_lookup 𝗣𝗔 logical sentence axioms all imp
    (fun x ha hb => ArithmeticDiagonalCodes.output_disjoint x ⟨ha, hb⟩) p q n hn

end ArithmeticPair

#print axioms SignedDerivation.member_eq_lookup
#print axioms SignedDerivation.membership_graph_comparison
#print axioms SignedDerivation.membership_comparison_PA
#print axioms SignedDerivation.positiveLeafAssignment
#print axioms SignedDerivation.positiveSupport
#print axioms SignedDerivation.canonical_nullary_collect
#print axioms SignedDerivation.canonical_logical_collect
#print axioms SignedDerivation.canonical_positive_collect
#print axioms SignedDerivation.canonical_negative_collect
#print axioms SignedDerivation.canonical_unary_collect
#print axioms SignedDerivation.canonical_binary_collect
#print axioms SignedDerivation.canonical_support
#print axioms SignedDerivation.canonical_negative_lookup
