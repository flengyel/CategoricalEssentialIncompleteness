/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedContradiction
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Independent checks of truth for diagonal signed derivations -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists ArithmeticSignedTheoryTruth

section ConstructedSyntax
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
local notation "S" => SyntacticSyntax.plainCategoricalSyntax 𝗣𝗔 N
  (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0
local notation "Q" => SyntacticDerivation.derivationAlgebra 𝗣𝗔 (rules S)
local notation "P" => listObject 𝗣𝗔 N
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The syntax, signed rules, valuation and support are all constructed.
No truth, consistency or syntax-existence premise is supplied. -/
example (l : Obj 𝗣𝗔 M P)
    (hl : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb ![l.val])
    (d : Obj 𝗣𝗔 M (Q).a.left)
    (hc : ∀ i < len ((F 𝗣𝗔 M).map (support S) d).val,
      MemVec (nth ((F 𝗣𝗔 M).map (support S) d).val i) l.val)
    (z : Obj 𝗣𝗔 M (P ⨯ (S).algebra.a.2))
    (hp : (F 𝗣𝗔 M).map (prod.fst : P ⨯ (S).algebra.a.2 ⟶ P) z = l)
    (hf : (F 𝗣𝗔 M).map (prod.snd : P ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2) z =
      (F 𝗣𝗔 M).map (Q).a.hom d) :
    (F 𝗣𝗔 M).map (SignedFiniteFormulaValuation.valuation 𝗣𝗔 S) z =
      (F 𝗣𝗔 M).map (Two.constant (P ⨯ (S).algebra.a.2) true) z :=
  internal_truth S M l hl d hc z hp hf

example (p q : Obj 𝗣𝗔 M (Q).a.left) :
    ¬ ((F 𝗣𝗔 M).map (Q).a.hom q =
      (F 𝗣𝗔 M).map (S).negationConstructor ((F 𝗣𝗔 M).map (Q).a.hom p)) :=
  no_contradictory_derivations S M p q

example (p q : Obj 𝗣𝗔 M (Q).a.left) :
    (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb
      ![SyntacticSyntax.Words.append ((F 𝗣𝗔 M).map (support S) p).val
        ((F 𝗣𝗔 M).map (support S) q).val] := jointSupport_alpha S M p q
end ConstructedSyntax

#print axioms ArithmeticSignedAtoms.numberInclusion
#print axioms ArithmeticSignedAtoms.numberInclusion_value
#print axioms ArithmeticSignedAtoms.positive_true
#print axioms ArithmeticSignedAtoms.negative_true
#print axioms ArithmeticSignedTheoryTruth.axioms
#print axioms ArithmeticSignedTheoryTruth.rules
#print axioms ArithmeticSignedTheoryTruth.support
#print axioms ArithmeticSignedTheoryTruth.singleton_value
#print axioms ArithmeticSignedTheoryTruth.leaf_truth
#print axioms ArithmeticSignedTheoryTruth.internal_truth
#print axioms ArithmeticSignedTheoryTruth.jointSupport
#print axioms ArithmeticSignedTheoryTruth.jointSupport_alpha
#print axioms ArithmeticSignedTheoryTruth.joint_left_truth
#print axioms ArithmeticSignedTheoryTruth.joint_right_truth
#print axioms ArithmeticSignedTheoryTruth.trueAt_not_negation
#print axioms ArithmeticSignedTheoryTruth.no_contradictory_derivations
