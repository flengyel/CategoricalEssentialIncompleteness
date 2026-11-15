/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedEssential

/-! # Independent predicate-presentation checks of Lemma 8.9 -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open LocalConnectedness SyntacticPredicates ArithmeticSignedAtoms

example : Inseparable (SplitObject.includedIdem ArithmeticDiagonalCodes.a0)
    (SplitObject.includedIdem ArithmeticDiagonalCodes.a1) :=
  ArithmeticDiagonalSplitting.source_pair_inseparable

example : SubobjectInseparable positiveSubobject negativeSubobject :=
  ArithmeticSignedEssential.diagonal_inseparable

variable {V : PredicateCategory 𝗣𝗔} (F : NullaryPresentations V)
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)

example : (F.presentation N).Consistent
    (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ∧
    ∀ U : (F.presentation N).Theories,
      (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ≤ U.val →
      (F.presentation N).Consistent U.val → ¬ (F.presentation N).Complete U.val :=
  ArithmeticSignedEssential.essentially_incomplete F

example (U : (F.presentation N).Theories)
    (hExt : (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (F.syntaxData N).sentenceNegation).obj U.val = ⊥) :
    U.val ⊔ (Subobject.pullback (F.syntaxData N).sentenceNegation).obj U.val ≠ ⊤ :=
  ArithmeticSignedEssential.every_consistent_extension_incomplete F U hExt hc

#print axioms ArithmeticDiagonalSplitting.alpha_idem
#print axioms ArithmeticDiagonalSplitting.beta_idem
#print axioms ArithmeticDiagonalSplitting.source_pair_inseparable
#print axioms ArithmeticSignedSeparator.partition_complement
#print axioms ArithmeticSignedSeparator.partition_computable
#print axioms ArithmeticSignedSeparator.no_separator
#print axioms ArithmeticSignedEssential.diagonal_disjoint
#print axioms ArithmeticSignedEssential.diagonal_inseparable
#print axioms ArithmeticSignedEssential.essentially_incomplete
#print axioms ArithmeticSignedEssential.every_consistent_extension_incomplete
