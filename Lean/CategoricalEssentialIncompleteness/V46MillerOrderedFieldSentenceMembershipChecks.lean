/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOrderedFieldSentenceMembership


/-! # Primitive-recursive membership in the ordered-field sentence words -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSentenceMembership
open OrderedFieldSyntax

example : PrimrecPred (fun word : ℕ =>
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔
      NamedPostfixEncoding.variableCarrier functionSymbols relationSymbols 2).val.Evalb ![word]) :=
  sentence_membership_primrec

example : ∃ dec : ℕ → Bool,Computable dec ∧ ∀ word,dec word=true ↔
    sentencePredicate.val.Evalb ![word] := sentence_membership_computable

end CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSentenceMembership
