/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTheorySentenceMorphisms


/-! # The ordered-field sentence morphisms -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
namespace CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceMorphisms.Checks

example (P : Uniform.Family) : numericalObject P ⟶
    (NamedProofImage.syntaxData P OrderedFieldSyntax.functionSymbols
      OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound).sentenceObject := theta P

example (P : Uniform.Family) (n : ℕ) :
    Total.underlying.map (theta P) (numericalPoint P n)=
      NamedProofImage.sentencePoint P OrderedFieldSyntax.functionSymbols
        OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound
        (OrderedFieldSyntax.thetaSentence n) (OrderedFieldSyntax.thetaSentence_closed n) :=
  theta_point P n

example (P : Uniform.Family) (n s : ℕ) :
    s ∈ Total.val (theta P).hom n ↔ OrderedFieldSyntax.theta n ∈
      Total.val (NamedProofImage.sentenceWord P OrderedFieldSyntax.functionSymbols
        OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound).hom s := theta_graph P n s

example (P : Uniform.Family) :
    (NamedProofImage.syntaxData P OrderedFieldSyntax.functionSymbols
      OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound).sentenceObject ⟶
    (NamedProofImage.syntaxData P OrderedFieldSyntax.functionSymbols
      OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound).sentenceObject := negation P

example (P : Uniform.Family) (φ : OrderedFieldSyntax.Formula) (hc : φ.freeVariables = []) :
    Total.underlying.map (negation P)
      (NamedProofImage.sentencePoint P OrderedFieldSyntax.functionSymbols
        OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound φ hc) =
      NamedProofImage.sentencePoint P OrderedFieldSyntax.functionSymbols
        OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound (.neg φ) hc :=
  negation_point P φ hc

example (P : Uniform.Family) (n : ℕ) :
    Total.underlying.map (theta P ≫ negation P) (numericalPoint P n) =
      NamedProofImage.sentencePoint P OrderedFieldSyntax.functionSymbols
        OrderedFieldSyntax.relationSymbols OrderedFieldSyntax.bound
        (.neg (OrderedFieldSyntax.thetaSentence n)) (OrderedFieldSyntax.thetaSentence_closed n) :=
  negation_theta_point P n

end CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceMorphisms.Checks
