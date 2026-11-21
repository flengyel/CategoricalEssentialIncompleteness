/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTheorySentenceWords


/-! # The chosen sentence object and its literal-word carrier -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWords
open OrderedFieldSyntax
variable (P : Uniform.Family)
local notation "S" => NamedProofImage.syntaxData P functionSymbols relationSymbols bound
local notation "U" => (Total.underlying (P := P))

example : (S).sentenceObject ≅ (Syntax.predicateFunctor P).obj
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 NamedPostfixEncoding.variableCarrier
      functionSymbols relationSymbols 2) := sentenceIso P

example (word : ℕ) : word∈Total.Subobjects.imageCodes
    (NamedProofImage.sentenceWord P functionSymbols relationSymbols bound) ↔
    OrderedFieldSyntax.sentencePredicate.val.Evalb ![word] :=
  Set.ext_iff.mp (sentenceWord_image P) word

example (s word : ℕ) : word∈Total.val (sentenceIso P).hom.hom s ↔
    word∈Total.val (NamedProofImage.sentenceWord P functionSymbols relationSymbols bound).hom s :=
  toLiteral_graph P s word

example (word s : ℕ) : s∈Total.val (sentenceIso P).inv.hom word ↔
    word∈Total.val (NamedProofImage.sentenceWord P functionSymbols relationSymbols bound).hom s :=
  fromLiteral_graph P word s

example : (S).sentenceNegation ≫ (sentenceIso P).hom=
    (sentenceIso P).hom ≫ literalNegation P := negation_square P

example (n : ℕ) :
    ((U).map (TheorySentenceMorphisms.theta P ≫ (sentenceIso P).hom)
      (TheorySentenceMorphisms.numericalPoint P n)).val=
      formulaCode (lt (mul (natural 2) (c n)) one) := theta_word_value P n

example (s : (U).obj (S).sentenceObject) :
    ((U).map ((S).sentenceNegation ≫ (sentenceIso P).hom) s).val=
      negationWord (((U).map (sentenceIso P).hom s).val) := negation_word_value P s

end CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWords
