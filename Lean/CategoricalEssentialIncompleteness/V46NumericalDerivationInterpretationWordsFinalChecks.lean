/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationWordsFinal


/-! # Literal word identity of the constructed PA derivation comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordsFinal
open SyntacticDerivation
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example : mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R) ≅
    NumericalDerivation.literalOrdinaryTree (interpretedRules R) := ordinaryWordIso R
example : (sourceOrdinaryIso R).hom.f ≫
    (NumericalDerivation.ordinaryWordAlgebraIso (interpretedRules R)).hom.f =
    (ordinaryWordIso R).hom.f := ordinaryWordIso_unique R
example : (interpretationCodeIso R).hom ≫ sourceProofWord R =
    NumericalDerivation.codeWordInclusion (interpretedRules R) := word_square R
example (x : NumericalTuples.Point (NumericalDerivation.codeObject (interpretedRules R))) :
    NumericalTuples.code (K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left).dimension
      ((interpretationCodeIso R).hom.toFun x).val =
    NumericalTuples.code (NumericalDerivation.codeObject (interpretedRules R)).dimension x.val :=
  interpretationCodeIso_word_coded R x
example (x : NumericalTuples.Point (K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left)) :
    NumericalTuples.code (NumericalDerivation.codeObject (interpretedRules R)).dimension
      ((interpretationCodeIso R).inv.toFun x).val =
    NumericalTuples.code (K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left).dimension x.val :=
  interpretationCodeIso_inverse_word_coded R x
example : (NumericalDerivation.codeObject (interpretedRules R)).dimension = 1 := rfl
example : (K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left).dimension = 1 := rfl
example (n : ℕ) : NumericalTuples.code 1 n = n := rfl
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordsFinal
