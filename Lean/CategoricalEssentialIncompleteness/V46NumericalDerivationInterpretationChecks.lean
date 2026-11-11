/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretation


/-! # Statement checks in `V46NumericalDerivationInterpretationChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example : NumericalDerivation.codeAlgebra (interpretedRules R) ≅
    mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R) := interpretationAlgebraIso R
example : NumericalDerivation.codeObject (interpretedRules R) ≅
    K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left := interpretationCodeIso R
example : (interpretationCodeIso R).hom ≫ K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom =
    NumericalDerivation.codeConclusion (interpretedRules R) := interpretationCodeIso_conclusion R
example : (interpretationCodeIso R).inv ≫ NumericalDerivation.codeConclusion (interpretedRules R) =
    K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom := interpretationCodeIso_inverse_conclusion R
example : (interpretedRules R).inference.map (interpretationOverIso R).hom ≫
      (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)).str =
    (NumericalDerivation.codeAlgebra (interpretedRules R)).str ≫ (interpretationOverIso R).hom :=
  interpretationCodeIso_constructor R
example : IsInitial (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)) := mappedDerivationInitial R
example (B : Endofunctor.Algebra (interpretedRules R).inference) :
    (interpretedDerivationFold R B).f.left ≫ B.a.hom =
      K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom := interpretedDerivationFold_conclusion R B
example (B : Endofunctor.Algebra (interpretedRules R).inference) :
    (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)).str ≫
      (interpretedDerivationFold R B).f =
    (interpretedRules R).inference.map (interpretedDerivationFold R B).f ≫ B.str := interpretedDerivationFold_constructor R B
example (B : Endofunctor.Algebra (interpretedRules R).inference)
    (f : mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R) ⟶ B) :
    f = interpretedDerivationFold R B := interpretedDerivationFold_unique R B f
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
