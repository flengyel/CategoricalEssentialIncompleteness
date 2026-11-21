/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalRuleRebase


/-! # Changing formula coordinates in numerical derivation algebras -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {F G : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N) (e : F ≅ G)

example (i : Fin (N + 1)) : (NumericalRuleRebase.rules R e).instances i = R.instances i := rfl

example (i : Fin (N + 1)) : (NumericalRuleRebase.rules R e).premises i =
    R.premises i ≫ finitePowerMap e.hom i.val := rfl

example (Q : Over F) (i : Fin (N + 1)) :
    (NumericalRuleRebase.inputIso R e Q i).hom ≫
      pullback.snd ((NumericalRuleRebase.rules R e).premises i)
        (finitePowerMap ((NumericalRuleRebase.slice e).functor.obj Q).hom i.val) =
      pullback.snd (R.premises i) (finitePowerMap Q.hom i.val) :=
  NumericalRuleRebase.input_snd R e Q i

example : NumericalDerivation.codeObject R ≅
    NumericalDerivation.codeObject (NumericalRuleRebase.rules R e) :=
  NumericalRuleRebase.codeIso R e

example : (NumericalRuleRebase.codeIso R e).hom ≫
    NumericalDerivation.codeConclusion (NumericalRuleRebase.rules R e) =
      NumericalDerivation.codeConclusion R ≫ e.hom :=
  NumericalRuleRebase.conclusion R e

example : (NumericalRuleRebase.codeIso R e).inv ≫
    (NumericalDerivation.codeConclusion R ≫ e.hom) =
      NumericalDerivation.codeConclusion (NumericalRuleRebase.rules R e) :=
  NumericalRuleRebase.inverse_conclusion R e
