/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationFunctor
public import CategoricalEssentialIncompleteness.V46NumericalUnderlying
public import Mathlib.CategoryTheory.Limits.Types.Products

/-! # Uniqueness of numerical validation from its exact successful pullback

Two total option-valued maps with the same successful subobject and the
same successful conclusion agree. Their failure values also agree because
the failure coefficient is terminal. No evaluation or initiality premise
is part of this uniqueness theorem.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation

/-- This applies to arbitrary numerical carriers, including empty ones. -/
theorem validator_unique {X W F : NumericalTuples.Object}
    (m : W ⟶ X) (h : W ⟶ F) (f g : X ⟶ OptionSyntax.obj F)
    (hf : IsPullback m h f (coprod.inr : F ⟶ OptionSyntax.obj F))
    (hg : IsPullback m h g (coprod.inr : F ⟶ OptionSyntax.obj F)) : f = g := by
  let U := NumericalUnderlying.functor
  let _ : Unique (U.obj (⊤_ NumericalTuples.Object)) :=
    Types.isTerminalEquivUnique _ (terminalIsTerminal.isTerminalObj U _)
  apply NumericalTuples.Map.ext
  funext x
  have hf' := hf.map U
  have hg' := hg.map U
  rcases OptionModels.sum_cases U (⊤_ NumericalTuples.Object) F (f.toFun x) with
      ⟨a, ha⟩ | ⟨b, hb⟩
  · rcases OptionModels.sum_cases U (⊤_ NumericalTuples.Object) F (g.toFun x) with
        ⟨c, hc⟩ | ⟨d, hd⟩
    · exact ha.symm.trans ((congrArg (U.map (coprod.inl : ⊤_ NumericalTuples.Object ⟶
          OptionSyntax.obj F)) (Subsingleton.elim a c)).trans hc)
    · obtain ⟨w, hw, _⟩ := Types.exists_of_isPullback hg' x d hd.symm
      have he := congrArg (fun k => k.toFun w) hf.w
      change f.toFun (m.toFun w) = (coprod.inr : F ⟶ OptionSyntax.obj F).toFun (h.toFun w) at he
      change m.toFun w = x at hw
      rw [hw] at he
      exact False.elim ((OptionModels.sum_disjoint U (⊤_ NumericalTuples.Object) F a
        (h.toFun w)) (ha.trans he))
  · obtain ⟨w, hw, _⟩ := Types.exists_of_isPullback hf' x b hb.symm
    have he := congrArg (fun k => k.toFun w) hf.w
    have he' := congrArg (fun k => k.toFun w) hg.w
    change f.toFun (m.toFun w) = (coprod.inr : F ⟶ OptionSyntax.obj F).toFun (h.toFun w) at he
    change g.toFun (m.toFun w) = (coprod.inr : F ⟶ OptionSyntax.obj F).toFun (h.toFun w) at he'
    change m.toFun w = x at hw
    rw [hw] at he he'
    exact he.trans he'.symm

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
