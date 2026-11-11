/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationRules


/-! # Statement checks in `V46NumericalDerivationInterpretationRulesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example (n : ℕ) : K.obj (finitePower F n) ≅ finitePower (K.obj F) n := finitePowerIso F n
example (i : Fin (N+1)) : (interpretedRules R).instances i = K.obj (R.instances i) := rfl
example (i : Fin (N+1)) : (interpretedRules R).premises i =
    K.map (R.premises i) ≫ (finitePowerIso F i.val).hom := rfl
example (i : Fin (N+1)) : (interpretedRules R).conclusion i = K.map (R.conclusion i) := rfl
example (Q : Over F) (i : Fin (N+1)) :
    K.obj (R.ruleObject Q i) ≅ (interpretedRules R).ruleObject ((overFunctor R).obj Q) i := inputIso R Q i
example (Q : Over F) (i : Fin (N+1)) : (inputIso R Q i).hom ≫ pullback.fst _ _ =
    K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) := inputIso_fst R Q i
example (Q : Over F) (i : Fin (N+1)) : (inputIso R Q i).hom ≫ pullback.snd _ _ =
    K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
      (finitePowerIso Q.left i.val).hom := inputIso_snd R Q i
example (i : Fin (N+1)) (n : ℕ) :
    (NumericalSyntaxTreeChart.E.inverse.obj
      (SyntacticDerivation.PolynomialComparison.coefficients (interpretedRules R) i.val)).val.Evalb
        (M := ℕ) ![n] ↔ (R.instances i).val.Evalb (M := ℕ) ![n] := interpreted_rule_labels R i n
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
