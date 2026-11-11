/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptions
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorValues

/-! # Actual successful constructor values after parameterization -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem parameterOperation_some_code (P X Y Z : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (f : a.eval.obj (X,Y) ⟶ Z) (φ : M → M)
    (hf : ∀ (u : M) (z : Obj T M (a.eval.obj (X,Y))),
      (baseRepresentation T X Y a).val.Evalb ![u,z.val] → ((F T M).map f z).val = φ u)
    (p : Obj T M P) (u : M)
    (q : Obj T M ((a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left)
    (hq : (constantRepresentation T P X Y a).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Z ((F T M).map (prod.snd : P ⨯ OptionSyntax.obj Z ⟶ _)
      ((F T M).map (SyntaxPolynomial.parameterComparison P (X,Y) a ≫
        (constantFamilyFunctor P).map (f ≫ coprod.inr)).left q)) = Arithmetic.pair (φ u) 1 := by
  let z := (F T M).map (parameterValueMap T P X Y a) q
  have hz := parameterValueMap_representation T M P X Y a p u q hq
  have hp := parameterOperation_value T M P X Y (OptionSyntax.obj Z) a (f ≫ coprod.inr) q
  have hs : (F T M).map (f ≫ coprod.inr) z =
      (F T M).map (coprod.inr : Z ⟶ OptionSyntax.obj Z) ((F T M).map f z) := by
    rw [Functor.map_comp_apply]
  exact (congrArg (optionCode T M Z) (hp.trans hs)).trans
    ((optionCode_inr T M Z ((F T M).map f z)).trans
      (congrArg (fun v => Arithmetic.pair v 1) (hf u z hz)))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
