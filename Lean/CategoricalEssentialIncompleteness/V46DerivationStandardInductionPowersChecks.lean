/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionPowers


/-! # Statement checks in `V46DerivationStandardInductionPowersChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.DerivationStandardInductionPowersChecks
open SyntacticSyntax SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
example {X Y : PredicateCategory T} (f : X ⟶ Y) (n : ℕ) (i : Fin n) :
    finitePowerMap f n ≫ finiteChild T Y n i = finiteChild T X n i ≫ f :=
  finiteChild_natural T f n i
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (X Y : PredicateCategory T) (n : ℕ) (bound u : M)
    (z : Obj T M ((SyntaxPolynomial.power .term n).eval.obj (X,Y)))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.power .term n)).val.Evalb ![u,z.val])
    (hs : Coding.ChildSize (SyntaxPolynomial.power .term n) bound u) :
    ∀ i : Fin n, len ((F T M).map (powerProjection T X Y n i) z).val < bound :=
  power_children_smaller T M X Y n bound u z hz hs
end CategoricalEssentialIncompleteness.V46.DerivationStandardInductionPowersChecks
