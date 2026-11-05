/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCandidateValues

/-! # Explicit signature checks for CandidateValues -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example {P C : PredicateCategory T} {X : Over P}
    (f : constantFamily P C ⟶ X) (p : Obj T M P) (u v : M)
    (z : Obj T M (P ⨯ C))
    (hz : (constantLeaf T P C).val.Evalb ![p.val,u,z.val]) :
    (rawArrow T f).val.Evalb ![p.val,u,v] ↔ v = ((F T M).map f.left z).val :=
  rawArrow_value_iff T M f p u v z hz
