/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvability


/-! # A uniform provability formula from the constructed family conclusion -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (AxPA : Carrier) (e z : M) :
    (provability AxPA).val.Evalb ![e,z] ↔
      ∃ p : Obj 𝗣𝗔 M (proofCarrier AxPA),
        ((F 𝗣𝗔 M).map (rawConclusion AxPA) p).val = ⟪e,z⟫ :=
  provability_eval M AxPA e z
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
