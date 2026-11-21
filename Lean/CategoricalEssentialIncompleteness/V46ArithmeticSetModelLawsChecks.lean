/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSetModelLaws


/-! # Set and total-function laws before arithmetic specialization -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSetModelLaws.Checks
example {A B : Pfn} (f : A ⟶ B) (hf : isTotal f) (a : A) :
    totalValue f hf a ∈ f a := totalValue_mem f hf a
example {A B : Pfn} (f : A ⟶ B) (R : B → Prop)
    (h : Idem.pull f (setIdem {b : B | R b}) = ⊥) (a : A) (b : B)
    (hb : b ∈ f a) : ¬ R b := pull_zero_not_mem f R h a b hb
end CategoricalEssentialIncompleteness.V46.ArithmeticSetModelLaws.Checks
