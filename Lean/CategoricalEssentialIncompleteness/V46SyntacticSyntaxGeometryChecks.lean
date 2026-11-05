/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry

/-! # Signature checks for actual syntax geometry -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example (P : PredicateCategory T) (p : Obj T M P) :
    ∃! z : Obj T M (⊤_ (Over P)).left, (F T M).map (⊤_ (Over P)).hom z = p :=
  modelOverTerminal_existsUnique T M P p

example (P : PredicateCategory T) (A B : Over P) :
    Function.Injective ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left) ∧
      Function.Injective ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left) ∧
        IsCompl (Set.range ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left))
          (Set.range ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left)) :=
  modelOverSum_properties T M A B
