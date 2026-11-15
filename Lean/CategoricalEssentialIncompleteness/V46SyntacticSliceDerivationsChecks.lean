/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SyntacticSliceDerivations

/-! # Independent checks of arbitrary parameterized deduction initiality -/
@[expose] public section
noncomputable section
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46 SyntacticPredicates

section General
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D] {P : D}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N) (Q : Over F)

example (i : Fin (N + 1)) : (SliceRuleObjects.rules R).instances i = (R.instances i).left := rfl
example (i : Fin (N + 1)) : (SliceRuleObjects.rules R).premises i =
    (R.premises i).left ≫ SliceFinitePowers.comparison F i.val := rfl
example (i : Fin (N + 1)) : (SliceRuleObjects.rules R).conclusion i = (R.conclusion i).left := rfl

example (i : Fin (N + 1)) :
    (SliceRuleObjects.iso R Q i).hom ≫ (SliceRuleObjects.rules R).ruleConclusion
      ((Over.iteratedSliceEquiv F).functor.obj Q) i = (R.ruleConclusion Q i).left :=
  SliceRuleObjects.iso_conclusion R Q i

example : Endofunctor.Algebra R.inference ≌
    Endofunctor.Algebra (SliceRuleObjects.rules R).inference := SliceInference.algebraEquivalence R
end General

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {P : TotalSplit T}
local instance : Regular (Over P) := RegularSlices.regular P
variable {F : Over P} {N : ℕ} (R : RulePresentation F N)

/-- P, every rule coefficient family and every algebra morphism are arbitrary. -/
example : IsInitial (SyntacticSliceDerivations.algebra T R) :=
  SyntacticSliceDerivations.initial T R

example (B : Endofunctor.Algebra R.inference) :
    ∃! _f : SyntacticSliceDerivations.algebra T R ⟶ B, True := by
  refine ⟨SyntacticSliceDerivations.fold T R B, trivial, ?_⟩
  intro f _
  exact SyntacticSliceDerivations.fold_unique T R B f

#print axioms SliceRuleObjects.forward_backward
#print axioms SliceRuleObjects.backward_forward
#print axioms SliceRuleObjects.iso
#print axioms SliceRuleObjects.iso_fst
#print axioms SliceRuleObjects.iso_snd
#print axioms SliceRuleObjects.iso_conclusion
#print axioms SliceRuleObjects.naturality
#print axioms SliceInference.comparison
#print axioms SliceInference.algebraEquivalence
#print axioms SliceInference.initial
#print axioms SyntacticSliceDerivations.algebra
#print axioms SyntacticSliceDerivations.initial
#print axioms SyntacticSliceDerivations.fold_unique
