/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticAssociatedIncompleteness

/-! # Independent checks of the logical clauses of Corollary 8.10 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46 SyntacticPredicates
open ArithmeticAssociatedDeduction ArithmeticAssociatedIncompleteness
local notation "F₀" => ArithmeticSignedTheory.presentation
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
local notation "S" => NullaryPresentations.syntaxData (F₀) N
local notation "G" => SyntacticPredicates.realization 𝗣𝗔
local instance (P : TotalSplit 𝗣𝗔) : Regular (Over P) := RegularSlices.regular P
local instance (P : TotalSplit 𝗣𝗔) : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance (P : TotalSplit 𝗣𝗔) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

example (P : TotalSplit 𝗣𝗔)
    (A : Subobject ((constantFamilyFunctor P).obj ((G).obj (S).sentenceObject))) :
    IsInitial (proofs P A) := initial P A

example : IsTerminal pointDomain := pointDomain_terminal

example (U : GlobalTheory) :
    ∃ p : pointDomain ⟶ (U.val : TotalSplit 𝗣𝗔), p ≫ U.val.arrow = theoremPoint := point_factors U

/-- The actual theorem family is the image of 1_U times the original
subobject arrow; its closure is constructed by the parameterized proof family. -/
example (U : GlobalTheory) : (constantTheory U).val =
    Subobject.mk ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map U.val.arrow) :=
  constantTheory_value U

/-- No slice extension is required to be a constant family. -/
example (U : GlobalTheory)
    (hExt : (ArithmeticSignedTotal.theory (F₀)).val ≤ U.val)
    (hcU : U.val ⊓ (Subobject.pullback (ArithmeticSignedTotal.negation (F₀))).obj U.val = ⊥) :
    ((constantTheory U).val ⊓ (Subobject.pullback
      ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map
        (ArithmeticSignedTotal.negation (F₀)))).obj (constantTheory U).val = ⊥) ∧
    ∀ W : FirstOrderReflection.Theory (proofs (U.val : TotalSplit 𝗣𝗔)),
      (constantTheory U).val ≤ W.val →
      W.val ⊓ (Subobject.pullback ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map
        (ArithmeticSignedTotal.negation (F₀)))).obj W.val = ⊥ →
      W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map
        (ArithmeticSignedTotal.negation (F₀)))).obj W.val ≠ ⊤ :=
  essentially_incomplete U hExt hcU

example (U : GlobalTheory)
    (hExt : (ArithmeticSignedTotal.theory (F₀)).val ≤ U.val)
    (hcU : U.val ⊓ (Subobject.pullback (ArithmeticSignedTotal.negation (F₀))).obj U.val = ⊥) :
    SubobjectInseparable U.val ((Subobject.pullback (ArithmeticSignedTotal.negation (F₀))).obj U.val) :=
  extension_inseparable U hExt hcU

#print axioms NullaryLogicalPoint.formula_closed
#print axioms NullaryLogicalPoint.logicalInstance_formula
#print axioms NullaryLogicalPoint.factors
#print axioms ArithmeticAssociatedDeduction.proofs
#print axioms ArithmeticAssociatedDeduction.initial
#print axioms ArithmeticAssociatedDeduction.pointDomain_terminal
#print axioms ArithmeticAssociatedDeduction.logicalPoint_diagram
#print axioms ArithmeticAssociatedDeduction.point_factors
#print axioms ArithmeticAssociatedIncompleteness.constantTheory
#print axioms ArithmeticAssociatedIncompleteness.evaluatedTheory
#print axioms ArithmeticAssociatedIncompleteness.every_consistent_extension_incomplete
#print axioms ArithmeticAssociatedIncompleteness.essentially_incomplete
#print axioms ArithmeticAssociatedIncompleteness.extension_inseparable
