/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticAssociatedDeduction
public import CategoricalEssentialIncompleteness.V46AssociatedClosedTheories
public import CategoricalEssentialIncompleteness.V46AssociatedExtensionWitness

/-! # Arithmetic incompleteness for arbitrary closed associated-slice extensions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedIncompleteness
open ArithmeticAssociatedDeduction
local notation "F₀" => ArithmeticSignedTheory.presentation
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
local notation "S" => NullaryPresentations.syntaxData (F₀) N
local notation "G" => SyntacticPredicates.realization 𝗣𝗔

abbrev GlobalTheory := FirstOrderReflection.Theory (ArithmeticSignedTotal.proofs (F₀))

local instance (P : TotalSplit 𝗣𝗔) : Regular (Over P) := RegularSlices.regular P
local instance (P : TotalSplit 𝗣𝗔) : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance (P : TotalSplit 𝗣𝗔) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance {Z U : TotalSplit 𝗣𝗔} (p : Z ⟶ U) (h : IsTerminal Z) :
    PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation p h) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits p h

variable (U : GlobalTheory)

def point : pointDomain ⟶ (U.val : TotalSplit 𝗣𝗔) := (point_factors U).choose

theorem point_over : point U ≫ U.val.arrow = theoremPoint := (point_factors U).choose_spec

/-- This is the actual constant theorem family, with its closure proved
from the constructed parameterized deduction algebras. -/
def constantTheory : FirstOrderReflection.Theory (proofs (U.val : TotalSplit 𝗣𝗔)) :=
  (SliceClosedTheories.constantTheoryFunctor (U.val : TotalSplit 𝗣𝗔)
    (ArithmeticSignedTotal.proofs (F₀)) (ArithmeticSignedTotal.initial (F₀))
    (proofs (U.val : TotalSplit 𝗣𝗔)) (initial (U.val : TotalSplit 𝗣𝗔))).obj U

theorem constantTheory_value : (constantTheory U).val =
    FiniteLimitSubobjects.object (constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)) U.val := rfl

def evaluatedTheory (W : FirstOrderReflection.Theory (proofs (U.val : TotalSplit 𝗣𝗔))) :
    GlobalTheory := by
  let A := SliceSubobjectPredicates.evaluate (point U) pointDomain_terminal W.val
  refine ⟨A, ?_⟩
  have h := RetractedClosedTheories.closed_back (constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔))
    (SliceBaseChangeGeometry.evaluation (point U) pointDomain_terminal)
    (SliceBaseChangeGeometry.ordinaryRetraction (point U) pointDomain_terminal)
    (ArithmeticSignedTotal.proofs (F₀)) (ArithmeticSignedTotal.initial (F₀))
    (proofs (U.val : TotalSplit 𝗣𝗔)) (initial (U.val : TotalSplit 𝗣𝗔)) W.val W.property
  have he := SliceSubobjectPredicates.evaluate_eq_retraction (point U) pointDomain_terminal W.val
  change FirstOrderReflection.generated (ArithmeticSignedTotal.proofs (F₀)) A = A
  dsimp only [A]
  rw [he]
  exact h

/-- Evaluation covers arbitrary closed slice extensions, without requiring
that they be constant families or images of a selected theory. -/
theorem every_consistent_extension_incomplete
    (hExt : (ArithmeticSignedTotal.theory (F₀)).val ≤ U.val)
    (W : FirstOrderReflection.Theory (proofs (U.val : TotalSplit 𝗣𝗔)))
    (hW : (constantTheory U).val ≤ W.val)
    (hcW : W.val ⊓ (Subobject.pullback
      ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map
        (ArithmeticSignedTotal.negation (F₀)))).obj W.val = ⊥) :
    W.val ⊔ (Subobject.pullback
      ((constantFamilyFunctor (U.val : TotalSplit 𝗣𝗔)).map
        (ArithmeticSignedTotal.negation (F₀)))).obj W.val ≠ ⊤ := by
  intro hcomp
  let W₀ := evaluatedTheory U W
  have hb : U.val ≤ W₀.val := by
    have h := SliceSubobjectPredicates.evaluate_monotone (point U) pointDomain_terminal hW
    rw [constantTheory_value, SliceSubobjectPredicates.evaluate_constant] at h
    exact h
  exact ArithmeticSignedTotal.every_consistent_extension_incomplete (F₀) W₀ (hExt.trans hb)
    (SliceSubobjectPredicates.evaluate_consistency (point U) pointDomain_terminal
      (ArithmeticSignedTotal.negation (F₀)) W.val hcW)
    (SliceSubobjectPredicates.evaluate_completeness (point U) pointDomain_terminal
      (ArithmeticSignedTotal.negation (F₀)) W.val hcomp)

theorem essentially_incomplete
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
  ⟨SliceSubobjectPredicates.constant_consistency (U.val : TotalSplit 𝗣𝗔)
    (ArithmeticSignedTotal.negation (F₀)) U.val hcU,
    every_consistent_extension_incomplete U hExt⟩

/-- Theorem and refutation domains of every consistent global extension
inherit the actual arithmetic reduction's inseparability. -/
theorem extension_inseparable
    (hExt : (ArithmeticSignedTotal.theory (F₀)).val ≤ U.val)
    (hcU : U.val ⊓ (Subobject.pullback (ArithmeticSignedTotal.negation (F₀))).obj U.val = ⊥) :
    SubobjectInseparable U.val ((Subobject.pullback (ArithmeticSignedTotal.negation (F₀))).obj U.val) :=
  AssociatedCategory.extension_inseparable ArithmeticSignedTotal.positive ArithmeticSignedTotal.negative
    ArithmeticSignedTotal.inseparable (ArithmeticSignedTotal.atom (F₀))
    (ArithmeticSignedTotal.negation (F₀)) (ArithmeticSignedTotal.theory (F₀)).val U.val
    (ArithmeticSignedTotal.atomic_bounds (F₀)).1 (ArithmeticSignedTotal.atomic_bounds (F₀)).2 hExt hcU

end CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedIncompleteness
