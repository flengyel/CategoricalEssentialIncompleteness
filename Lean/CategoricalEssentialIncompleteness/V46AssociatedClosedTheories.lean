/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RetractedClosedTheories
public import CategoricalEssentialIncompleteness.V46SliceEvaluationSubobjects
public import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness

/-! # Essential incompleteness and arbitrary associated-slice extensions -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.AssociatedClosedTheories

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
local instance sliceRegular (U : D) : Regular (Over U) := RegularSlices.regular U
local instance sliceExtensive (U : D) : FinitaryExtensive (Over U) :=
  RegularSlices.finitaryExtensive U
local instance constantLimits (U : D) : PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U
local instance evaluationLimits {Z U : D} (point : Z ⟶ U) (hZ : IsTerminal Z) :
    PreservesFiniteLimits (SliceBaseChangeGeometry.evaluation point hZ) :=
  SliceBaseChangeGeometry.evaluation_preservesFiniteLimits point hZ

variable {V : D} (P : FirstOrderPresentation V) (U : D)

/-- The parameterized deduction assumption at axiom subobjects of the actual
constant sentence family, with the original logical operations transported. -/
abbrev SliceProofs :=
  (W : Subobject ((constantFamilyFunctor U).obj P.syntaxData.sentenceObject)) →
  Endofunctor.Algebra (firstOrderRules ((constantFamilyFunctor U).map P.syntaxData.logicalAxioms)
    ((constantFamilyFunctor U).map P.syntaxData.sentenceInclusion) W.arrow
    (FirstOrderRuleTransport.mappedAll (constantFamilyFunctor U) P.syntaxData.quantifierConstructor)
    (FirstOrderRuleTransport.mappedImp (constantFamilyFunctor U)
      P.syntaxData.implicationConstructor)).inference

variable (Q : SliceProofs P U) (hQ : ∀ W, IsInitial (Q W))

def Consistent (W : Subobject (constantFamily U P.syntaxData.sentenceObject)) : Prop :=
  W ⊓ (Subobject.pullback ((constantFamilyFunctor U).map P.syntaxData.sentenceNegation)).obj W = ⊥

def Complete (W : Subobject (constantFamily U P.syntaxData.sentenceObject)) : Prop :=
  W ⊔ (Subobject.pullback ((constantFamilyFunctor U).map P.syntaxData.sentenceNegation)).obj W = ⊤

def EssentiallyIncomplete (T : FirstOrderReflection.Theory Q) : Prop :=
  Consistent P U T.val ∧
    ∀ W : FirstOrderReflection.Theory Q, T.val ≤ W.val → Consistent P U W.val →
      ¬ Complete P U W.val

def constantTheory (T : P.Theories) : FirstOrderReflection.Theory Q :=
  (SliceClosedTheories.constantTheoryFunctor U P.proofs P.initial Q hQ).obj T

theorem constantTheory_value (T : P.Theories) :
    (constantTheory P U Q hQ T).val =
      FiniteLimitSubobjects.object (constantFamilyFunctor U) T.val := rfl

variable {Z : D} (point : Z ⟶ U) (hZ : IsTerminal Z)

include hQ in
theorem evaluate_closed (W : FirstOrderReflection.Theory Q) :
    FirstOrderReflection.generated P.proofs (SliceSubobjectPredicates.evaluate point hZ W.val) =
      SliceSubobjectPredicates.evaluate point hZ W.val := by
  have h := RetractedClosedTheories.closed_back (constantFamilyFunctor U)
    (SliceBaseChangeGeometry.evaluation point hZ)
    (SliceBaseChangeGeometry.ordinaryRetraction point hZ)
    P.proofs P.initial Q hQ W.val W.property
  have heq : SliceSubobjectPredicates.evaluate point hZ W.val =
      RetractedClosedTheories.backObject (constantFamilyFunctor U)
        (SliceBaseChangeGeometry.evaluation point hZ)
        (SliceBaseChangeGeometry.ordinaryRetraction point hZ) W.val :=
    SliceSubobjectPredicates.evaluate_eq_retraction point hZ W.val
  rw [heq]
  exact h

def evaluationTheory (W : FirstOrderReflection.Theory Q) : P.Theories :=
  ⟨SliceSubobjectPredicates.evaluate point hZ W.val, evaluate_closed P U Q hQ point hZ W⟩

include hQ point hZ in
theorem essential_incomplete_iff (T : P.Theories) (hc : P.Consistent T.val) :
    P.EssentiallyIncomplete T ↔ EssentiallyIncomplete P U Q (constantTheory P U Q hQ T) := by
  constructor
  · intro h
    refine ⟨SliceSubobjectPredicates.constant_consistency U
      P.syntaxData.sentenceNegation T.val hc, ?_⟩
    intro W hTW hcW hcompW
    let W₀ := evaluationTheory P U Q hQ point hZ W
    have hbound : T.val ≤ W₀.val := by
      have hb := SliceSubobjectPredicates.evaluate_monotone point hZ hTW
      rw [constantTheory_value, SliceSubobjectPredicates.evaluate_constant] at hb
      exact hb
    exact h.2 W₀ hbound
      (SliceSubobjectPredicates.evaluate_consistency point hZ
        P.syntaxData.sentenceNegation W.val hcW)
      (SliceSubobjectPredicates.evaluate_completeness point hZ
        P.syntaxData.sentenceNegation W.val hcompW)
  · intro h
    refine ⟨hc, ?_⟩
    intro W hTW hcW hcompW
    exact h.2 (constantTheory P U Q hQ W)
      (FiniteLimitSubobjects.object_monotone (constantFamilyFunctor U) hTW)
      (SliceSubobjectPredicates.constant_consistency U P.syntaxData.sentenceNegation W.val hcW)
      (SliceSubobjectPredicates.constant_completeness U P.syntaxData.sentenceNegation W.val hcompW)

end CategoricalEssentialIncompleteness.V46.AssociatedClosedTheories
