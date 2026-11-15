/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTheory
public import CategoricalEssentialIncompleteness.V46SyntacticSliceDerivations
public import CategoricalEssentialIncompleteness.V46NullaryLogicalPoint
public import CategoricalEssentialIncompleteness.V46SliceClosedTheories

/-! # Parameterized deduction and a common logical point for the arithmetic theory -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedDeduction
local notation "F₀" => ArithmeticSignedTheory.presentation
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
local notation "S" => NullaryPresentations.syntaxData (F₀) N
local notation "G" => SyntacticPredicates.realization 𝗣𝗔

local instance (P : TotalSplit 𝗣𝗔) : Regular (Over P) := RegularSlices.regular P
local instance (P : TotalSplit 𝗣𝗔) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

/-- Only axiom subobjects of the constant sentence family are indexed.
Their coefficients may depend on the parameter in an arbitrary way. -/
def rules (P : TotalSplit 𝗣𝗔)
    (A : Subobject ((constantFamilyFunctor P).obj ((G).obj (S).sentenceObject))) :=
  firstOrderRules ((constantFamilyFunctor P).map ((G).map (S).logicalAxioms))
    ((constantFamilyFunctor P).map ((G).map (S).sentenceInclusion)) A.arrow
    (FirstOrderRuleTransport.mappedAll (constantFamilyFunctor P)
      (FirstOrderRuleTransport.mappedAll (G) (S).quantifierConstructor))
    (FirstOrderRuleTransport.mappedImp (constantFamilyFunctor P)
      (FirstOrderRuleTransport.mappedImp (G) (S).implicationConstructor))

def proofs (P : TotalSplit 𝗣𝗔)
    (A : Subobject ((constantFamilyFunctor P).obj ((G).obj (S).sentenceObject))) :
    Endofunctor.Algebra (rules P A).inference :=
  SyntacticSliceDerivations.algebra 𝗣𝗔 (rules P A)

def initial (P : TotalSplit 𝗣𝗔)
    (A : Subobject ((constantFamilyFunctor P).obj ((G).obj (S).sentenceObject))) :
    IsInitial (proofs P A) := SyntacticSliceDerivations.initial 𝗣𝗔 (rules P A)

def pointDomain : TotalSplit 𝗣𝗔 := (G).obj terminalCarrier

def pointDomain_terminal : IsTerminal pointDomain :=
  IsTerminal.isTerminalObj (G) _ (SyntacticPredicates.terminalIsTerminal 𝗣𝗔)

/-- The zero label yields a fixed closed instance of the first logical
scheme. It is chosen before quantifying over any theory extension. -/
def theoremPoint : pointDomain ⟶ (G).obj (S).sentenceObject :=
  (G).map (NullaryLogicalPoint.sentence (S) (ArithmeticSignedAtoms.numberInclusion terminalCarrier))

def logicalPoint : pointDomain ⟶ (G).obj (S).logicalParameters :=
  (G).map (NullaryLogicalPoint.logicalInstance (S)
    (ArithmeticSignedAtoms.numberInclusion terminalCarrier))

theorem logicalPoint_diagram : logicalPoint ≫ (G).map (S).logicalAxioms =
    theoremPoint ≫ (G).map (S).sentenceInclusion := by
  unfold logicalPoint theoremPoint
  rw [← Functor.map_comp, NullaryLogicalPoint.logicalInstance_formula, Functor.map_comp]

/-- Every closed target theory contains the same global logical point. -/
theorem point_factors (U : FirstOrderReflection.Theory (ArithmeticSignedTotal.proofs (F₀))) :
    ∃ point : pointDomain ⟶ (U.val : TotalSplit 𝗣𝗔), point ≫ U.val.arrow = theoremPoint :=
  NullaryLogicalPoint.factors ((G).map (S).logicalAxioms) ((G).map (S).sentenceInclusion)
    (FirstOrderRuleTransport.mappedAll (G) (S).quantifierConstructor)
    (FirstOrderRuleTransport.mappedImp (G) (S).implicationConstructor)
    (ArithmeticSignedTotal.proofs (F₀)) theoremPoint logicalPoint logicalPoint_diagram U

end CategoricalEssentialIncompleteness.V46.ArithmeticAssociatedDeduction
