/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesPrinted

/-! # Exact statement checks for the arithmetic diagonal construction -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedTuringMorphism
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.PrintedChecks
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example : ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceTau).hom =
    arrowOfIndex 𝗣𝗔 .omega .omega UniformTrace.universalIndex := printed_tau_is_universal
example : ((PrintedObjectCoding.comparison 𝗣𝗔).map
    (TypedRecursionCategory.omegaCoprodIso 𝗣𝗔).inv).hom = 𝟙 (omegaObject 𝗣𝗔) :=
  printed_parity_is_identity
example (x z : M) : SyntacticModel.programRelation 𝗣𝗔 M
    ((PrintedObjectCoding.comparison 𝗣𝗔).map
      (PCategoryStruct.diag (omegaObject 𝗣𝗔))).hom.val x z ↔
    z = ExponentialPairing.code x x := printed_diagonal M x z
example (a b y : M) : SyntacticModel.programRelation 𝗣𝗔 M
    ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceTau).hom.val
      (ExponentialPairing.code a b) y ↔
    UniformTrace.graph.val.Evalb ![a,b,y] := printed_tau M a b y
example (x m : M) : SyntacticModel.programRelation 𝗣𝗔 M
    ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceParityDiagonal).hom.val x (2 * m) ↔
    UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m] := printed_parity_inl M x m
example (x m : M) : SyntacticModel.programRelation 𝗣𝗔 M
    ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceParityDiagonal).hom.val x (2 * m + 1) ↔
    UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m + 1] := printed_parity_inr M x m
end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.PrintedChecks
