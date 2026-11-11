/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PrintedObjectCoding

/-! Typed object coding and quotient-program comparison in the production numbering. -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.CodedObjectMembership
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates PrintedObjectCoding
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (Q : STObjectCode) : object T Q ≅ omegaObject T := isoToOmega T Q
example : CodedProgramCategory T ≌ NormalizedCategory T := equivalence T
example (Q R : NormalizedCategory T) : (Q ⟶ R) ≃ ProgramQuotient T := homProgramEquiv T Q R
example (Q : CodedProgramCategory T) : (comparison T).obj Q = objectCode Q := rfl

example {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (comparison T).map (rst f) = rst ((comparison T).map f) := preserves_restrictions T f

example {Q R : NormalizedCategory T} (f : Q ⟶ R) :
    (equivalence T).inverse.map (rst f) = rst ((equivalence T).inverse.map f) :=
  inverse_preserves_restrictions T f

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M (encodeProgram T) x y ↔
      (ExponentialProducts.encodeGraph Number Number).val.Evalb ![x, y] :=
  GraphMorphism.programClass_model (ExponentialProducts.encode T Number Number) M x y

example (Q R : STObjectCode) :
    (isoToOmega T (.product Q R)).hom =
      CategoryTheory.PCategoryStruct.nearProd_map (isoToOmega T Q).hom (isoToOmega T R).hom ≫
        (PrintedObjectCoding.omegaProductIso T).hom := rfl

example (Q R : STObjectCode) :
    (isoToOmega T (.coproduct Q R)).hom =
      CategoryTheory.CoprodStruct.coprod_map (isoToOmega T Q).hom (isoToOmega T R).hom ≫
        (TypedRecursionCategory.omegaCoprodIso T).hom := rfl
