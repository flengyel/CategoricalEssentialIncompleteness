/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformSearch


/-! # Joint functional search for the uniform arithmetic construction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct PCategoryStruct
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearchChecks
open ArithmeticUniformSearch
example (C C' : 𝚺₁.Semisentence 2) : 𝗣𝗔 ⊢
    (let Pair := ExponentialPairing.graph
     let G := eventualGraph (index C C')
     let R := reversedRelation C C'
     “∀ e x w z, !Pair.val w e x → !G.val w z → !R.val e x z”) :=
  sound_PA C C'
example (C C' : 𝚺₁.Semisentence 2) : 𝗣𝗔 ⊢
    (let Pair := ExponentialPairing.graph
     let G := eventualGraph (index C C')
     “∀ e x w, !Pair.val w e x → ((∃ z, !G.val w z) ↔ (!C.val e x ∨ !C'.val e x))”) :=
  domain_PA C C'
example (C C' : 𝚺₁.Semisentence 2) :
    (PrintedObjectCoding.omegaProductIso 𝗣𝗔).inv ≫ lift C C' ≫
      (omegaCoprodIso 𝗣𝗔).hom =
        arrowOfIndex 𝗣𝗔 .omega .omega (SyntacticSearch.searchIndex (inputGraph C C')) :=
  lift_printed_coordinates C C'
example (C C' : 𝚺₁.Semisentence 2) : isTotal (diagonal C C') := diagonal_total C C'
example (C C' : 𝚺₁.Semisentence 2) :
    diagonal C C' ≫ diag (omegaObject 𝗣𝗔) ≫ ArithmeticDiagonalCodes.sourceTau ≫
      (omegaCoprodIso 𝗣𝗔).inv =
        partialPairing (𝟙 (omegaObject 𝗣𝗔)) (diagonal C C') ≫ lift C C' :=
  diagonal_equation C C'
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C C' : 𝚺₁.Semisentence 2) (e x : M) :
    (∃ z : M, (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z]) ↔
      C.val.Evalb ![e,x] ∨ C'.val.Evalb ![e,x] := search_domain_at C C' e x
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C C' : 𝚺₁.Semisentence 2) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x])) (x z : M) :
    (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z] ↔
      (C.val.Evalb ![e,x] ∧ z = 2*x+1) ∨ (C'.val.Evalb ![e,x] ∧ z = 2*x) :=
  (search_exact_at C C' e hd x z).trans (reversedRelation_eval C C' e x z)
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearchChecks
