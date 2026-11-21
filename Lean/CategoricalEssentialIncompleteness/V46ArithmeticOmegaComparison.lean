/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticSignature
public import CategoricalEssentialIncompleteness.V46SyntacticPredicates

/-! # The numerical variable carrier and the identity omega splitting

The predicate realization of all numerical variables has the identity restriction
idempotent. Its comparison to the source identity splitting is proved from the
universal T-model graph equations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ArithmeticOmegaComparison
open SyntacticPredicates
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def identityOmega : TotalSplit T := ⟨⟨omegaObject T, ⊤⟩⟩

theorem variables_idempotent :
    predicateIdem T NamedArithmeticSignature.variableSymbols = ⊤ := by
  apply Idem.ext
  apply CodedHom.ext
  change predicateClass T NamedArithmeticSignature.variableSymbols =
    objectIdempotent T .omega
  apply programClass_ext T
  intro M _ _ x y
  rw [predicateClass_model,SyntacticModel.object_relation]
  simp only [NamedArithmeticSignature.variables_eval,memberFormula_omega_eval,true_and]

def omegaIso : identityOmega T ≅
    (predicateEquivalence T).functor.obj
      (NamedArithmeticSignature.variableSymbols : PredicateCategory T) := by
  apply eqToIso
  change (⟨⟨omegaObject T,⊤⟩⟩ : TotalSplit T) =
    ⟨⟨omegaObject T,predicateIdem T NamedArithmeticSignature.variableSymbols⟩⟩
  exact congrArg (fun e : Idem (omegaObject T) =>
    (⟨⟨omegaObject T,e⟩⟩ : TotalSplit T)) (variables_idempotent T).symm

end CategoricalEssentialIncompleteness.V46.ArithmeticOmegaComparison
