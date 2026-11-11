/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionRoots
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariables

/-! Literal named-variable substitution and its separately computed free-for
flag. All functions are total on numbers; only source restrictions later assert
that the input is a variable and the replacement and body have their types. -/

@[expose] public section
noncomputable section
local instance primitiveNamedAlgorithmDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

def substitutionPayloadGraph : 𝚺₁.Semisentence 4 :=
  let FV := freeVariablesGraph V σ π d
  let E := Traversal.outputGraph (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) (termRootGraph V σ d) (formulaRootGraph V π d)
  .mkSigma “out x replacement word. ∃ fv tail param, !FV.val fv replacement ∧
    !pairDef.val tail replacement fv ∧ !pairDef.val param x tail ∧ !E.val out param word”

def substitutionResultGraph : 𝚺₁.Semisentence 4 :=
  let E := substitutionPayloadGraph V σ π d
  .mkSigma “out x replacement word. ∃ value, !E.val value x replacement word ∧ !resultGraph.val out value”

def substitutionFreeForGraph : 𝚺₁.Semisentence 4 :=
  let E := substitutionPayloadGraph V σ π d
  .mkSigma “out x replacement word. ∃ value, !E.val value x replacement word ∧ !freeForGraph.val out value”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def substitutionPayload (x replacement word : M) : M :=
  Traversal.output (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
    (termRootGraph V σ d) (formulaRootGraph V π d) (termRoot V σ d) (formulaRoot V π d)
    ⟪x,⟪replacement,freeVariables V σ π d replacement⟫⟫ word

/-- On term inputs this is the rebuilt term; on formula inputs it is
failure zero or the literal success pair. The body sort is read from the word. -/
def substitutionResult (x replacement word : M) : M :=
  result (substitutionPayload V σ π d x replacement word)

/-- This is computed from the independent structural flag field, rather
than being defined as a successful substitution result. -/
def substitutionFreeFor (x replacement word : M) : M :=
  freeFor (substitutionPayload V σ π d x replacement word)

@[simp] theorem substitutionPayloadGraph_eval (out x replacement word : M) :
    (substitutionPayloadGraph V σ π d).val.Evalb ![out,x,replacement,word] ↔
      out = substitutionPayload V σ π d x replacement word := by
  simp [substitutionPayloadGraph,substitutionPayload,Traversal.outputGraph_eval_any _ _ _ _
    (termRoot V σ d) (formulaRoot V π d)]
@[simp] theorem substitutionResultGraph_eval (out x replacement word : M) :
    (substitutionResultGraph V σ π d).val.Evalb ![out,x,replacement,word] ↔
      out = substitutionResult V σ π d x replacement word := by
  simp [substitutionResultGraph,substitutionResult]
@[simp] theorem substitutionFreeForGraph_eval (out x replacement word : M) :
    (substitutionFreeForGraph V σ π d).val.Evalb ![out,x,replacement,word] ↔
      out = substitutionFreeFor V σ π d x replacement word := by
  simp [substitutionFreeForGraph,substitutionFreeFor]

instance substitutionPayload_defined :
    𝚺₁-Function₃ (substitutionPayload V σ π d : M → M → M → M) via substitutionPayloadGraph V σ π d :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3] = v := (Matrix.fun_eq_vec_four v).symm
    simpa [hv] using substitutionPayloadGraph_eval V σ π d (v 0) (v 1) (v 2) (v 3)
instance substitutionResult_defined :
    𝚺₁-Function₃ (substitutionResult V σ π d : M → M → M → M) via substitutionResultGraph V σ π d :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3] = v := (Matrix.fun_eq_vec_four v).symm
    simpa [hv] using substitutionResultGraph_eval V σ π d (v 0) (v 1) (v 2) (v 3)
instance substitutionFreeFor_defined :
    𝚺₁-Function₃ (substitutionFreeFor V σ π d : M → M → M → M) via substitutionFreeForGraph V σ π d :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3] = v := (Matrix.fun_eq_vec_four v).symm
    simpa [hv] using substitutionFreeForGraph_eval V σ π d (v 0) (v 1) (v 2) (v 3)

instance substitutionPayload_definable :
    𝚺₁-Function₃ (substitutionPayload V σ π d : M → M → M → M) :=
  (substitutionPayload_defined V σ π d).to_definable
instance substitutionResult_definable :
    𝚺₁-Function₃ (substitutionResult V σ π d : M → M → M → M) :=
  (substitutionResult_defined V σ π d).to_definable
instance substitutionFreeFor_definable :
    𝚺₁-Function₃ (substitutionFreeFor V σ π d : M → M → M → M) :=
  (substitutionFreeFor_defined V σ π d).to_definable
instance substitutionPayload_definable' (Γ m) :
    Γ-[m + 1]-Function₃ (substitutionPayload V σ π d : M → M → M → M) :=
  (substitutionPayload_definable V σ π d).of_sigmaOne
instance substitutionResult_definable' (Γ m) :
    Γ-[m + 1]-Function₃ (substitutionResult V σ π d : M → M → M → M) :=
  (substitutionResult_definable V σ π d).of_sigmaOne
instance substitutionFreeFor_definable' (Γ m) :
    Γ-[m + 1]-Function₃ (substitutionFreeFor V σ π d : M → M → M → M) :=
  (substitutionFreeFor_definable V σ π d).of_sigmaOne

/-- The literal product chart codes ((x,replacement),word). -/
def codedSubstitutionPayload (input : M) : M :=
  substitutionPayload V σ π d (π₁ (π₁ input)) (π₂ (π₁ input)) (π₂ input)
def codedSubstitutionResult (input : M) : M :=
  substitutionResult V σ π d (π₁ (π₁ input)) (π₂ (π₁ input)) (π₂ input)
def codedSubstitutionFreeFor (input : M) : M :=
  substitutionFreeFor V σ π d (π₁ (π₁ input)) (π₂ (π₁ input)) (π₂ input)

end Models

open SyntacticSyntax.NatVectors

theorem substitutionPayload_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => substitutionPayload V σ π d p.1 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : ℕ × ℕ × ℕ =>
      ⟪p.1,⟪p.2.1,freeVariables V σ π d p.2.1⟫⟫) :=
    pair_primrec.comp Primrec.fst (pair_primrec.comp (Primrec.fst.comp Primrec.snd)
      ((freeVariables_primrec V σ π d).comp (Primrec.fst.comp Primrec.snd)))
  exact (Traversal.output_primrec _ _ _ _ (termRoot V σ d) (formulaRoot V π d)
    (termRoot_primrec V σ d) (formulaRoot_primrec V π d)).comp hp (Primrec.snd.comp Primrec.snd)

theorem substitutionResult_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => substitutionResult V σ π d p.1 p.2.1 p.2.2) :=
  result_primrec.comp (substitutionPayload_primrec V σ π d)

theorem substitutionFreeFor_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => substitutionFreeFor V σ π d p.1 p.2.1 p.2.2) :=
  freeFor_primrec.comp (substitutionPayload_primrec V σ π d)

private theorem codedArguments_primrec :
    Primrec (fun input : ℕ => (π₁ (π₁ input),π₂ (π₁ input),π₂ input)) :=
  Primrec.pair (pi1_primrec.comp pi1_primrec)
    (Primrec.pair (pi2_primrec.comp pi1_primrec) pi2_primrec)

private theorem applyCodedArguments_primrec {f : ℕ × ℕ × ℕ → ℕ} (hf : Primrec f) :
    Primrec (fun input : ℕ => f (π₁ (π₁ input),π₂ (π₁ input),π₂ input)) :=
  hf.comp codedArguments_primrec

theorem codedSubstitutionPayload_primrec : Primrec (codedSubstitutionPayload V σ π d : ℕ → ℕ) := by
  exact Primrec.of_eq (applyCodedArguments_primrec (substitutionPayload_primrec V σ π d)) (fun _ => rfl)
theorem codedSubstitutionResult_primrec : Primrec (codedSubstitutionResult V σ π d : ℕ → ℕ) := by
  exact Primrec.of_eq (applyCodedArguments_primrec (substitutionResult_primrec V σ π d)) (fun _ => rfl)
theorem codedSubstitutionFreeFor_primrec : Primrec (codedSubstitutionFreeFor V σ π d : ℕ → ℕ) := by
  exact Primrec.of_eq (applyCodedArguments_primrec (substitutionFreeFor_primrec V σ π d)) (fun _ => rfl)

theorem codedSubstitutionPayload_natPrimrec : Nat.Primrec (codedSubstitutionPayload V σ π d : ℕ → ℕ) :=
  Primrec.nat_iff.mp (codedSubstitutionPayload_primrec V σ π d)
theorem codedSubstitutionResult_natPrimrec : Nat.Primrec (codedSubstitutionResult V σ π d : ℕ → ℕ) :=
  Primrec.nat_iff.mp (codedSubstitutionResult_primrec V σ π d)
theorem codedSubstitutionFreeFor_natPrimrec : Nat.Primrec (codedSubstitutionFreeFor V σ π d : ℕ → ℕ) :=
  Primrec.nat_iff.mp (codedSubstitutionFreeFor_primrec V σ π d)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
