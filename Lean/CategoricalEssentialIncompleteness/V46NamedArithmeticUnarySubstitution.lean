/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSubstitution
public import CategoricalEssentialIncompleteness.V46NamedArithmeticTranslationFreeVariables

/-! Unary arithmetic formulas specialize the already proved generic
finite-source numeral-substitution construction. The diagonal index may
remain opaque inside the source formula throughout this specialization. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticUnarySubstitution
open NamedArithmeticSignature NamedArithmeticNumerals ConcreteNamedSubstitution

def namedFormula (α : ArithmeticSemisentence 1) : Formula :=
  ArithmeticNamedTranslation.translateFormula 1 ![0] α

theorem namedFormula_freeVariables (α : ArithmeticSemisentence 1) :
    ∀ y, y ∈ (namedFormula α).freeVariables → y = 0 :=
  fun y hy => ArithmeticNamedTranslation.translateUnary_freeVariables α y hy

def sourceWord (α : ArithmeticSemisentence 1) : ℕ :=
  NamedArithmeticFixedSubstitution.sourceWord (namedFormula α)

def graph (α : ArithmeticSemisentence 1) : 𝚺₁.Semisentence 2 :=
  NamedArithmeticFixedSubstitution.graph (namedFormula α)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def value (α : ArithmeticSemisentence 1) (n : M) : M :=
  NamedArithmeticFixedSubstitution.value (namedFormula α) n

@[simp] theorem graph_eval (α : ArithmeticSemisentence 1) (out n : M) :
    (graph α).val.Evalb ![out,n] ↔ out = value α n :=
  NamedArithmeticFixedSubstitution.graph_eval (M := M) (namedFormula α) out n

instance value_defined (α : ArithmeticSemisentence 1) :
    𝚺₁-Function₁ (value α : M → M) via graph α :=
  NamedArithmeticFixedSubstitution.value_defined (M := M) (namedFormula α)
instance value_definable (α : ArithmeticSemisentence 1) : 𝚺₁-Function₁ (value α : M → M) :=
  NamedArithmeticFixedSubstitution.value_definable (M := M) (namedFormula α)

 theorem sourceWord_freeVariables (α : ArithmeticSemisentence 1) :
    freeVariables variableSymbols functionSymbols relationSymbols bound (sourceWord α : M) =
      ((SyntacticSyntax.NatVectors.pack (namedFormula α).freeVariables : ℕ) : M) :=
  NamedArithmeticFixedSubstitution.sourceWord_freeVariables (M := M) (namedFormula α)

 theorem sourceWord_members (α : ArithmeticSemisentence 1) (name : M)
    (h : member name (freeVariables variableSymbols functionSymbols relationSymbols bound (sourceWord α : M)) = 1) : name = 0 :=
  NamedArithmeticFixedSubstitution.sourceWord_members (M := M) (namedFormula α) (namedFormula_freeVariables α) name h

 theorem value_eq_output (α : ArithmeticSemisentence 1) (n : M) :
    value α n = NamedArithmeticModelSubstitution.formulaOutput (M := M) (σ := functionSymbols)
      (π := relationSymbols) (d := bound) 0 (numeralCode n) (namedFormula α) :=
  NamedArithmeticFixedSubstitution.value_eq_output (M := M) (namedFormula α) n

 theorem value_carrier (α : ArithmeticSemisentence 1) (n : M) :
    formulaCarrier.val.Evalb ![value α n] :=
  NamedArithmeticFixedSubstitution.value_carrier (M := M) (namedFormula α) n

 theorem value_closed (α : ArithmeticSemisentence 1) (n : M) :
    freeVariables variableSymbols functionSymbols relationSymbols bound (value α n) = 0 :=
  NamedArithmeticFixedSubstitution.value_closed (M := M) (namedFormula α) (namedFormula_freeVariables α) n

 theorem value_sentence (α : ArithmeticSemisentence 1) (n : M) :
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).val.Evalb
      ![value α n] :=
  NamedArithmeticFixedSubstitution.value_sentence (M := M) (namedFormula α) (namedFormula_freeVariables α) n

 theorem value_admissible (α : ArithmeticSemisentence 1) (n : M) :
    substitutionFreeFor variableSymbols functionSymbols relationSymbols bound 0 (numeralCode n) (sourceWord α : M) = 1 :=
  NamedArithmeticFixedSubstitution.value_admissible (M := M) (namedFormula α) n

 theorem value_success (α : ArithmeticSemisentence 1) (n : M) :
    substitutionResult variableSymbols functionSymbols relationSymbols bound 0 (numeralCode n) (sourceWord α : M) = ok (value α n) :=
  NamedArithmeticFixedSubstitution.value_success (M := M) (namedFormula α) n

end Models

 theorem value_primrec (α : ArithmeticSemisentence 1) : Primrec (value α : ℕ → ℕ) :=
  NamedArithmeticFixedSubstitution.value_primrec (namedFormula α)

 def morphism (α : ArithmeticSemisentence 1) : GraphMorphism 𝗣𝗔 variableSymbols
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound) :=
  NamedArithmeticFixedSubstitution.morphism (namedFormula α) (namedFormula_freeVariables α)

@[simp] theorem morphism_graph_eval (α : ArithmeticSemisentence 1)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n word : M) :
    (morphism α).graph.val.Evalb ![n,word] ↔ word = value α n :=
  NamedArithmeticFixedSubstitution.morphism_graph_eval (M := M) (namedFormula α) (namedFormula_freeVariables α) n word

end CategoricalEssentialIncompleteness.V46.NamedArithmeticUnarySubstitution
