/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparison
public import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution
public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumerals
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationRecordLaws

/-! # Literal constructor graphs used to enumerate native PA axiom matrices

Expressions compute only word codes. Their graphs are explicit Σ₁ formulas,
and their values are proved in every PA model before standard native syntax
is compared. No definition of PA axioms is supplied as a premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.Words
open NamedArithmeticSignature

inductive Expr
  | slot (index : ℕ)
  | constant (n : ℕ)
  | pair (left right : Expr)
  | term (payload : Expr)
  | formula (payload : Expr)

/-- Parameter environments are ordinary ordered pair-tuples; these projections
are existential computation data and do not add labels to the syntax. -/
def slotGraph : ℕ → 𝚺₁.Semisentence 2
  | 0 => .mkSigma “out env. !pi₁Def.val out env”
  | i + 1 =>
      let G := slotGraph i
      .mkSigma “out env. ∃ tail, !pi₂Def.val tail env ∧ !G.val out tail”

section SlotModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

def slotValue : ℕ → M → M
  | 0, env => π₁ env
  | i + 1, env => slotValue i (π₂ env)

@[simp] theorem slotGraph_eval (i : ℕ) (out env : M) :
    (slotGraph i).val.Evalb ![out,env] ↔ out = slotValue i env := by
  induction i generalizing env with
  | zero => simp [slotGraph,slotValue]
  | succ i ih => simp [slotGraph,slotValue,ih]

end SlotModels

namespace Compiler

def graph (termGraph formulaGraph : 𝚺₁.Semisentence 2) : Expr → 𝚺₁.Semisentence 2
  | .slot i => slotGraph i
  | .constant n => .mkSigma “out env. out = !!(n)”
  | .pair left right =>
      let L := graph termGraph formulaGraph left
      let R := graph termGraph formulaGraph right
      .mkSigma “out env. ∃ l r, !L.val l env ∧ !R.val r env ∧ !pairDef.val out l r”
  | .term payload =>
      let P := graph termGraph formulaGraph payload
      .mkSigma “out env. ∃ u, !P.val u env ∧ !termGraph.val out u”
  | .formula payload =>
      let P := graph termGraph formulaGraph payload
      .mkSigma “out env. ∃ u, !P.val u env ∧ !formulaGraph.val out u”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

def value (termValue formulaValue : M → M) : Expr → M → M
  | .slot i, env => slotValue i env
  | .constant n, _ => (n : M)
  | .pair left right, env => Arithmetic.pair (value termValue formulaValue left env)
      (value termValue formulaValue right env)
  | .term payload, env => termValue (value termValue formulaValue payload env)
  | .formula payload, env => formulaValue (value termValue formulaValue payload env)

theorem graph_eval (termGraph formulaGraph : 𝚺₁.Semisentence 2)
    (termValue formulaValue : M → M)
    (ht : ∀ out u, termGraph.val.Evalb ![out,u] ↔ out = termValue u)
    (hf : ∀ out u, formulaGraph.val.Evalb ![out,u] ↔ out = formulaValue u)
    (expr : Expr) (out env : M) :
    (graph termGraph formulaGraph expr).val.Evalb ![out,env] ↔
      out = value termValue formulaValue expr env := by
  induction expr generalizing out with
  | slot i => simp [graph,value]
  | constant n => simp [graph,value,numeral_eq_natCast_app]
  | pair left right il ir => simp [graph,value,il,ir]
  | term payload ih => simp [graph,value,ih,ht]
  | formula payload ih => simp [graph,value,ih,hf]

end Models
end Compiler

def termConstructorGraph : 𝚺₁.Semisentence 2 :=
  SyntacticSyntax.Coding.constructorGraph false termPolynomial

def formulaConstructorGraph : 𝚺₁.Semisentence 2 :=
  SyntacticSyntax.Coding.constructorGraph true formulaPolynomial

def graph : Expr → 𝚺₁.Semisentence 2 :=
  Compiler.graph termConstructorGraph formulaConstructorGraph

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

def value : Expr → M → M :=
  Compiler.value (SyntacticSyntax.Coding.constructor false termPolynomial)
    (SyntacticSyntax.Coding.constructor true formulaPolynomial)

@[simp] theorem value_slot (i : ℕ) (env : M) : value (.slot i) env = slotValue i env := rfl

@[simp] theorem graph_eval (expr : Expr) (out env : M) :
    (graph expr).val.Evalb ![out,env] ↔ out = value expr env := by
  exact Compiler.graph_eval termConstructorGraph formulaConstructorGraph
    (SyntacticSyntax.Coding.constructor false termPolynomial)
    (SyntacticSyntax.Coding.constructor true formulaPolynomial)
    (SyntacticSyntax.Coding.constructorGraph_eval false termPolynomial)
    (SyntacticSyntax.Coding.constructorGraph_eval true formulaPolynomial) expr out env

end Models

def varWord (name : Expr) : Expr := .term (.pair name (.constant 0))

def nullaryTerm (symbol : Expr) : Expr :=
  .term (.pair (.pair (.pair (.pair symbol (.constant 0)) (.constant 0)) (.constant 0)) (.constant 1))

def zero : Expr := nullaryTerm (.constant 0)
def one : Expr := nullaryTerm (.constant 1)

def binaryTerm (symbol left right : Expr) : Expr :=
  .term (.pair (.pair (.pair symbol (.pair left right)) (.constant 1)) (.constant 1))

def add (left right : Expr) : Expr := binaryTerm (.constant 0) left right
def mul (left right : Expr) : Expr := binaryTerm (.constant 1) left right

def equal (left right : Expr) : Expr :=
  .formula (.pair (.pair (.pair (.pair (.pair left right) (.constant 0))
    (.constant 0)) (.constant 0)) (.constant 0))

def less (left right : Expr) : Expr :=
  .formula (.pair (.pair (.pair (.pair
    (.pair (.pair (.constant 1) (.pair left right)) (.constant 1)) (.constant 1))
      (.constant 0)) (.constant 0)) (.constant 0))

def neg (body : Expr) : Expr :=
  .formula (.pair (.pair (.pair body (.constant 1)) (.constant 0)) (.constant 0))

def imp (left right : Expr) : Expr :=
  .formula (.pair (.pair (.pair left right) (.constant 1)) (.constant 0))

def all (name body : Expr) : Expr := .formula (.pair (.pair name body) (.constant 1))
def disjunction (left right : Expr) : Expr := imp (neg left) right
def conjunction (left right : Expr) : Expr := neg (imp left (neg right))
def existential (name body : Expr) : Expr := neg (all name (neg body))
def le (left right : Expr) : Expr := disjunction (equal left right) (less left right)

def inductionMatrix (name body base step : Expr) : Expr :=
  imp base (imp (all name (imp body step)) (all name body))

section Standard
open NamedPostfixEncoding

@[simp] theorem variable_value (name : Expr) (env : ℕ) :
    value (varWord name) env = NamedArithmeticSignature.termCode (.var (value name env)) := by
  simp [varWord,value,Compiler.value,NamedArithmeticSignature.termCode,NamedPostfixEncoding.termCode,
    Arithmetic.natCast_nat]

@[simp] theorem zero_value (env : ℕ) :
    value zero env = NamedArithmeticSignature.termCode NamedArithmeticSignature.zero := by
  rfl

@[simp] theorem one_value (env : ℕ) :
    value one env = NamedArithmeticSignature.termCode NamedArithmeticSignature.one := by
  rfl

theorem add_value (left right : Expr) (env : ℕ) (r t : Term)
    (hr : value left env = NamedArithmeticSignature.termCode r)
    (ht : value right env = NamedArithmeticSignature.termCode t) :
    value (add left right) env = NamedArithmeticSignature.termCode (NamedArithmeticSignature.add r t) := by
  simp only [value] at hr ht
  simp only [add,binaryTerm,value,Compiler.value,Arithmetic.natCast_nat,hr,ht]
  rfl

theorem mul_value (left right : Expr) (env : ℕ) (r t : Term)
    (hr : value left env = NamedArithmeticSignature.termCode r)
    (ht : value right env = NamedArithmeticSignature.termCode t) :
    value (mul left right) env = NamedArithmeticSignature.termCode (NamedArithmeticSignature.mul r t) := by
  simp only [value] at hr ht
  simp only [mul,binaryTerm,value,Compiler.value,Arithmetic.natCast_nat,hr,ht]
  rfl

theorem equal_value (left right : Expr) (env : ℕ) (r t : Term)
    (hr : value left env = NamedArithmeticSignature.termCode r)
    (ht : value right env = NamedArithmeticSignature.termCode t) :
    value (equal left right) env = NamedArithmeticSignature.formulaCode (.equal r t) := by
  simp only [value] at hr ht
  simp only [equal,value,Compiler.value,Arithmetic.natCast_nat,hr,ht]
  rfl

theorem less_value (left right : Expr) (env : ℕ) (r t : Term)
    (hr : value left env = NamedArithmeticSignature.termCode r)
    (ht : value right env = NamedArithmeticSignature.termCode t) :
    value (less left right) env = NamedArithmeticSignature.formulaCode (NamedArithmeticSignature.less r t) := by
  simp only [value] at hr ht
  simp only [less,value,Compiler.value,Arithmetic.natCast_nat,hr,ht]
  rfl

theorem neg_value (body : Expr) (env : ℕ) (φ : Formula)
    (hφ : value body env = NamedArithmeticSignature.formulaCode φ) :
    value (neg body) env = NamedArithmeticSignature.formulaCode (.neg φ) := by
  simp only [value] at hφ
  simp only [neg,value,Compiler.value,Arithmetic.natCast_nat,hφ]
  rfl

theorem imp_value (left right : Expr) (env : ℕ) (φ ψ : Formula)
    (hφ : value left env = NamedArithmeticSignature.formulaCode φ)
    (hψ : value right env = NamedArithmeticSignature.formulaCode ψ) :
    value (imp left right) env = NamedArithmeticSignature.formulaCode (.imp φ ψ) := by
  simp only [value] at hφ hψ
  simp only [imp,value,Compiler.value,Arithmetic.natCast_nat,hφ,hψ]
  rfl

theorem all_value (name body : Expr) (env x : ℕ) (φ : Formula)
    (hx : value name env = x) (hφ : value body env = NamedArithmeticSignature.formulaCode φ) :
    value (all name body) env = NamedArithmeticSignature.formulaCode (.all x φ) := by
  simp only [value] at hx hφ
  simp only [all,value,Compiler.value,Arithmetic.natCast_nat,hx,hφ]
  rfl

theorem inductionMatrix_value (name body base step : Expr) (env x : ℕ)
    (φ φ0 φs : Formula) (hx : value name env = x)
    (hφ : value body env = NamedArithmeticSignature.formulaCode φ)
    (h0 : value base env = NamedArithmeticSignature.formulaCode φ0)
    (hs : value step env = NamedArithmeticSignature.formulaCode φs) :
    value (inductionMatrix name body base step) env =
      NamedArithmeticSignature.formulaCode
        (ArithmeticNamedAxiomComparison.inductionMatrix x φ φ0 φs) := by
  exact imp_value base _ env φ0 _ h0
    (imp_value _ _ env _ _
      (all_value name _ env x _ hx (imp_value body step env φ φs hφ hs))
      (all_value name body env x φ hx hφ))

end Standard
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration.Words
