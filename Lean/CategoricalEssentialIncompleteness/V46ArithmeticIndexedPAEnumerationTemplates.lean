/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationWords
public import Mathlib.Tactic.FinCases

/-! # The seventeen arithmetic/order seed templates

The names are numerical inputs of the word graphs. Instantiation returns named syntax,
and the graph compiler is proved to return its postfix code. The existential-variable
freshness condition is retained.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

inductive TermSchema
  | var (slot : ℕ)
  | zero
  | one
  | add (left right : TermSchema)
  | mul (left right : TermSchema)

inductive FormulaSchema
  | equal (left right : TermSchema)
  | less (left right : TermSchema)
  | neg (body : FormulaSchema)
  | imp (left right : FormulaSchema)
  | all (slot : ℕ) (body : FormulaSchema)

namespace TermSchema
def expression : TermSchema → Words.Expr
  | .var i => Words.varWord (.slot i)
  | .zero => Words.zero
  | .one => Words.one
  | .add left right => Words.add left.expression right.expression
  | .mul left right => Words.mul left.expression right.expression

def instantiate (env : ℕ) : TermSchema → Term
  | .var i => .var (Words.value (.slot i) env)
  | .zero => NamedArithmeticSignature.zero
  | .one => NamedArithmeticSignature.one
  | .add left right => NamedArithmeticSignature.add (left.instantiate env) (right.instantiate env)
  | .mul left right => NamedArithmeticSignature.mul (left.instantiate env) (right.instantiate env)

theorem expression_code (env : ℕ) (t : TermSchema) :
    Words.value t.expression env = termCode (t.instantiate env) := by
  induction t with
  | var i => exact Words.variable_value (.slot i) env
  | zero => exact Words.zero_value env
  | one => exact Words.one_value env
  | add left right ihl ihr => exact Words.add_value _ _ env _ _ ihl ihr
  | mul left right ihl ihr => exact Words.mul_value _ _ env _ _ ihl ihr
end TermSchema

namespace FormulaSchema
def expression : FormulaSchema → Words.Expr
  | .equal left right => Words.equal left.expression right.expression
  | .less left right => Words.less left.expression right.expression
  | .neg body => Words.neg body.expression
  | .imp left right => Words.imp left.expression right.expression
  | .all i body => Words.all (.slot i) body.expression

def instantiate (env : ℕ) : FormulaSchema → Formula
  | .equal left right => .equal (left.instantiate env) (right.instantiate env)
  | .less left right => NamedArithmeticSignature.less (left.instantiate env) (right.instantiate env)
  | .neg body => .neg (body.instantiate env)
  | .imp left right => .imp (left.instantiate env) (right.instantiate env)
  | .all i body => .all (Words.value (.slot i) env) (body.instantiate env)

theorem expression_code (env : ℕ) (φ : FormulaSchema) :
    Words.value φ.expression env = formulaCode (φ.instantiate env) := by
  induction φ with
  | equal left right =>
      exact Words.equal_value _ _ env _ _
        (TermSchema.expression_code env left) (TermSchema.expression_code env right)
  | less left right =>
      exact Words.less_value _ _ env _ _
        (TermSchema.expression_code env left) (TermSchema.expression_code env right)
  | neg body ih => exact Words.neg_value _ env _ ih
  | imp left right ihl ihr => exact Words.imp_value _ _ env _ _ ihl ihr
  | all i body ih => exact Words.all_value (.slot i) _ env _ _ rfl ih

def disjunction (φ ψ : FormulaSchema) : FormulaSchema := .imp (.neg φ) ψ
def conjunction (φ ψ : FormulaSchema) : FormulaSchema := .neg (.imp φ (.neg ψ))
def existential (i : ℕ) (φ : FormulaSchema) : FormulaSchema := .neg (.all i (.neg φ))
def le (s t : TermSchema) : FormulaSchema := disjunction (.equal s t) (.less s t)
end FormulaSchema

abbrev x : TermSchema := .var 0
abbrev y : TermSchema := .var 1
abbrev z : TermSchema := .var 2

def simpleTemplate (k : Fin 17) : FormulaSchema :=
  match k.val with
  | 0 => .equal (.add x .zero) x
  | 1 => .equal (.add (.add x y) z) (.add x (.add y z))
  | 2 => .equal (.add x y) (.add y x)
  | 3 => .imp (.less x y) (FormulaSchema.existential 2 (.equal (.add x z) y))
  | 4 => FormulaSchema.le .zero x
  | 5 => .less .zero .one
  | 6 => .imp (.less .zero x) (FormulaSchema.le .one x)
  | 7 => .imp (.less x y) (.less (.add x z) (.add y z))
  | 8 => .equal (.mul x .zero) .zero
  | 9 => .equal (.mul x .one) x
  | 10 => .equal (.mul (.mul x y) z) (.mul x (.mul y z))
  | 11 => .equal (.mul x y) (.mul y x)
  | 12 => .imp (FormulaSchema.conjunction (.less x y) (.less .zero z))
      (.less (.mul x z) (.mul y z))
  | 13 => .equal (.mul x (.add y z)) (.add (.mul x y) (.mul x z))
  | 14 => .neg (.less x x)
  | 15 => .imp (FormulaSchema.conjunction (.less x y) (.less y z)) (.less x z)
  | _ => FormulaSchema.disjunction (.less x y)
      (FormulaSchema.disjunction (.equal x y) (.less y x))

def fresh (k : Fin 17) (env : ℕ) : Prop :=
  k.val = 3 → Words.value (.slot 2) env ≠ Words.value (.slot 0) env ∧
    Words.value (.slot 2) env ≠ Words.value (.slot 1) env

theorem simpleTemplate_seed (k : Fin 17) (env : ℕ) (h : fresh k env) :
    PASeed ((simpleTemplate k).instantiate env) := by
  fin_cases k
  · exact .addZero _
  · exact .addAssoc _ _ _
  · exact .addComm _ _
  · exact .addEqOfLt _ _ _ (h rfl).1 (h rfl).2
  · exact .zeroLe _
  · exact .zeroLtOne
  · exact .oneLeOfZeroLt _
  · exact .addLtAdd _ _ _
  · exact .mulZero _
  · exact .mulOne _
  · exact .mulAssoc _ _ _
  · exact .mulComm _ _
  · exact .mulLtMul _ _ _
  · exact .distr _ _ _
  · exact .ltIrrefl _
  · exact .ltTrans _ _ _
  · exact .ltTri _ _

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
