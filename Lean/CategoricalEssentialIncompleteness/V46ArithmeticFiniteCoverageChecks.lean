/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticFiniteCoverage

/-! # Independent checks of coverage at arbitrary internal vector lengths -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open ArithmeticFiniteCoverage
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (s l : M) :
    (formula (M := M)).val.Eval ![s, l] id ↔ ∀ x, MemVec x s → MemVec x l :=
  (formula_eval s l).trans (covers_iff s l)

example : 𝚺₁-Relation (fun s l : M => ∀ i < len s, MemVec (nth s i) l) :=
  covers_definable 𝚺 0

example : 𝚷₁-Relation (fun s l : M => ∀ i < len s, MemVec (nth s i) l) :=
  covers_definable 𝚷 0

example (a b l : M) :
    (∀ i < len (SyntacticSyntax.Words.append a b),
      MemVec (nth (SyntacticSyntax.Words.append a b) i) l) ↔
      (∀ i < len a, MemVec (nth a i) l) ∧ (∀ i < len b, MemVec (nth b i) l) :=
  covers_append a b l

example (a b : M) : ∀ x, MemVec x a → MemVec x (SyntacticSyntax.Words.append a b) :=
  (covers_iff _ _).mp (covers_append_left a b)

#print axioms ArithmeticFiniteCoverage.Covers
#print axioms ArithmeticFiniteCoverage.covers_definable
#print axioms ArithmeticFiniteCoverage.covers_iff
#print axioms ArithmeticFiniteCoverage.covers_nil
#print axioms ArithmeticFiniteCoverage.covers_adjoin
#print axioms ArithmeticFiniteCoverage.covers_append
#print axioms ArithmeticFiniteCoverage.covers_refl
#print axioms ArithmeticFiniteCoverage.covers_trans
#print axioms ArithmeticFiniteCoverage.covers_append_left
#print axioms ArithmeticFiniteCoverage.covers_append_right
#print axioms ArithmeticFiniteCoverage.formula
#print axioms ArithmeticFiniteCoverage.formula_eval
