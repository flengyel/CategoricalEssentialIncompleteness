/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFold

/-! # The concrete evaluator gives actual arrows into every parameter-family algebra -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (P : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T))
variable (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (a.withParameters P) (b.withParameters P)))

example : constantFamily P (termCarrier a b) ⟶ B.a.1 := termFold T a b B

example : (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).a ⟶ B.a :=
  fold T a b B

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (q : Obj T M (P ⨯ termCarrier a b)) (x : Obj T M B.a.1.left) :
    (F T M).map (termFoldMap T a b B) q = x ↔
      ((decode T P a b B).evaluationFormula false).val.Evalb
        ![((F T M).map (prod.fst : P ⨯ termCarrier a b ⟶ P) q).val,
          ((F T M).map (prod.snd : P ⨯ termCarrier a b ⟶ termCarrier a b) q).val, x.val] :=
  termFoldMap_eval T a b B M q x
