/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationTerms


/-! # Statement checks in `V46ArithmeticNamedPresentationTermsChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
example (n : ℕ) (r : Term) (hr : ∀ x ∈ r.freeVariables, x < n) :
    ArithmeticNamedOpenTranslation.term ![] Fin.val (term n r) = r := term_roundtrip n r hr
example (k : Fin 3) (s : RelationSymbols k.val) (c : Fin k.val → Term) :
    ∃ r t, NamedFiniteSyntax.Formula.relation k s c = less r t := relation_presentation k s c
example (n : ℕ) (r : Term) (x : Fin n) (hx : (term n r).FVar? x) :
    x.val ∈ r.freeVariables := term_fvar n r x hx
universe w
example {K : Type w} [ORingStructure K] (n : ℕ) (r : Term)
    (hr : ∀ x ∈ r.freeVariables, x < n) (ρ : ℕ → K) :
    (term n r).val (s := Arithmetic.standardModel K) ![] (fun i => ρ i.val) =
      r.evaluate ArithmeticNamedTranslation.functions ρ := term_value n r hr ρ
end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
