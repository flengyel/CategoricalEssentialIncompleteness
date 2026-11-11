/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxInterpretation

/-! # Checks for the free-syntax interpretation prerequisites -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D}

open NullaryInterpretation
variable {X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

example : S.variableConstructor ≫ (interpretation S Q f).1 = Q.variableConstructor :=
  variable_law S Q f
example : atomFormula S ≫ (interpretation S Q f).2 = f ≫ Q.sentenceInclusion := atom S Q f
example : S.negationConstructor ≫ (interpretation S Q f).2 =
    (interpretation S Q f).2 ≫ Q.negationConstructor := negation S Q f
example (m : S.algebra.a ⟶ Q.algebra.a)
    (hv : S.variableConstructor ≫ m.1 = Q.variableConstructor)
    (he : S.equalityConstructor ≫ m.2 = prod.map m.1 m.1 ≫ Q.equalityConstructor)
    (ha : atomFormula S ≫ m.2 = f ≫ Q.sentenceInclusion)
    (hn : S.negationConstructor ≫ m.2 = m.2 ≫ Q.negationConstructor)
    (hi : S.implicationConstructor ≫ m.2 = prod.map m.2 m.2 ≫ Q.implicationConstructor)
    (hq : S.quantifierConstructor ≫ m.2 = prod.map (𝟙 V) m.2 ≫ Q.quantifierConstructor) :
    m = interpretation S Q f := unique S Q f m hv he ha hn hi hq

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.interpretation
#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.atom
#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.unique
