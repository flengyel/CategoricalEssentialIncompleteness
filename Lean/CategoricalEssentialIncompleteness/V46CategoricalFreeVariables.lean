/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalListOperations

/-! # Occurrence-list folds and the sentence pullback -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

namespace StableListAlgebra

variable {V : D} (L : StableListAlgebra V)

/-- Ordered concatenation on a finite left-associated power of the list
object, with the empty tuple interpreted as the empty list. -/
def tupleAppend : (n : ℕ) →
    (SyntaxPolynomial.power .term n).eval.obj (L.algebra.carrier, L.algebra.carrier) ⟶
      L.algebra.carrier
  | 0 => L.algebra.nil
  | 1 => 𝟙 _
  | n + 2 => prod.map (tupleAppend (n + 1)) (𝟙 _) ≫ L.append

/-- The finite family of function or relation constructors concatenates
the occurrence lists of its arguments in their given order. -/
def constructorOccurrences (σ : ℕ → D) : (d : ℕ) →
    (SyntaxPolynomial.constructors σ d).eval.obj
      (L.algebra.carrier, L.algebra.carrier) ⟶ L.algebra.carrier
  | 0 => prod.snd ≫ L.tupleAppend 0
  | n + 1 => coprod.desc (constructorOccurrences σ n)
      (prod.snd ≫ L.tupleAppend (n + 1))

end StableListAlgebra

namespace CategoricalSyntax

variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

/-- The target algebra for free-variable occurrence lists. -/
def occurrenceAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)) where
  a := (S.lists.algebra.carrier, S.lists.algebra.carrier)
  str :=
    (coprod.desc S.lists.singleton (S.lists.constructorOccurrences σ d),
      coprod.desc
        (coprod.desc
          (coprod.desc (coprod.desc S.lists.append (S.lists.constructorOccurrences π d))
            (𝟙 S.lists.algebra.carrier))
          S.lists.append)
        (S.lists.deletion S.decidableVariables))

def termOccurrences : S.algebra.a.1 ⟶ S.lists.algebra.carrier :=
  (S.fold S.occurrenceAlgebra).1

def formulaOccurrences : S.algebra.a.2 ⟶ S.lists.algebra.carrier :=
  (S.fold S.occurrenceAlgebra).2

/-- The formula-negation constructor is the inclusion of the unary
formula summand followed by the initial algebra's constructor morphism. -/
def negationInjection : S.algebra.a.2 ⟶
    (SyntaxPolynomial.formulaExpression V π d).eval.obj S.algebra.a :=
  coprod.inr ≫ coprod.inl ≫ coprod.inl

def negationConstructor : S.algebra.a.2 ⟶ S.algebra.a.2 :=
  S.negationInjection ≫ S.algebra.str.2

theorem negation_occurrences :
    S.negationConstructor ≫ S.formulaOccurrences = S.formulaOccurrences := by
  have h := congrArg Prod.snd (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => S.negationInjection ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    occurrenceAlgebra, negationInjection, negationConstructor, termOccurrences, formulaOccurrences,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
    Category.assoc] using hh.symm

/-- Definition A.2: sentences are the pullback of the empty occurrence
list along the formula occurrence-list morphism. -/
def sentenceObject : D := pullback S.formulaOccurrences S.lists.algebra.nil

def sentenceInclusion : S.sentenceObject ⟶ S.algebra.a.2 := pullback.fst _ _

instance sentenceInclusion_mono : Mono S.sentenceInclusion := by
  let : Mono S.lists.algebra.nil := S.lists.nil_mono
  exact pullback.fst_of_mono

/-- Negation restricts to the sentence subobject because it preserves
the occurrence list. -/
def sentenceNegation : S.sentenceObject ⟶ S.sentenceObject :=
  pullback.lift (S.sentenceInclusion ≫ S.negationConstructor)
    (pullback.snd S.formulaOccurrences S.lists.algebra.nil) (by
      rw [Category.assoc, S.negation_occurrences]
      exact pullback.condition)

theorem sentenceNegation_inclusion :
    S.sentenceNegation ≫ S.sentenceInclusion =
      S.sentenceInclusion ≫ S.negationConstructor :=
  pullback.lift_fst _ _ _

end CategoricalSyntax

end CategoricalEssentialIncompleteness.V46
