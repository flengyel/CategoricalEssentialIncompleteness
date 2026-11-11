/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalTranslations
public import CategoricalEssentialIncompleteness.V46CategoricalFreeVariableLaws

/-! # Interpretation of nullary predicates by closed sentences

The initial fold interprets arbitrary nullary predicates by closed
sentences. Its constructor equations and uniqueness preserve the named
variables.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

/-- The atom map into the formula carrier; the sentence factorization
is obtained from its empty occurrence list. -/
def atomFormula : X ⟶ S.algebra.a.2 :=
  prod.lift (𝟙 X) (terminal.from X) ≫ S.relationConstructors

theorem atom_occurrences : atomFormula S ≫ S.formulaOccurrences =
    terminal.from X ≫ S.lists.algebra.nil := by
  rw [atomFormula, Category.assoc, S.relation_occurrences]
  simp [SyntaxPolynomial.constructors, SyntaxPolynomial.power,
    SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
    StableListAlgebra.constructorOccurrences, StableListAlgebra.tupleAppend]

def atomSentence : X ⟶ S.sentenceObject :=
  pullback.lift (atomFormula S) (terminal.from X) (atom_occurrences S)

@[reassoc (attr := simp)] theorem atomSentence_inclusion :
    atomSentence S ≫ S.sentenceInclusion = atomFormula S := pullback.lift_fst _ _ _

def interpretationAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0)
    (SyntaxPolynomial.formulaExpression V (fun _ => X) 0)) where
  a := Q.algebra.a
  str := (coprod.desc Q.variableConstructor (prod.fst ≫ initial.to _),
    coprod.desc
      (coprod.desc
        (coprod.desc
          (coprod.desc Q.equalityConstructor (prod.fst ≫ f ≫ Q.sentenceInclusion))
          Q.negationConstructor)
        Q.implicationConstructor)
      Q.quantifierConstructor)

def interpretation : S.algebra.a ⟶ Q.algebra.a := S.fold (interpretationAlgebra Q f)

theorem variable_law : S.variableConstructor ≫ (interpretation S Q f).1 =
    Q.variableConstructor := by
  have h := congrArg Prod.fst (S.fold_commutes (interpretationAlgebra Q f))
  have hh := congrArg (fun k => coprod.inl ≫ k) h
  simpa [interpretation, interpretationAlgebra, CategoricalSyntax.variableConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.termExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    Category.assoc] using hh.symm

theorem equality : S.equalityConstructor ≫ (interpretation S Q f).2 =
    prod.map (interpretation S Q f).1 (interpretation S Q f).1 ≫
      Q.equalityConstructor := by
  have h := congrArg Prod.snd (S.fold_commutes (interpretationAlgebra Q f))
  have hh := congrArg (fun k =>
    (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [interpretation, interpretationAlgebra, CategoricalSyntax.equalityConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

theorem atom : atomFormula S ≫ (interpretation S Q f).2 = f ≫ Q.sentenceInclusion := by
  have h := congrArg Prod.snd (S.fold_commutes (interpretationAlgebra Q f))
  have hh := congrArg (fun k =>
    (prod.lift (𝟙 X) (terminal.from X) ≫ coprod.inr ≫
      coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [interpretation, interpretationAlgebra, atomFormula,
    CategoricalSyntax.relationConstructors, SyntaxPolynomial.jointFunctor,
    SyntaxPolynomial.formulaExpression, SyntaxPolynomial.constructors,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

theorem negation : S.negationConstructor ≫ (interpretation S Q f).2 =
    (interpretation S Q f).2 ≫ Q.negationConstructor := by
  have h := congrArg Prod.snd (S.fold_commutes (interpretationAlgebra Q f))
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [interpretation, interpretationAlgebra, CategoricalSyntax.negationConstructor,
    CategoricalSyntax.negationInjection, SyntaxPolynomial.jointFunctor,
    SyntaxPolynomial.formulaExpression, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

theorem implication : S.implicationConstructor ≫ (interpretation S Q f).2 =
    prod.map (interpretation S Q f).2 (interpretation S Q f).2 ≫
      Q.implicationConstructor := by
  have h := congrArg Prod.snd (S.fold_commutes (interpretationAlgebra Q f))
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl) ≫ k) h
  simpa [interpretation, interpretationAlgebra, CategoricalSyntax.implicationConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

theorem quantifier : S.quantifierConstructor ≫ (interpretation S Q f).2 =
    prod.map (𝟙 V) (interpretation S Q f).2 ≫ Q.quantifierConstructor := by
  have h := congrArg Prod.snd (S.fold_commutes (interpretationAlgebra Q f))
  have hh := congrArg (fun k => coprod.inr ≫ k) h
  simpa [interpretation, interpretationAlgebra, CategoricalSyntax.quantifierConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

def terminalProductIso (Z : D) : Z ≅ Z ⨯ (⊤_ D) where
  hom := prod.lift (𝟙 _) (terminal.from _)
  inv := prod.fst
  hom_inv_id := prod.lift_fst _ _
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · exact Subsingleton.elim _ _

/-- The empty function-constructor input has no labels. This proof uses
its product with the terminal object, rather than identifying carriers. -/
def emptyFunctionsInitial : IsInitial ((⊥_ D) ⨯ (⊤_ D)) := by
  exact (initialIsInitial : IsInitial (⊥_ D)).ofIso (terminalProductIso (⊥_ D))

/-- Constructor compatibility determines the interpretation from a
nullary-predicate syntax. These hypotheses describe the candidate
morphism; the existence of the interpretation was constructed above. -/
theorem unique (m : S.algebra.a ⟶ Q.algebra.a)
    (hv : S.variableConstructor ≫ m.1 = Q.variableConstructor)
    (he : S.equalityConstructor ≫ m.2 = prod.map m.1 m.1 ≫ Q.equalityConstructor)
    (ha : atomFormula S ≫ m.2 = f ≫ Q.sentenceInclusion)
    (hn : S.negationConstructor ≫ m.2 = m.2 ≫ Q.negationConstructor)
    (hi : S.implicationConstructor ≫ m.2 = prod.map m.2 m.2 ≫ Q.implicationConstructor)
    (hq : S.quantifierConstructor ≫ m.2 = prod.map (𝟙 V) m.2 ≫ Q.quantifierConstructor) :
    m = interpretation S Q f := by
  apply S.fold_unique (interpretationAlgebra Q f) m
  apply Prod.ext
  · apply coprod.hom_ext
    · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.termExpression,
        SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
        interpretationAlgebra, CategoricalSyntax.variableConstructor, Category.assoc] using hv.symm
    · apply (emptyFunctionsInitial (D := D)).hom_ext
  · apply coprod.hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
              SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
              SyntaxPolynomial.productFunctor, interpretationAlgebra,
              CategoricalSyntax.equalityConstructor, Category.assoc] using he.symm
          · have : IsIso (prod.lift (𝟙 X) (terminal.from X)) :=
              (terminalProductIso X).isIso_hom
            apply (cancel_epi (prod.lift (𝟙 X) (terminal.from X))).mp
            simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
              SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
              SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor, interpretationAlgebra,
              atomFormula, CategoricalSyntax.relationConstructors, Category.assoc] using ha.symm
        · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
            SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
            interpretationAlgebra, CategoricalSyntax.negationConstructor,
            CategoricalSyntax.negationInjection, Category.assoc] using hn.symm
      · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
          SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
          SyntaxPolynomial.productFunctor, interpretationAlgebra,
          CategoricalSyntax.implicationConstructor, Category.assoc] using hi.symm
    · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
        interpretationAlgebra, CategoricalSyntax.quantifierConstructor,
        Category.assoc] using hq.symm

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
