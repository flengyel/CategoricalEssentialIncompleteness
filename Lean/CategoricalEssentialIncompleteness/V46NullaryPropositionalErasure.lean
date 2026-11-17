/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebraHom
public import CategoricalEssentialIncompleteness.V46NullarySyntaxInterpretation

/-! # Erasure from nullary first-order syntax to propositional operations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure

variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {V X Y : C}

/-- Equality is a fixed proposition and quantification forgets the variable. -/
def algebra (V : C) (atom : X ⟶ Y) (neg : Y ⟶ Y)
    (imp : Y ⨯ Y ⟶ Y) (truth : ⊤_ C ⟶ Y) : NullarySyntaxAlgebra.Algebra V X where
  a := (⊤_ C, Y)
  str := (coprod.desc (terminal.from _) (terminal.from _),
    coprod.desc (coprod.desc (coprod.desc
      (coprod.desc (terminal.from _ ≫ truth) (prod.fst ≫ atom)) neg) imp) prod.snd)

variable (S : CategoricalSyntax V (fun _ => ⊥_ C) (fun _ => X) 0)
variable (atom : X ⟶ Y) (neg : Y ⟶ Y) (imp : Y ⨯ Y ⟶ Y) (truth : ⊤_ C ⟶ Y)

def erase : S.algebra.a.2 ⟶ Y := (S.fold (algebra V atom neg imp truth)).2

@[reassoc] theorem equality : S.equalityConstructor ≫ erase S atom neg imp truth =
    terminal.from _ ≫ truth := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V atom neg imp truth))
  have hh := congrArg (fun k =>
    (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [erase, algebra, CategoricalSyntax.equalityConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem atom_law :
    NullaryInterpretation.atomFormula S ≫ erase S atom neg imp truth = atom := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V atom neg imp truth))
  have hh := congrArg (fun k => (prod.lift (𝟙 X) (terminal.from X) ≫ coprod.inr ≫
    coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [erase, algebra, NullaryInterpretation.atomFormula,
    CategoricalSyntax.relationConstructors, SyntaxPolynomial.jointFunctor,
    SyntaxPolynomial.formulaExpression, SyntaxPolynomial.constructors,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem negation : S.negationConstructor ≫ erase S atom neg imp truth =
    erase S atom neg imp truth ≫ neg := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V atom neg imp truth))
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [erase, algebra, CategoricalSyntax.negationConstructor,
    CategoricalSyntax.negationInjection, SyntaxPolynomial.jointFunctor,
    SyntaxPolynomial.formulaExpression, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem implication : S.implicationConstructor ≫ erase S atom neg imp truth =
    prod.map (erase S atom neg imp truth) (erase S atom neg imp truth) ≫ imp := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V atom neg imp truth))
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl) ≫ k) h
  simpa [erase, algebra, CategoricalSyntax.implicationConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem quantifier : S.quantifierConstructor ≫ erase S atom neg imp truth =
    prod.snd ≫ erase S atom neg imp truth := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V atom neg imp truth))
  have hh := congrArg (fun k => coprod.inr ≫ k) h
  simpa [erase, algebra, CategoricalSyntax.quantifierConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    Category.assoc] using hh.symm

/-- Uniqueness among all formula morphisms satisfying the five printed clauses. -/
theorem unique (m : S.algebra.a.2 ⟶ Y)
    (he : S.equalityConstructor ≫ m = terminal.from _ ≫ truth)
    (ha : NullaryInterpretation.atomFormula S ≫ m = atom)
    (hn : S.negationConstructor ≫ m = m ≫ neg)
    (hi : S.implicationConstructor ≫ m = prod.map m m ≫ imp)
    (hq : S.quantifierConstructor ≫ m = prod.snd ≫ m) :
    m = erase S atom neg imp truth := by
  let f : S.algebra ⟶ algebra V atom neg imp truth :=
    NullarySyntaxAlgebra.homOfConstructors (terminal.from _, m)
      (terminalIsTerminal.hom_ext _ _)
      (by simpa [NullarySyntaxAlgebra.equalityConstructor, algebra,
        CategoricalSyntax.equalityConstructor, SyntaxPolynomial.eval, SyntaxPolynomial.power,
        SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.termExpression, SyntaxPolynomial.jointFunctor,
        SyntaxPolynomial.productFunctor, SyntaxPolynomial.sumFunctor, Category.assoc] using he)
      (by simpa [NullarySyntaxAlgebra.atomConstructor, algebra,
        NullaryInterpretation.atomFormula, CategoricalSyntax.relationConstructors,
        SyntaxPolynomial.constructors, SyntaxPolynomial.eval, SyntaxPolynomial.power,
        SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.termExpression, SyntaxPolynomial.jointFunctor,
        SyntaxPolynomial.productFunctor, SyntaxPolynomial.sumFunctor, Category.assoc] using ha)
      (by simpa [NullarySyntaxAlgebra.negationConstructor, algebra,
        CategoricalSyntax.negationConstructor, CategoricalSyntax.negationInjection,
        SyntaxPolynomial.eval, SyntaxPolynomial.power,
        SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.termExpression, SyntaxPolynomial.jointFunctor,
        SyntaxPolynomial.productFunctor, SyntaxPolynomial.sumFunctor, Category.assoc] using hn)
      (by simpa [NullarySyntaxAlgebra.implicationConstructor, algebra,
        CategoricalSyntax.implicationConstructor, SyntaxPolynomial.eval, SyntaxPolynomial.power,
        SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.termExpression, SyntaxPolynomial.jointFunctor,
        SyntaxPolynomial.productFunctor, SyntaxPolynomial.sumFunctor, Category.assoc] using hi)
      (by simpa [NullarySyntaxAlgebra.quantifierConstructor, algebra,
        CategoricalSyntax.quantifierConstructor, SyntaxPolynomial.eval, SyntaxPolynomial.power,
        SyntaxPolynomial.formulaExpression,
        SyntaxPolynomial.termExpression, SyntaxPolynomial.jointFunctor,
        SyntaxPolynomial.productFunctor, SyntaxPolynomial.sumFunctor, Category.assoc] using hq)
  exact congrArg (fun k => k.f.2) (S.initial.hom_ext f (S.initial.to _))

/-- Erasure commutes with every morphism preserving the propositional operations. -/
theorem map {Z : C} (a : X ⟶ Z) (n : Z ⟶ Z) (i : Z ⨯ Z ⟶ Z) (t : ⊤_ C ⟶ Z)
    (m : Y ⟶ Z) (ha : atom ≫ m = a) (hn : neg ≫ m = m ≫ n)
    (hi : imp ≫ m = prod.map m m ≫ i) (ht : truth ≫ m = t) :
    erase S atom neg imp truth ≫ m = erase S a n i t := by
  apply unique
  · rw [← Category.assoc, equality, Category.assoc, ht]
  · rw [← Category.assoc, atom_law, ha]
  · rw [← Category.assoc, negation, Category.assoc, hn, ← Category.assoc]
  · rw [← Category.assoc, implication, Category.assoc, hi, ← Category.assoc,
      prod.map_map]
  · rw [← Category.assoc, quantifier, Category.assoc]

end CategoricalEssentialIncompleteness.V46.NullaryPropositionalErasure
