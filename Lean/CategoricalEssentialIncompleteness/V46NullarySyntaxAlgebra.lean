/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-! # Algebra morphisms for syntax with nullary predicates

The six constructor equations determine an algebra morphism for the
manuscript polynomial with no function symbols and nullary predicates X.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable {E V X : D}

abbrev AlgebraWithEmpty (E V X : D) := Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression V (fun _ => E) 0)
  (SyntaxPolynomial.formulaExpression V (fun _ => X) 0))

abbrev Algebra (V X : D) := AlgebraWithEmpty (⊥_ D) V X

def variableConstructor (A : AlgebraWithEmpty E V X) : V ⟶ A.a.1 := coprod.inl ≫ A.str.1

def equalityConstructor (A : AlgebraWithEmpty E V X) : A.a.1 ⨯ A.a.1 ⟶ A.a.2 :=
  coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ A.str.2

def atomConstructor (A : AlgebraWithEmpty E V X) : X ⟶ A.a.2 :=
  prod.lift (𝟙 X) (terminal.from X) ≫
    coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ A.str.2

def negationConstructor (A : AlgebraWithEmpty E V X) : A.a.2 ⟶ A.a.2 :=
  coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ A.str.2

def implicationConstructor (A : AlgebraWithEmpty E V X) : A.a.2 ⨯ A.a.2 ⟶ A.a.2 :=
  coprod.inr ≫ coprod.inl ≫ A.str.2

def quantifierConstructor (A : AlgebraWithEmpty E V X) : V ⨯ A.a.2 ⟶ A.a.2 := coprod.inr ≫ A.str.2

def terminalProductIso (Z : D) : Z ≅ Z ⨯ (⊤_ D) where
  hom := prod.lift (𝟙 _) (terminal.from _)
  inv := prod.fst
  hom_inv_id := prod.lift_fst _ _
  inv_hom_id := by
    apply prod.hom_ext
    · simp
    · exact Subsingleton.elim _ _

def emptyInputInitial (hE : IsInitial E) : IsInitial (E ⨯ (⊤_ D)) :=
  hE.ofIso (terminalProductIso E)

def emptyFunctionsInitial : IsInitial ((⊥_ D) ⨯ (⊤_ D)) :=
  emptyInputInitial initialIsInitial

def constantInitial [HasStrictInitialObjects D] (P : D) :
    IsInitial (constantFamily P (⊥_ D)) := by
  let h : IsInitial (P ⨯ (⊥_ D)) := IsInitial.ofStrict prod.snd initialIsInitial
  exact IsInitial.ofUniqueHom
    (fun A => Over.homMk (h.to A.left) (h.hom_ext _ _))
    (fun _ _ => Over.OverMorphism.ext (h.hom_ext _ _))

def homOfConstructorsOfInitial (hE : IsInitial E) {A B : AlgebraWithEmpty E V X} (m : A.a ⟶ B.a)
    (hv : variableConstructor A ≫ m.1 = variableConstructor B)
    (he : equalityConstructor A ≫ m.2 = prod.map m.1 m.1 ≫ equalityConstructor B)
    (ha : atomConstructor A ≫ m.2 = atomConstructor B)
    (hn : negationConstructor A ≫ m.2 = m.2 ≫ negationConstructor B)
    (hi : implicationConstructor A ≫ m.2 = prod.map m.2 m.2 ≫ implicationConstructor B)
    (hq : quantifierConstructor A ≫ m.2 = prod.map (𝟙 V) m.2 ≫ quantifierConstructor B) :
    A ⟶ B where
  f := m
  h := by
    apply Prod.ext
    · apply coprod.hom_ext
      · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.termExpression,
          SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          variableConstructor, Category.assoc] using hv.symm
      · apply (emptyInputInitial hE).hom_ext
    · apply coprod.hom_ext
      · apply coprod.hom_ext
        · apply coprod.hom_ext
          · apply coprod.hom_ext
            · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
                SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
                SyntaxPolynomial.productFunctor, equalityConstructor, Category.assoc] using he.symm
            · have : IsIso (prod.lift (𝟙 X) (terminal.from X)) :=
                (terminalProductIso X).isIso_hom
              apply (cancel_epi (prod.lift (𝟙 X) (terminal.from X))).mp
              simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
                SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
                SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
                atomConstructor, Category.assoc] using ha.symm
          · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
              SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
              negationConstructor, Category.assoc] using hn.symm
        · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
            SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
            SyntaxPolynomial.productFunctor, implicationConstructor, Category.assoc] using hi.symm
      · simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
          SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
          quantifierConstructor, Category.assoc] using hq.symm

def homOfConstructors {A B : Algebra V X} (m : A.a ⟶ B.a)
    (hv : variableConstructor A ≫ m.1 = variableConstructor B)
    (he : equalityConstructor A ≫ m.2 = prod.map m.1 m.1 ≫ equalityConstructor B)
    (ha : atomConstructor A ≫ m.2 = atomConstructor B)
    (hn : negationConstructor A ≫ m.2 = m.2 ≫ negationConstructor B)
    (hi : implicationConstructor A ≫ m.2 = prod.map m.2 m.2 ≫ implicationConstructor B)
    (hq : quantifierConstructor A ≫ m.2 = prod.map (𝟙 V) m.2 ≫ quantifierConstructor B) :
    A ⟶ B := homOfConstructorsOfInitial initialIsInitial m hv he ha hn hi hq

@[simp] theorem homOfConstructors_f {A B : Algebra V X} (m : A.a ⟶ B.a) hv he ha hn hi hq :
    (homOfConstructors m hv he ha hn hi hq).f = m := rfl

end CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra
