/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax

/-! # One-sort constructor initiality obtained from the two-sort algebra -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable {D : Type u} [Category.{v} D] [HasFiniteProducts D] [HasFiniteCoproducts D]

/-- A term power ignores every map on the second recursive sort. Its
comparison map is an isomorphism without any hypothesis on that map. -/
theorem termPower_secondMap_isIso (X : D) {Y Z : D} (g : Y ⟶ Z) (n : ℕ) :
    IsIso ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.map
      ((𝟙 X, g) : (X,Y) ⟶ (X,Z))) := by
  induction n with
  | zero => change IsIso (𝟙 (⊤_ D)); infer_instance
  | succ n ih =>
      cases n with
      | zero => change IsIso (𝟙 X); infer_instance
      | succ n =>
          change IsIso (prod.map
            ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) (n+1)).eval.map
              ((𝟙 X,g) : (X,Y) ⟶ (X,Z))) (𝟙 X))
          let := ih
          infer_instance

/-- The precise finite rule-label expression has no formula leaves.
This supplies the comparison for every rule family and arity bound. -/
theorem constructors_secondMap_isIso (R : ℕ → D) (N : ℕ)
    (X : D) {Y Z : D} (g : Y ⟶ Z) :
    IsIso ((SyntaxPolynomial.constructors R N).eval.map
      ((𝟙 X,g) : (X,Y) ⟶ (X,Z))) := by
  induction N with
  | zero => change IsIso (prod.map (𝟙 (R 0)) (𝟙 (⊤_ D))); infer_instance
  | succ N ih =>
      change IsIso (coprod.map
        ((SyntaxPolynomial.constructors R N).eval.map ((𝟙 X,g) : (X,Y) ⟶ (X,Z)))
        (prod.map (𝟙 (R (N+1)))
          ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) (N+1)).eval.map
            ((𝟙 X,g) : (X,Y) ⟶ (X,Z)))))
      let := ih
      let := termPower_secondMap_isIso X g (N+1)
      infer_instance

/-- The literal first-sort constructor polynomial, evaluated with a
terminal second coordinate. -/
def constructorFunctor (R : ℕ → D) (N : ℕ) : D ⥤ D :=
  ((𝟭 D).prod' ((Functor.const D).obj (⊤_ D))) ⋙
    (SyntaxPolynomial.constructors R N).eval

variable (R : ℕ → D) (N : ℕ)
variable (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.constructors R N) .unit))

def constructorProjection :
    (SyntaxPolynomial.constructors R N).eval.obj A.a ⟶
      (constructorFunctor R N).obj A.a.1 :=
  (SyntaxPolynomial.constructors R N).eval.map
    ((𝟙 A.a.1, terminal.from A.a.2) : A.a ⟶ (A.a.1, ⊤_ D))

instance constructorProjection_isIso : IsIso (constructorProjection R N A) :=
  constructors_secondMap_isIso R N A.a.1 (terminal.from A.a.2)

def projectedConstructorAlgebra : Endofunctor.Algebra (constructorFunctor R N) where
  a := A.a.1
  str := inv (constructorProjection R N A) ≫ A.str.1

def liftConstructorAlgebra (B : Endofunctor.Algebra (constructorFunctor R N)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.constructors R N) .unit) where
  a := (B.a, ⊤_ D)
  str := (B.str, 𝟙 (⊤_ D))

theorem constructorProjection_factor {Y : D} (f : A.a.1 ⟶ Y) :
    (SyntaxPolynomial.constructors R N).eval.map
        ((f, terminal.from A.a.2) : A.a ⟶ (Y, ⊤_ D)) =
      constructorProjection R N A ≫ (constructorFunctor R N).map f := by
  change (SyntaxPolynomial.constructors R N).eval.map _ =
    (SyntaxPolynomial.constructors R N).eval.map _ ≫
      (SyntaxPolynomial.constructors R N).eval.map _
  rw [← Functor.map_comp]
  congr 1
  exact Prod.ext (Category.id_comp f).symm (Category.comp_id _).symm

/-- Every one-sort algebra morphism extends to a two-sort algebra morphism by the unique
map to the terminal second coordinate. -/
def liftConstructorHom (B : Endofunctor.Algebra (constructorFunctor R N))
    (f : projectedConstructorAlgebra R N A ⟶ B) : A ⟶ liftConstructorAlgebra R N B where
  f := (f.f, terminal.from A.a.2)
  h := by
    apply Prod.ext
    · change (SyntaxPolynomial.constructors R N).eval.map
        ((f.f,terminal.from A.a.2) : A.a ⟶ (B.a,⊤_ D)) ≫ B.str = A.str.1 ≫ f.f
      rw [constructorProjection_factor, Category.assoc, f.h]
      change constructorProjection R N A ≫
        ((inv (constructorProjection R N A) ≫ A.str.1) ≫ f.f) = _
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    · exact terminalIsTerminal.hom_ext _ _

def constructorFoldHom (hA : IsInitial A)
    (B : Endofunctor.Algebra (constructorFunctor R N)) :
    projectedConstructorAlgebra R N A ⟶ B where
  f := (hA.to (liftConstructorAlgebra R N B)).f.1
  h := by
    apply (cancel_epi (constructorProjection R N A)).mp
    change constructorProjection R N A ≫
      ((constructorFunctor R N).map (hA.to (liftConstructorAlgebra R N B)).f.1 ≫ B.str) =
        constructorProjection R N A ≫
          ((inv (constructorProjection R N A) ≫ A.str.1) ≫ _)
    rw [← Category.assoc, ← constructorProjection_factor]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    have h := congrArg Prod.fst (hA.to (liftConstructorAlgebra R N B)).h
    change (SyntaxPolynomial.constructors R N).eval.map
        (((hA.to (liftConstructorAlgebra R N B)).f.1,
          (hA.to (liftConstructorAlgebra R N B)).f.2) : A.a ⟶ (B.a,⊤_ D)) ≫ B.str =
      A.str.1 ≫ (hA.to (liftConstructorAlgebra R N B)).f.1 at h
    have ht : (hA.to (liftConstructorAlgebra R N B)).f.2 = terminal.from A.a.2 :=
      terminalIsTerminal.hom_ext _ _
    rw [ht] at h
    exact h

/-- The one-sort universal property is proved by lifting each candidate morphism and
applying the joint-algebra uniqueness theorem. -/
def projectedConstructorInitial (hA : IsInitial A) :
    IsInitial (projectedConstructorAlgebra R N A) :=
  IsInitial.ofUniqueHom (fun B => constructorFoldHom R N A hA B) (fun B f => by
    apply Endofunctor.Algebra.Hom.ext
    exact congrArg (fun h : A ⟶ liftConstructorAlgebra R N B => h.f.1)
      (hA.hom_ext (liftConstructorHom R N A B f)
        (hA.to (liftConstructorAlgebra R N B))))

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
