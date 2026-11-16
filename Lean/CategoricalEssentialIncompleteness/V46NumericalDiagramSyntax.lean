/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46DiagramInitialAlgebras
public import CategoricalEssentialIncompleteness.V46SyntaxCoefficientMorphisms
public import CategoricalEssentialIncompleteness.V46NumericalSyntax

/-! # Initial numerical syntax with arbitrary coefficient diagrams -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalDiagramSyntax
open SyntaxCoefficientMorphisms DiagramInitialAlgebras
variable {J : Type u} [Category.{v} J] {I : Type w}
variable (c : I → J ⥤ NumericalTuples.Object) (p q : SyntaxPolynomial I)

def polynomials : J ⥤ ((NumericalTuples.Object × NumericalTuples.Object) ⥤
    NumericalTuples.Object × NumericalTuples.Object) where
  obj j := SyntaxPolynomial.jointFunctor
    (p.mapCoefficients (fun i => (c i).obj j)) (q.mapCoefficients (fun i => (c i).obj j))
  map f := jointAction (fun i => (c i).map f) p q
  map_id j := by
    have hh : (fun i => (c i).map (𝟙 j)) = (fun i => 𝟙 ((c i).obj j)) :=
      funext (fun i => (c i).map_id j)
    apply NatTrans.ext
    funext X
    apply Prod.ext
    · change SyntaxCoefficientMorphisms.component (fun i => (c i).map (𝟙 j)) p X = 𝟙 _
      rw [hh]
      exact SyntaxCoefficientMorphisms.component_id p X
    · change SyntaxCoefficientMorphisms.component (fun i => (c i).map (𝟙 j)) q X = 𝟙 _
      rw [hh]
      exact SyntaxCoefficientMorphisms.component_id q X
  map_comp f g := by
    apply NatTrans.ext
    funext X
    apply Prod.ext
    · change SyntaxCoefficientMorphisms.component (fun i => (c i).map (f ≫ g)) p X =
        SyntaxCoefficientMorphisms.component (fun i => (c i).map f) p X ≫ SyntaxCoefficientMorphisms.component (fun i => (c i).map g) p X
      simp only [Functor.map_comp, component_comp]
    · change SyntaxCoefficientMorphisms.component (fun i => (c i).map (f ≫ g)) q X =
        SyntaxCoefficientMorphisms.component (fun i => (c i).map f) q X ≫ SyntaxCoefficientMorphisms.component (fun i => (c i).map g) q X
      simp only [Functor.map_comp, component_comp]

def componentAlgebra (j : J) : Endofunctor.Algebra ((polynomials c p q).obj j) :=
  (NumericalSyntax.data (p.mapCoefficients (fun i => (c i).obj j))
    (q.mapCoefficients (fun i => (c i).obj j))).1

def componentInitial (j : J) : IsInitial (componentAlgebra c p q j) :=
  (NumericalSyntax.data (p.mapCoefficients (fun i => (c i).obj j))
    (q.mapCoefficients (fun i => (c i).obj j))).2.1

def algebra : Endofunctor.Algebra (diagonal (polynomials c p q)) :=
  DiagramInitialAlgebras.algebra (polynomials c p q) (componentAlgebra c p q) (componentInitial c p q)

def initial : IsInitial (algebra c p q) :=
  DiagramInitialAlgebras.initial (polynomials c p q) (componentAlgebra c p q) (componentInitial c p q)

def fold (B : Endofunctor.Algebra (diagonal (polynomials c p q))) : algebra c p q ⟶ B :=
  (initial c p q).to B

theorem fold_constructor (B : Endofunctor.Algebra (diagonal (polynomials c p q))) :
    (diagonal (polynomials c p q)).map (fold c p q B).f ≫ B.str =
      (algebra c p q).str ≫ (fold c p q B).f := (fold c p q B).h

theorem fold_natural (B : Endofunctor.Algebra (diagonal (polynomials c p q)))
    {j k : J} (f : j ⟶ k) :
    (algebra c p q).a.map f ≫ (fold c p q B).f.app k =
      (fold c p q B).f.app j ≫ B.a.map f := (fold c p q B).f.naturality f

theorem fold_unique (B : Endofunctor.Algebra (diagonal (polynomials c p q)))
    (m : algebra c p q ⟶ B) : m = fold c p q B := (initial c p q).hom_ext _ _

end CategoricalEssentialIncompleteness.V46.NumericalDiagramSyntax
