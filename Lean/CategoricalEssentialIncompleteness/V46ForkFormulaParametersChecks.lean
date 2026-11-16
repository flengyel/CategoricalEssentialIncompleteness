/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkFormulaParameterChange

/-! # Independent checks of parameterized component folds

Global fork naturality, stable lists, substitution and finite derivations
remain separate obligations in Proposition 10.7.
-/
@[expose] public section
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open ForkFirstOrderFormula
/-- The generic naturality criterion uses only the two constructor
squares. It does not assume an invertible endofunctor comparison. -/
example {X Y : Type u} [Category X] [Category Y]
    {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R)
    {F : X ⥤ X} {G : Y ⥤ Y} (θ : F ⋙ L ⟶ L ⋙ G)
    (A B : Endofunctor.Algebra F) (hA : IsInitial A)
    (A' B' : Endofunctor.Algebra G) (s : L.obj A.a ⟶ A'.a) (t : L.obj B.a ⟶ B'.a)
    (hs : θ.app A.a ≫ G.map s ≫ A'.str = L.map A.str ≫ s)
    (ht : θ.app B.a ≫ G.map t ≫ B'.str = L.map B.str ≫ t)
    (f : A ⟶ B) (g : A' ⟶ B') : s ≫ g.f = L.map f.f ≫ t :=
  LaxAlgebraAdjunction.fold_natural adj θ A B hA A' B' s t hs ht f g

namespace ForkParameterChecks
open ForkFormulaParameterComponents
local instance (X : C) : Regular (Over X) := RegularSlices.regular X

/-- N, D and P are arbitrary numerical objects, including empty carriers. -/
example (N D P : C) : IsInitial (algebra N D P) := initial N D P

example (N D P : C) : (algebra N D P).a =
    constantFamily P (componentAlgebra N D).a := rfl

example (N D P : C) (B : Endofunctor.Algebra (polynomial N D P)) :
    (fold N D P B).f.left ≫ B.a.hom = (constantFamily P (componentAlgebra N D).a).hom ∧
    (polynomial N D P).map (fold N D P B).f ≫ B.str =
      (algebra N D P).str ≫ (fold N D P B).f :=
  ⟨fold_over N D P B, fold_constructor N D P B⟩

example (N D P : C) (B : Endofunctor.Algebra (polynomial N D P))
    (m : algebra N D P ⟶ B) : m = fold N D P B := fold_unique N D P B m

/-- The parameter and atom morphisms are arbitrary, including morphisms
that identify labels. The target carrier may be any family over Q. -/
example (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q)) :
    (ForkFormulaParameterChange.fold N b h B).left ≫ B.a.hom =
      (algebra N D P).a.hom ≫ b ∧
    (ForkFormulaParameterChange.comparison N b h).app (algebra N D P).a ≫
      (polynomial N E Q).map (ForkFormulaParameterChange.fold N b h B) ≫ B.str =
        (Over.map b).map (algebra N D P).str ≫ ForkFormulaParameterChange.fold N b h B :=
  ⟨ForkFormulaParameterChange.fold_over N b h B,
    ForkFormulaParameterChange.fold_constructor N b h B⟩

example (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E) :
    (ForkFormulaParameterChange.coefficientMap N b h false).left = prod.map b (𝟙 N) ∧
    (ForkFormulaParameterChange.coefficientMap N b h true).left = prod.map b h := ⟨rfl, rfl⟩

example (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q))
    (f g : (algebra N D P).a.left ⟶ B.a.left)
    (hfP : f ≫ B.a.hom = (algebra N D P).a.hom ≫ b)
    (hgP : g ≫ B.a.hom = (algebra N D P).a.hom ≫ b)
    (hf : (ForkFormulaParameterChange.comparison N b h).app (algebra N D P).a ≫
      (polynomial N E Q).map (Over.homMk f hfP) ≫ B.str =
        (Over.map b).map (algebra N D P).str ≫ Over.homMk f hfP)
    (hg : (ForkFormulaParameterChange.comparison N b h).app (algebra N D P).a ≫
      (polynomial N E Q).map (Over.homMk g hgP) ≫ B.str =
        (Over.map b).map (algebra N D P).str ≫ Over.homMk g hgP) : f = g :=
  ForkFormulaParameterChange.underlying_unique N b h B f g hfP hgP hf hg

end ForkParameterChecks

#print axioms LaxAlgebraAdjunction.rightAlgebra
#print axioms LaxAlgebraAdjunction.mate_hom_iff
#print axioms LaxAlgebraAdjunction.fold_constructor
#print axioms LaxAlgebraAdjunction.unique
#print axioms LaxAlgebraAdjunction.fold_natural
#print axioms LaxPolynomialComparison.naturality
#print axioms LaxPolynomialComparison.comparison
#print axioms LaxPolynomialComparison.joint
#print axioms LaxPolynomialComparison.input_natural
#print axioms ForkFormulaParameterComponents.initial
#print axioms ForkFormulaParameterComponents.fold_over
#print axioms ForkFormulaParameterComponents.fold_constructor
#print axioms ForkFormulaParameterComponents.fold_unique
#print axioms ForkFormulaParameterChange.comparison
#print axioms ForkFormulaParameterChange.fold
#print axioms ForkFormulaParameterChange.fold_over
#print axioms ForkFormulaParameterChange.fold_constructor
#print axioms ForkFormulaParameterChange.unique
#print axioms ForkFormulaParameterChange.underlying_unique
