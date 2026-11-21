/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInitial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance

/-! # The initial algebra on the plain postfix parser predicates -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax

section ParameterIsomorphisms
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

theorem parameterHom_component (P : D) (a : SyntaxPolynomial D) {X Y : D × D}
    (f : X ⟶ Y) {Z W : D} (s : a.eval.obj X ⟶ Z) (t : a.eval.obj Y ⟶ W)
    (k : Z ⟶ W) (h : a.eval.map f ≫ t = s ≫ k) :
    (a.withParameters P).eval.map
        ((constantFamilyFunctor P).map f.1, (constantFamilyFunctor P).map f.2) ≫
      (SyntaxPolynomial.parameterComparison P Y a ≫ (constantFamilyFunctor P).map t) =
      (SyntaxPolynomial.parameterComparison P X a ≫ (constantFamilyFunctor P).map s) ≫
        (constantFamilyFunctor P).map k := by
  rw [← Category.assoc, SyntaxPolynomial.parameterComparison_natural,
    Category.assoc, ← Functor.map_comp, h, Functor.map_comp]
  simp only [Category.assoc]

/-- Parameterization acts on algebra morphisms. Its commutation equation follows from
naturality of the specified parameterComparison. -/
def parameterAlgebraHom (a b : SyntaxPolynomial D) (P : D)
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b)} (f : A ⟶ B) :
    SyntaxPolynomial.algebraWithParameters a b A P ⟶
      SyntaxPolynomial.algebraWithParameters a b B P where
  f := ((constantFamilyFunctor P).map f.f.1, (constantFamilyFunctor P).map f.f.2)
  h := Prod.ext
    (parameterHom_component P a f.f A.str.1 B.str.1 f.f.1 (congrArg Prod.fst f.h))
    (parameterHom_component P b f.f A.str.2 B.str.2 f.f.2 (congrArg Prod.snd f.h))

def parameterAlgebraIso (a b : SyntaxPolynomial D) (P : D)
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b)} (i : A ≅ B) :
    SyntaxPolynomial.algebraWithParameters a b A P ≅
      SyntaxPolynomial.algebraWithParameters a b B P :=
  Endofunctor.Algebra.isoMk
    (((constantFamilyFunctor P).prod (constantFamilyFunctor P)).mapIso
      ((Endofunctor.Algebra.forget (SyntaxPolynomial.jointFunctor a b)).mapIso i))
    (parameterAlgebraHom a b P i.hom).h

end ParameterIsomorphisms

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (a b : SyntaxPolynomial (PredicateCategory T))

/-- Both components are the literal numeric-identity parser comparisons. -/
def plainPairIso :
    CategoryTheory.Iso (C := PredicateCategory T × PredicateCategory T)
      (postfixAlgebra T a b).a
      (Postfix.plainCarrier false a b, Postfix.plainCarrier true a b) where
  hom := ((Postfix.plainCarrierIso T false a b).hom,
    (Postfix.plainCarrierIso T true a b).hom)
  inv := ((Postfix.plainCarrierIso T false a b).inv,
    (Postfix.plainCarrierIso T true a b).inv)
  hom_inv_id := Prod.ext (Postfix.plainCarrierIso T false a b).hom_inv_id
    (Postfix.plainCarrierIso T true a b).hom_inv_id
  inv_hom_id := Prod.ext (Postfix.plainCarrierIso T false a b).inv_hom_id
    (Postfix.plainCarrierIso T true a b).inv_hom_id

/-- Conjugating both recursive sorts by numeric identity retains the
same constructor words on the plain parser carriers. -/
def plainPostfixAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b) where
  a := (Postfix.plainCarrier false a b, Postfix.plainCarrier true a b)
  str := (SyntaxPolynomial.jointFunctor a b).map (plainPairIso T a b).inv ≫
    (postfixAlgebra T a b).str ≫ (plainPairIso T a b).hom

def plainAlgebraIso : postfixAlgebra T a b ≅ plainPostfixAlgebra T a b := by
  refine Endofunctor.Algebra.isoMk (plainPairIso T a b) ?_
  change (SyntaxPolynomial.jointFunctor a b).map (plainPairIso T a b).hom ≫
      ((SyntaxPolynomial.jointFunctor a b).map (plainPairIso T a b).inv ≫
        (postfixAlgebra T a b).str ≫ (plainPairIso T a b).hom) =
    (postfixAlgebra T a b).str ≫ (plainPairIso T a b).hom
  rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    (SyntaxPolynomial.jointFunctor a b).map_id, Category.id_comp]

theorem plain_constructor_comparison :
    (SyntaxPolynomial.jointFunctor a b).map (plainPairIso T a b).hom ≫
      (plainPostfixAlgebra T a b).str =
        (postfixAlgebra T a b).str ≫ (plainPairIso T a b).hom :=
  (plainAlgebraIso T a b).hom.h

def plainPostfixInitial : IsInitial (plainPostfixAlgebra T a b) :=
  (postfixInitial T a b).ofIso (plainAlgebraIso T a b)

def plainWithParametersInitial (P : PredicateCategory T) :
    IsInitial (SyntaxPolynomial.algebraWithParameters a b (plainPostfixAlgebra T a b) P) :=
  (withParametersInitial T P a b).ofIso (parameterAlgebraIso a b P (plainAlgebraIso T a b))

/-- The named syntax bundle has precisely the plain parser predicates
as its two carriers, with base and every-parameter universal properties. -/
def plainCategoricalSyntax (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := SyntacticDecidableVariables.decidableVariables T V
  algebra := plainPostfixAlgebra T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  initial := plainPostfixInitial T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  stable P := plainWithParametersInitial T (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) P
  lists := SyntacticLists.stableListAlgebra T V

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
