/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonBundle
public import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransport

/-! # The forward coefficient comparison for the explicit canonical push

This comparison starts with the supplied source signature. In particular it
does not replace that signature by the inverse image of its forward image.
The constructor equation is an algebra-morphism equation obtained from the
two initial algebras, rather than a condition on their underlying carriers.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation

section Forward
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : C) (σ π : ℕ → C) (d : ℕ)
local notation "p" => SyntaxPolynomial.termExpression V σ d
local notation "q" => SyntaxPolynomial.formulaExpression V π d
local notation "p'" => SyntaxPolynomial.termExpression (E.functor.obj V)
  (fun n => E.functor.obj (σ n)) d
local notation "q'" => SyntaxPolynomial.formulaExpression (E.functor.obj V)
  (fun n => E.functor.obj (π n)) d
local notation "K₀" => SyntaxPolynomial.jointFunctor p q
local notation "K₁" => SyntaxPolynomial.jointFunctor p' q'

def forwardJointIso : K₀ ⋙ (E.prod E).functor ≅ (E.prod E).functor ⋙ K₁ :=
  eqToIso (congrArg (fun K => K ⋙ (E.prod E).functor)
    (congrArg₂ SyntaxPolynomial.jointFunctor
      (SyntacticSyntax.mapCoefficients_id p).symm
      (SyntacticSyntax.mapCoefficients_id q).symm)) ≪≫
    SyntaxPolynomialTransport.jointIso (I := C) (C := C) (D := D)
      E (id : C → C) E.functor.obj (fun X : C => Iso.refl (E.functor.obj X)) (p) (q) ≪≫
    eqToIso (congrArg (fun K => (E.prod E).functor ⋙ K)
      (congrArg₂ SyntaxPolynomial.jointFunctor
        (SyntaxOperationsTransport.mapCoefficients_termExpression E.functor.obj V σ d)
        (SyntaxOperationsTransport.mapCoefficients_formulaExpression E.functor.obj V π d)))

variable (S₀ : CategoricalSyntax V σ π d)
variable (S₁ : CategoricalSyntax (E.functor.obj V)
  (fun n => E.functor.obj (σ n)) (fun n => E.functor.obj (π n)) d)

def forwardAlgebra : Endofunctor.Algebra K₁ :=
  AlgebraTransport.mappedAlgebra (E.prod E) (forwardJointIso E V σ π d) S₀.algebra

def forwardInitial : IsInitial (forwardAlgebra E V σ π d S₀) :=
  AlgebraTransport.initial (E.prod E) (forwardJointIso E V σ π d) S₀.algebra S₀.initial

/-- The source and target functor casts retain the mapped carrier pair;
their constructor compatibility is established below as a full algebra law. -/
theorem forwardAlgebra_carrier :
    (forwardAlgebra E V σ π d S₀).a=(E.prod E).functor.obj S₀.algebra.a := rfl

def forwardAlgebraIso : forwardAlgebra E V σ π d S₀ ≅ S₁.algebra :=
  (forwardInitial E V σ π d S₀).uniqueUpToIso S₁.initial

def forwardCarrierIso : (E.prod E).functor.obj S₀.algebra.a ≅ S₁.algebra.a :=
  (Endofunctor.Algebra.forget K₁).mapIso (forwardAlgebraIso E V σ π d S₀ S₁)

def forwardTermIso : E.functor.obj S₀.algebra.a.1 ≅ S₁.algebra.a.1 :=
  (CategoryTheory.Prod.fst D D).mapIso (forwardCarrierIso E V σ π d S₀ S₁)

def forwardFormulaIso : E.functor.obj S₀.algebra.a.2 ≅ S₁.algebra.a.2 :=
  (CategoryTheory.Prod.snd D D).mapIso (forwardCarrierIso E V σ π d S₀ S₁)

theorem forward_constructor :
    (E.prod E).functor.map S₀.algebra.str ≫ (forwardAlgebraIso E V σ π d S₀ S₁).hom.f =
      (forwardJointIso E V σ π d).hom.app S₀.algebra.a ≫
        (K₁).map (forwardAlgebraIso E V σ π d S₀ S₁).hom.f ≫ S₁.algebra.str := by
  let c := forwardAlgebraIso E V σ π d S₀ S₁
  have hc : (K₁).map c.hom.f≫S₁.algebra.str=
      (forwardAlgebra E V σ π d S₀).str≫c.hom.f := c.hom.h
  calc
    (E.prod E).functor.map S₀.algebra.str≫c.hom.f =
        ((forwardJointIso E V σ π d).app S₀.algebra.a).hom≫
          ((forwardAlgebra E V σ π d S₀).str≫c.hom.f) := by
      change _=(((forwardJointIso E V σ π d).app S₀.algebra.a).hom≫
        ((((forwardJointIso E V σ π d).app S₀.algebra.a).inv≫
          (E.prod E).functor.map S₀.algebra.str)≫c.hom.f))
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
    _=((forwardJointIso E V σ π d).app S₀.algebra.a).hom≫
        ((K₁).map c.hom.f≫S₁.algebra.str) := congrArg
      (fun k : (K₁).obj (forwardAlgebra E V σ π d S₀).a ⟶ S₁.algebra.a =>
        ((forwardJointIso E V σ π d).app S₀.algebra.a).hom≫k) hc.symm
    _=_ := rfl

theorem forward_term_constructor :
    E.functor.map S₀.algebra.str.1 ≫ (forwardTermIso E V σ π d S₀ S₁).hom =
      ((forwardJointIso E V σ π d).hom.app S₀.algebra.a).1 ≫
        (p').eval.map (forwardAlgebraIso E V σ π d S₀ S₁).hom.f ≫ S₁.algebra.str.1 :=
  congrArg Prod.fst (forward_constructor E V σ π d S₀ S₁)

theorem forward_formula_constructor :
    E.functor.map S₀.algebra.str.2 ≫ (forwardFormulaIso E V σ π d S₀ S₁).hom =
      ((forwardJointIso E V σ π d).hom.app S₀.algebra.a).2 ≫
        (q').eval.map (forwardAlgebraIso E V σ π d S₀ S₁).hom.f ≫ S₁.algebra.str.2 :=
  congrArg Prod.snd (forward_constructor E V σ π d S₀ S₁)

/-- The entire source fold is compared as an algebra morphism. -/
theorem forward_fold (B : Endofunctor.Algebra K₀) :
    (AlgebraTransport.functor (E.prod E) (forwardJointIso E V σ π d)).map
      (S₀.initial.to B) =
        (forwardInitial E V σ π d S₀).to
          (AlgebraTransport.mappedAlgebra (E.prod E) (forwardJointIso E V σ π d) B) :=
  (forwardInitial E V σ π d S₀).hom_ext _ _

end Forward

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SyntacticPredicates
variable (a : Point) (V : PredicateCategory 𝗣𝗔)
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "F" => Syntax.predicateFunctor (P)
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d

abbrev forwardConstructorAlgebraIso := forwardAlgebraIso (E) ((F).obj V)
  (fun n => (F).obj (σ n)) (fun n => (F).obj (π n)) d (S₁) (S₂)

abbrev constructorTermIso := forwardTermIso (E) ((F).obj V)
  (fun n => (F).obj (σ n)) (fun n => (F).obj (π n)) d (S₁) (S₂)

abbrev constructorFormulaIso := forwardFormulaIso (E) ((F).obj V)
  (fun n => (F).obj (σ n)) (fun n => (F).obj (π n)) d (S₁) (S₂)

abbrev constructor_comparison := forward_constructor (E) ((F).obj V)
  (fun n => (F).obj (σ n)) (fun n => (F).obj (π n)) d (S₁) (S₂)

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
