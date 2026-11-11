/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonSquares


/-! # Statement checks in `V46MillerCanonicalSyntaxComparisonSquaresChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation

section GenericPullback
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {X Y Z : C} {X' Y' Z' : D}

omit [FinitaryExtensive C] [FinitaryExtensive D] in
example (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') (k : E.functor.obj Z ≅ Z')
    (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z')
    (hf : E.functor.map f ≫ k.hom = i.hom ≫ f')
    (hg : E.functor.map g ≫ k.hom = j.hom ≫ g') :
    IsPullback (E.functor.map (pullback.fst f g) ≫ i.hom)
      (E.functor.map (pullback.snd f g) ≫ j.hom) f' g' :=
  comparedPullback E i j k f g f' g' hf hg
end GenericPullback

variable (a : Point) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (Uniform.Family.ofPoint a) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d
example : (E).functor.map (S₁).quantifierConstructor ≫ (formulaIso a V σ π d).hom =
    (SyntaxOptionTransport.productIso (E) (nameIso a V) (formulaIso a V σ π d)).hom ≫
      (S₂).quantifierConstructor := quantifier_comparison a V σ π d
example : (E).functor.map ((S₁).lists.membership (S₁).decidableVariables) ≫
      (DecidableVariables.Transport.booleanIso (E)).hom =
    (SyntaxOptionTransport.productIso (E) (nameIso a V) (listIso a V σ π d)).hom ≫
      (S₂).lists.membership (S₂).decidableVariables := membership_comparison a V σ π d
example : (E).functor.map (S₁).lists.algebra.cons ≫ (listIso a V σ π d).hom =
    (SyntaxOptionTransport.productIso (E) (nameIso a V) (listIso a V σ π d)).hom ≫
      (S₂).lists.algebra.cons := list_cons_comparison a V σ π d
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
