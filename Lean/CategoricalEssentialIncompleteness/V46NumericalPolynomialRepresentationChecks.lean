/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalPolynomialRepresentation


/-! # Exact polynomial-input codes under the arithmetic numerical comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists SyntacticSyntax
open NumericalPolynomialRepresentation

example {I : Type w} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
    (c : ∀ i, K.obj (s i) ≅ E.functor.obj (t i))
    (X Y : PredicateCategory 𝗣𝗔) (X' Y' : PredicateCategory 𝗧𝗔)
    (bX : K.obj X ≅ E.functor.obj X') (bY : K.obj Y ≅ E.functor.obj Y')
    (hX : ∀ z : Obj 𝗣𝗔 ℕ X,
      ((NumericalCoordinates.predicatePresentationIso X').hom.toFun (bX.hom.toFun z)).val = z.val)
    (hY : ∀ z : Obj 𝗣𝗔 ℕ Y,
      ((NumericalCoordinates.predicatePresentationIso Y').hom.toFun (bY.hom.toFun z)).val = z.val)
    (hC : ∀ i, ∀ z : Obj 𝗣𝗔 ℕ (s i),
      ((NumericalCoordinates.predicatePresentationIso (t i)).hom.toFun ((c i).hom.toFun z)).val = z.val)
    (p : SyntaxPolynomial I) (u : ℕ)
    (z : Obj 𝗣𝗔 ℕ ((p.mapCoefficients s).eval.obj (X,Y))) :
    (baseRepresentation 𝗣𝗔 X Y (p.mapCoefficients s)).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 X' Y' (p.mapCoefficients t)).val.Evalb
        ![u,(point s t c X Y X' Y' bX bY p z).val] :=
  baseRepresentation_iff s t c X Y X' Y' bX bY hX hY hC p u z

example {I : Type w} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
    (c : ∀ i, K.obj (s i) ≅ E.functor.obj (t i))
    (X Y : PredicateCategory 𝗣𝗔) (X' Y' : PredicateCategory 𝗧𝗔)
    (bX : K.obj X ≅ E.functor.obj X') (bY : K.obj Y ≅ E.functor.obj Y')
    (hX : ∀ z : Obj 𝗣𝗔 ℕ X,
      ((NumericalCoordinates.predicatePresentationIso X').hom.toFun (bX.hom.toFun z)).val = z.val)
    (hY : ∀ z : Obj 𝗣𝗔 ℕ Y,
      ((NumericalCoordinates.predicatePresentationIso Y').hom.toFun (bY.hom.toFun z)).val = z.val)
    (hC : ∀ i, ∀ z : Obj 𝗣𝗔 ℕ (s i),
      ((NumericalCoordinates.predicatePresentationIso (t i)).hom.toFun ((c i).hom.toFun z)).val = z.val)
    (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (u : ℕ) (z : Obj 𝗣𝗔 ℕ (p₀.eval.obj (X,Y))) :
    (baseRepresentation 𝗣𝗔 X Y p₀).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 X' Y' p₁).val.Evalb
        ![u,(normalizedPoint s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁ z).val] :=
  normalized_baseRepresentation_iff s t c X Y X' Y' bX bY hX hY hC p p₀ p₁ h₀ h₁ u z
