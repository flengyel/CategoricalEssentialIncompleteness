/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeStandard


/-! # Finite standard-model inputs and their parameterized points -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeStandardChecks
open NamedProofImage.NativeSubstitution
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ

example (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (SyntacticSyntax.baseRepresentation 𝗣𝗔 X.1 X.2 p).val.Evalb
      ![Standard.rawCode X p z,(Standard.realize X p z).val] := Standard.rawCode_represents X p z

example (R : PredicateCategory 𝗣𝗔) (r : (N).obj R) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (N).map ((p.withParameters R).eval.obj (constantFamily R X.1,constantFamily R X.2)).hom
      (Standard.liftData R r X p z).val=r := Standard.liftData_parameter R r X p z

example (R : PredicateCategory 𝗣𝗔) (r : (N).obj R) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (N).map (SyntacticSyntax.parameterValueMap 𝗣𝗔 R X.1 X.2 p) (Standard.liftData R r X p z).val=
      Standard.realize X p z := Standard.liftData_value R r X p z

example (R : PredicateCategory 𝗣𝗔) (r : (N).obj R) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (N).map (SyntaxPolynomial.parameterComparison R X p).left (Standard.liftData R r X p z).val=
      SyntacticLists.pairPoint 𝗣𝗔 ℕ r (Standard.realize X p z) := Standard.liftData_comparison R r X p z

example (R : PredicateCategory 𝗣𝗔) (r : (N).obj R) (X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (f : (constantFamily R X.1,constantFamily R X.2) ⟶ (constantFamily R Y.1,constantFamily R Y.2))
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (z : Standard.Data X p) :
    (N).map ((p.withParameters R).eval.map f).left (Standard.liftData R r X p z).val=
      (Standard.liftData R r Y p (Standard.mapData (Standard.leafValue r f.1) (Standard.leafValue r f.2) p z)).val :=
  Standard.liftData_natural r f p z

example (R : PredicateCategory 𝗣𝗔) (r : (N).obj R) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (W : PredicateCategory 𝗣𝗔)
    (v : R ⨯ p.eval.obj X ⟶ W) (z : Standard.Data X p) :
    (N).map (prod.snd : R ⨯ W ⟶ W)
      ((N).map (SyntaxPolynomial.parameterComparison R X p ≫ parameterHom v).left
        (Standard.liftData R r X p z).val)=
      (N).map v (SyntacticLists.pairPoint 𝗣𝗔 ℕ r (Standard.realize X p z)) := Standard.operation_value R r X p v z

example (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) (n : ℕ) (children : Fin n → (N).obj X.1) :
    Standard.rawCode X (SyntaxPolynomial.power .term n) (Standard.powerData X n children)=
      NamedPostfixEncoding.childTuple n (fun i => (children i).val) := Standard.powerData_rawCode X n children

example (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) (τ : ℕ → PredicateCategory 𝗣𝗔)
    (d : ℕ) (k : Fin (d+1)) (c : (N).obj (τ k.val)) (children : Fin k.val → (N).obj X.1) :
    Standard.rawCode X (SyntaxPolynomial.constructors τ d) (Standard.arityData X τ d k c children)=
      NamedPostfixEncoding.arityInput d k
        (Arithmetic.pair c.val (NamedPostfixEncoding.childTuple k.val (fun i => (children i).val))) :=
  Standard.arityData_rawCode X τ d k c children

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeStandardChecks
