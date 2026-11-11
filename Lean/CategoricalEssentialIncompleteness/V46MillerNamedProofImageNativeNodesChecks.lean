/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeNodes


/-! # Statement checks in `V46MillerNamedProofImageNativeNodesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeNodesChecks
open NamedProofImage NamedProofImage.NativeSubstitution NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P := P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "A" => SyntaxPolynomial.algebraWithParameters p q
  (CategoricalSyntax.algebra (NamedProofImage.syntaxData P σ π d)) R

example (r : (U).obj (R)) (t : Tm) :
    (U).map (A).str.1.left
      ((U).map (PointFrame.realize (R) r (A).a (p) (termNodeInput P σ π d r t)).left ⟨0,rfl⟩)=
        Points.pairPoint r (termPoint P σ π d t) :=
  term_node_realizes P σ π d r t

example (r : (U).obj (R)) (φ : Fm) :
    (U).map (A).str.2.left
      ((U).map (PointFrame.realize (R) r (A).a (q) (formulaNodeInput P σ π d r φ)).left ⟨0,rfl⟩)=
        Points.pairPoint r (formulaPoint P σ π d φ) :=
  formula_node_realizes P σ π d r φ

example (r : (U).obj (R)) (t : Tm) :
    PointFrame.realize (R) r (A).a (p) (termNodeInput P σ π d r t) ≫ (A).str.1=
      PointFrame.constant (R) r (S).algebra.a.1 (termPoint P σ π d t) :=
  term_node_realizes_hom P σ π d r t

example (r : (U).obj (R)) (φ : Fm) :
    PointFrame.realize (R) r (A).a (q) (formulaNodeInput P σ π d r φ) ≫ (A).str.2=
      PointFrame.constant (R) r (S).algebra.a.2 (formulaPoint P σ π d φ) :=
  formula_node_realizes_hom P σ π d r φ

example (R₁ X Y : Total.TotalCategory P) (r : (U).obj R₁)
    (e : SyntaxPolynomial (Total.TotalCategory P))
    (z : PointFrame.Data R₁ r (constantFamily R₁ X,constantFamily R₁ Y) e) :
    (PointFrame.realize R₁ r (constantFamily R₁ X,constantFamily R₁ Y) e z ≫
        SyntaxPolynomial.parameterComparison R₁ (X,Y) e).left ≫
          (prod.snd : R₁ ⨯ e.eval.obj (X,Y) ⟶ e.eval.obj (X,Y))=
      PointFrame.nodeBaseArrow R₁ r X Y e z :=
  PointFrame.realize_parameter_value R₁ r X Y e z

example (R₁ X Y : Total.TotalCategory P) (r : (U).obj R₁)
    (e : SyntaxPolynomial (Total.TotalCategory P))
    (z : PointFrame.Data R₁ r (constantFamily R₁ X,constantFamily R₁ Y) e) :
    ((U).map (PointFrame.nodeBaseArrow R₁ r X Y e z ≫
        (Syntax.Raw.baseComparison X Y e).inv) ⟨0,rfl⟩).val=
      PointFrame.nodeInputCode R₁ r X Y e z :=
  PointFrame.nodeBaseArrow_code R₁ r X Y e z

example (R₁ X Y : Total.TotalCategory P) (r : (U).obj R₁) (n : ℕ)
    (children : Fin n → (PointFrame.source R₁ r ⟶ constantFamily R₁ X)) :
    PointFrame.nodeInputCode R₁ r X Y (SyntaxPolynomial.power .term n)
        (PointFrame.powerData R₁ r (constantFamily R₁ X,constantFamily R₁ Y) n children)=
      childTuple n (fun i => ((U).map ((children i).left ≫ prod.snd) ⟨0,rfl⟩).val) :=
  PointFrame.nodeInputCode_powerData R₁ r X Y n children

example (R₁ X Y : Total.TotalCategory P) (r : (U).obj R₁)
    (τ : ℕ → Total.TotalCategory P) (b : ℕ) (k : Fin (b+1))
    (c : (U).obj (τ k.val))
    (children : Fin k.val → (PointFrame.source R₁ r ⟶ constantFamily R₁ X)) :
    PointFrame.nodeInputCode R₁ r X Y (SyntaxPolynomial.constructors τ b)
        (PointFrame.arityData R₁ r (constantFamily R₁ X,constantFamily R₁ Y) τ b k c children)=
      arityInput b k (Nat.pair c.val
        (childTuple k.val (fun i => ((U).map ((children i).left ≫ prod.snd) ⟨0,rfl⟩).val))) :=
  PointFrame.nodeInputCode_arityData R₁ r X Y τ b k c children

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeNodesChecks
