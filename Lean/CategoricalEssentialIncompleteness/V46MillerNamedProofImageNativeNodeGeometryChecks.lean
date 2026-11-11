/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeNodeGeometry


/-! # Statement checks in `V46MillerNamedProofImageNativeNodeGeometryChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open NamedProofImage.NativeSubstitution
variable {P : Uniform.Family} (R : Total.TotalCategory P)
variable (r : (Total.underlying (P := P)).obj R) (X Y : Total.TotalCategory P)
example (p : SyntaxPolynomial (Total.TotalCategory P))
    (z : PointFrame.Data R r (constantFamily R X,constantFamily R Y) p) :
    (PointFrame.realize R r (constantFamily R X,constantFamily R Y) p z ≫
        SyntaxPolynomial.parameterComparison R (X,Y) p).left ≫
          (prod.snd : R ⨯ p.eval.obj (X,Y) ⟶ p.eval.obj (X,Y))=
      PointFrame.nodeBaseArrow R r X Y p z :=
  PointFrame.realize_parameter_value R r X Y p z
example (p : SyntaxPolynomial (Total.TotalCategory P))
    (z : PointFrame.Data R r (constantFamily R X,constantFamily R Y) p) :
    ((Total.underlying (P := P)).map (PointFrame.nodeBaseArrow R r X Y p z ≫
        (Syntax.Raw.baseComparison X Y p).inv) ⟨0,rfl⟩).val=
      PointFrame.nodeInputCode R r X Y p z := PointFrame.nodeBaseArrow_code R r X Y p z
example (τ : ℕ → Total.TotalCategory P) (d : ℕ) (k : Fin (d+1))
    (c : (Total.underlying (P := P)).obj (τ k.val))
    (f : Fin k.val → (PointFrame.source R r ⟶ constantFamily R X)) :
    PointFrame.nodeInputCode R r X Y (SyntaxPolynomial.constructors τ d)
      (PointFrame.arityData R r (constantFamily R X,constantFamily R Y) τ d k c f)=
      NamedPostfixEncoding.arityInput d k (Nat.pair c.val
        (NamedPostfixEncoding.childTuple k.val
          (fun i => ((Total.underlying (P := P)).map ((f i).left ≫ prod.snd) ⟨0,rfl⟩).val))) :=
  PointFrame.nodeInputCode_arityData R r X Y τ d k c f
