/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionFrame


/-! # Statement checks in `V46MillerNamedProofImageNativeSubstitutionFrameChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open NamedProofImage.NativeSubstitution
variable {P : Uniform.Family} (R : Total.TotalCategory P)
variable (r : (Total.underlying (P := P)).obj R)
variable {A B : Over R × Over R} (f : A ⟶ B)
example (p : SyntaxPolynomial (Total.TotalCategory P)) (z : PointFrame.Data R r A p) :
    PointFrame.realize R r A p z ≫ (p.withParameters R).eval.map f=
      PointFrame.realize R r B p (PointFrame.mapData R r f p z) :=
  PointFrame.realize_natural R r f p z
example (n : ℕ) (c : Fin n → (PointFrame.source R r ⟶ A.1)) :
    PointFrame.mapData R r f (SyntaxPolynomial.power .term n) (PointFrame.powerData R r A n c)=
      PointFrame.powerData R r B n (fun i => c i ≫ f.1) :=
  PointFrame.powerData_natural R r f n c
example (τ : ℕ → Total.TotalCategory P) (d : ℕ) (k : Fin (d+1))
    (c : (Total.underlying (P := P)).obj (τ k.val))
    (children : Fin k.val → (PointFrame.source R r ⟶ A.1)) :
    PointFrame.mapData R r f (SyntaxPolynomial.constructors τ d)
      (PointFrame.arityData R r A τ d k c children)=
        PointFrame.arityData R r B τ d k c (fun i => children i ≫ f.1) :=
  PointFrame.arityData_natural R r f τ d k c children
example (X : Total.TotalCategory P) (x : (Total.underlying (P := P)).obj X) :
    (Total.underlying (P := P)).map (PointFrame.constant R r X x).left ⟨0,rfl⟩=
      NamedProofImage.Points.pairPoint r x := PointFrame.constant_point R r X x
