/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawProducts


/-! # Statement checks in `V46MillerSyntaxRawProductsChecks` -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks

variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)
variable (a b : SyntaxPolynomial (Total.TotalCategory P))

example {Z : Over R} (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b)
    (x u v : ℕ) (hu : u ∈ Total.val f.left.hom x) (hv : v ∈ Total.val g.left.hom x) :
    (Nat.unpair u).1=(Nat.unpair v).1 := outputs_same_parameter R X Y a b f g x u v hu hv

example {Z : Over R} (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) (x m : ℕ) :
    m ∈ Total.val (productLift R X Y a b f g).left.hom x ↔
      ∃ u,u ∈ Total.val f.left.hom x ∧ ∃ v,v ∈ Total.val g.left.hom x ∧
        Nat.pair (Nat.unpair u).1 (Nat.pair (Nat.unpair u).2 (Nat.unpair v).2)=m :=
  productLift_graph R X Y a b f g x m

example {Z : Over R} (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    productLift R X Y a b f g ≫ productFst R X Y a b=f := productLift_fst R X Y a b f g

example {Z : Over R} (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    productLift R X Y a b f g ≫ productSnd R X Y a b=g := productLift_snd R X Y a b f g

example {Z : Over R} (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b)
    (m : Z ⟶ object R X Y (.product a b))
    (hm₁ : m ≫ productFst R X Y a b=f) (hm₂ : m ≫ productSnd R X Y a b=g) :
    m=productLift R X Y a b f g := productLift_unique R X Y a b f g m hm₁ hm₂

example : IsLimit (BinaryFan.mk (productFst R X Y a b) (productSnd R X Y a b)) :=
  productIsLimit R X Y a b

example : object R X Y (.product a b) ≅ object R X Y a ⨯ object R X Y b :=
  productIso R X Y a b

example : (productIso R X Y a b).hom ≫
    (prod.fst : object R X Y a ⨯ object R X Y b ⟶ object R X Y a)=productFst R X Y a b :=
  productIso_fst R X Y a b

example : (productIso R X Y a b).hom ≫
    (prod.snd : object R X Y a ⨯ object R X Y b ⟶ object R X Y b)=productSnd R X Y a b :=
  productIso_snd R X Y a b

example : (productIso R X Y a b).inv=
    productLift R X Y a b (prod.fst : object R X Y a ⨯ object R X Y b ⟶ object R X Y a)
      (prod.snd : object R X Y a ⨯ object R X Y b ⟶ object R X Y b) :=
  productIso_inv R X Y a b

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
