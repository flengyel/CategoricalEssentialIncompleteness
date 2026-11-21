/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawLeaves
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawProducts
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawSums

/-! # Raw-fiber comparison for every parameter slice

The recursive comparison uses constructed family-graph isomorphisms and
product/coproduct universal cones. Both recursive sorts and ordered children are
retained. Target families and their projection morphisms are arbitrary uniform slice
objects.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)

def comparison : (p : SyntaxPolynomial (Total.TotalCategory P)) →
    object R X Y p ≅ (p.withParameters R).eval.obj (X,Y)
  | .term => termIso R X Y
  | .formula => formulaIso R X Y
  | .coefficient C => coefficientIso R X Y C
  | .unit => unitIso R X Y
  | .product a b => productIso R X Y a b ≪≫ prod.mapIso (comparison a) (comparison b)
  | .sum a b => sumIso R X Y a b ≪≫ coprod.mapIso (comparison a) (comparison b)

/-- The action is the polynomial action under the constructed raw charts. Its numerical
child-map equations follow from the cone triangles. -/
def expressionFunctor (p : SyntaxPolynomial (Total.TotalCategory P)) : Over R × Over R ⥤ Over R where
  obj Z := object R Z.1 Z.2 p
  map {Z W} k := (comparison R Z.1 Z.2 p).hom ≫
    (p.withParameters R).eval.map k ≫ (comparison R W.1 W.2 p).inv
  map_id Z := by simp
  map_comp f g := by
    change (comparison R _ _ p).hom ≫ (p.withParameters R).eval.map (f ≫ g) ≫ _ = _
    rw [Functor.map_comp]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]

def comparisonIso (p : SyntaxPolynomial (Total.TotalCategory P)) :
    expressionFunctor R p ≅ (p.withParameters R).eval :=
  NatIso.ofComponents (fun Z => comparison R Z.1 Z.2 p) (by
    intro Z W k
    simp [expressionFunctor,Category.assoc])

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
