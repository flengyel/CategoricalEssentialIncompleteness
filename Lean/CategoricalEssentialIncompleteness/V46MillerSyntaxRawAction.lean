/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawComparison

/-! # Raw polynomial action on arbitrary parameter-slice morphisms

The action is constructed recursively from the raw universal products and sums. Its
naturality comparison with the chosen polynomial action is proved from the cone
triangles, with no child-action comparison premise.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P:Uniform.Family} (R:Total.TotalCategory P) (X Y X' Y':Over R)

def rawAction (f:X⟶X') (g:Y⟶Y') : (p:SyntaxPolynomial (Total.TotalCategory P)) →
    object R X Y p ⟶ object R X' Y' p
  | .term => (termIso R X Y).hom ≫ f ≫ (termIso R X' Y').inv
  | .formula => (formulaIso R X Y).hom ≫ g ≫ (formulaIso R X' Y').inv
  | .coefficient _ => 𝟙 _
  | .unit => 𝟙 _
  | .product a b => productLift R X' Y' a b
      (productFst R X Y a b ≫ rawAction f g a)
      (productSnd R X Y a b ≫ rawAction f g b)
  | .sum a b => sumCopair R X Y a b
      (rawAction f g a ≫ sumInl R X' Y' a b)
      (rawAction f g b ≫ sumInr R X' Y' a b)

theorem comparison_product_fst (a b:SyntaxPolynomial (Total.TotalCategory P)) :
    (comparison R X Y (.product a b)).hom ≫ prod.fst=
      productFst R X Y a b ≫ (comparison R X Y a).hom := by
  change ((productIso R X Y a b).hom ≫
    prod.map (comparison R X Y a).hom (comparison R X Y b).hom) ≫ prod.fst=_
  rw [Category.assoc,prod.map_fst,← Category.assoc,productIso_fst]

theorem comparison_product_snd (a b:SyntaxPolynomial (Total.TotalCategory P)) :
    (comparison R X Y (.product a b)).hom ≫ prod.snd=
      productSnd R X Y a b ≫ (comparison R X Y b).hom := by
  change ((productIso R X Y a b).hom ≫
    prod.map (comparison R X Y a).hom (comparison R X Y b).hom) ≫ prod.snd=_
  rw [Category.assoc,prod.map_snd,← Category.assoc,productIso_snd]

theorem comparison_sum_inl (a b:SyntaxPolynomial (Total.TotalCategory P)) :
    sumInl R X Y a b ≫ (comparison R X Y (.sum a b)).hom=
      (comparison R X Y a).hom ≫ coprod.inl := by
  change sumInl R X Y a b ≫ ((sumIso R X Y a b).hom ≫
    coprod.map (comparison R X Y a).hom (comparison R X Y b).hom)=_
  rw [← Category.assoc,sumIso_inl,coprod.inl_map]

theorem comparison_sum_inr (a b:SyntaxPolynomial (Total.TotalCategory P)) :
    sumInr R X Y a b ≫ (comparison R X Y (.sum a b)).hom=
      (comparison R X Y b).hom ≫ coprod.inr := by
  change sumInr R X Y a b ≫ ((sumIso R X Y a b).hom ≫
    coprod.map (comparison R X Y a).hom (comparison R X Y b).hom)=_
  rw [← Category.assoc,sumIso_inr,coprod.inr_map]

private theorem rawAction_comparison_product (f:X⟶X') (g:Y⟶Y') (a b:SyntaxPolynomial (Total.TotalCategory P))
    (ia:rawAction R X Y X' Y' f g a ≫ (comparison R X' Y' a).hom=
      (comparison R X Y a).hom ≫ (a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))
    (ib:rawAction R X Y X' Y' f g b ≫ (comparison R X' Y' b).hom=
      (comparison R X Y b).hom ≫ (b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) :
    rawAction R X Y X' Y' f g (.product a b) ≫ (comparison R X' Y' (.product a b)).hom=
      (comparison R X Y (.product a b)).hom ≫ ((SyntaxPolynomial.product a b).withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)) := by
  apply prod.hom_ext
  · calc
      (rawAction R X Y X' Y' f g (.product a b) ≫
          (comparison R X' Y' (.product a b)).hom) ≫ prod.fst =
          (productFst R X Y a b ≫ rawAction R X Y X' Y' f g a) ≫
            (comparison R X' Y' a).hom := by
        rw [Category.assoc,comparison_product_fst,← Category.assoc]
        exact congrArg (fun h => h ≫ (comparison R X' Y' a).hom)
          (productLift_fst R X' Y' a b _ _)
      _ = productFst R X Y a b ≫
          ((comparison R X Y a).hom ≫ (a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) := by
        rw [Category.assoc,ia]
      _ = ((comparison R X Y (.product a b)).hom ≫
          ((SyntaxPolynomial.product a b).withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) ≫ prod.fst := by
        change _=((comparison R X Y (.product a b)).hom ≫
          prod.map ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))) ≫ prod.fst
        rw [Category.assoc,prod.map_fst]
        simpa only [Category.assoc] using
          (congrArg (fun (k:object R X Y (.product a b) ⟶ (a.withParameters R).eval.obj (X,Y)) =>
            k ≫ (a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))
              (comparison_product_fst R X Y a b)).symm
  · calc
      (rawAction R X Y X' Y' f g (.product a b) ≫
          (comparison R X' Y' (.product a b)).hom) ≫ prod.snd =
          (productSnd R X Y a b ≫ rawAction R X Y X' Y' f g b) ≫
            (comparison R X' Y' b).hom := by
        rw [Category.assoc,comparison_product_snd,← Category.assoc]
        exact congrArg (fun h => h ≫ (comparison R X' Y' b).hom)
          (productLift_snd R X' Y' a b _ _)
      _ = productSnd R X Y a b ≫
          ((comparison R X Y b).hom ≫ (b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) := by
        rw [Category.assoc,ib]
      _ = ((comparison R X Y (.product a b)).hom ≫
          ((SyntaxPolynomial.product a b).withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) ≫ prod.snd := by
        change _=((comparison R X Y (.product a b)).hom ≫
          prod.map ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))) ≫ prod.snd
        rw [Category.assoc,prod.map_snd]
        simpa only [Category.assoc] using
          (congrArg (fun (k:object R X Y (.product a b) ⟶ (b.withParameters R).eval.obj (X,Y)) =>
            k ≫ (b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))
              (comparison_product_snd R X Y a b)).symm

private theorem rawAction_comparison_sum (f:X⟶X') (g:Y⟶Y') (a b:SyntaxPolynomial (Total.TotalCategory P))
    (ia:rawAction R X Y X' Y' f g a ≫ (comparison R X' Y' a).hom=
      (comparison R X Y a).hom ≫ (a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))
    (ib:rawAction R X Y X' Y' f g b ≫ (comparison R X' Y' b).hom=
      (comparison R X Y b).hom ≫ (b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) :
    rawAction R X Y X' Y' f g (.sum a b) ≫ (comparison R X' Y' (.sum a b)).hom=
      (comparison R X Y (.sum a b)).hom ≫ ((SyntaxPolynomial.sum a b).withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)) := by
  apply sum_hom_ext R X Y a b
  · calc
      sumInl R X Y a b ≫ (rawAction R X Y X' Y' f g (.sum a b) ≫
          (comparison R X' Y' (.sum a b)).hom) =
          rawAction R X Y X' Y' f g a ≫ ((comparison R X' Y' a).hom ≫ coprod.inl) := by
        rw [← Category.assoc]
        change (sumInl R X Y a b ≫ sumCopair R X Y a b _ _) ≫ _=_
        rw [sumInl_copair,Category.assoc,comparison_sum_inl]
      _ = (comparison R X Y a).hom ≫ ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)) ≫ coprod.inl) := by
        rw [← Category.assoc,ia,Category.assoc]
      _ = sumInl R X Y a b ≫ ((comparison R X Y (.sum a b)).hom ≫
          ((SyntaxPolynomial.sum a b).withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) := by
        change _=sumInl R X Y a b ≫ ((comparison R X Y (.sum a b)).hom ≫
          coprod.map ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))))
        simpa only [Category.assoc,coprod.inl_map] using
      (congrArg (fun (k:object R X Y a ⟶
        ((a.withParameters R).eval.obj (X,Y) ⨿ (b.withParameters R).eval.obj (X,Y))) =>
          k ≫ coprod.map
            ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))
            ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))))
          (comparison_sum_inl R X Y a b)).symm
  · calc
      sumInr R X Y a b ≫ (rawAction R X Y X' Y' f g (.sum a b) ≫
          (comparison R X' Y' (.sum a b)).hom) =
          rawAction R X Y X' Y' f g b ≫ ((comparison R X' Y' b).hom ≫ coprod.inr) := by
        rw [← Category.assoc]
        change (sumInr R X Y a b ≫ sumCopair R X Y a b _ _) ≫ _=_
        rw [sumInr_copair,Category.assoc,comparison_sum_inr]
      _ = (comparison R X Y b).hom ≫ ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)) ≫ coprod.inr) := by
        rw [← Category.assoc,ib,Category.assoc]
      _ = sumInr R X Y a b ≫ ((comparison R X Y (.sum a b)).hom ≫
          ((SyntaxPolynomial.sum a b).withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) := by
        change _=sumInr R X Y a b ≫ ((comparison R X Y (.sum a b)).hom ≫
          coprod.map ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))) ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))))
        simpa only [Category.assoc,coprod.inr_map] using
      (congrArg (fun (k:object R X Y b ⟶
        ((a.withParameters R).eval.obj (X,Y) ⨿ (b.withParameters R).eval.obj (X,Y))) =>
          k ≫ coprod.map
            ((a.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)))
            ((b.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g))))
          (comparison_sum_inr R X Y a b)).symm

theorem rawAction_comparison (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) :
    rawAction R X Y X' Y' f g p ≫ (comparison R X' Y' p).hom=
      (comparison R X Y p).hom ≫ (p.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)) := by
  induction p with
  | term => simp only [rawAction,comparison,SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,CategoryTheory.Prod.fst,
      Category.assoc,Iso.inv_hom_id,Category.comp_id]
  | formula => simp only [rawAction,comparison,SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,CategoryTheory.Prod.snd,
      Category.assoc,Iso.inv_hom_id,Category.comp_id]
  | coefficient C =>
    change (𝟙 _) ≫ (coefficientIso R X' Y' C).hom=(coefficientIso R X Y C).hom ≫ 𝟙 _
    rw [Category.id_comp,Category.comp_id]
    rfl
  | unit =>
    change (𝟙 _) ≫ (unitIso R X' Y').hom=(unitIso R X Y).hom ≫ 𝟙 _
    rw [Category.id_comp,Category.comp_id]
    rfl
  | product a b ia ib => exact rawAction_comparison_product R X Y X' Y' f g a b ia ib
  | sum a b ia ib => exact rawAction_comparison_sum R X Y X' Y' f g a b ia ib

theorem rawAction_eq_transported (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) :
    rawAction R X Y X' Y' f g p=(comparison R X Y p).hom ≫
      (p.withParameters R).eval.map (show (X,Y) ⟶ (X',Y') from (f,g)) ≫ (comparison R X' Y' p).inv := by
  apply (cancel_mono (comparison R X' Y' p).hom).mp
  rw [rawAction_comparison,Category.assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]

theorem rawAction_id (p:SyntaxPolynomial (Total.TotalCategory P)) :
    rawAction R X Y X Y (𝟙 X) (𝟙 Y) p=𝟙 _ := by
  rw [rawAction_eq_transported]
  change (comparison R X Y p).hom ≫ (p.withParameters R).eval.map (𝟙 (X,Y)) ≫
    (comparison R X Y p).inv=𝟙 _
  rw [CategoryTheory.Functor.map_id,Category.id_comp,Iso.hom_inv_id]

theorem rawAction_comp {X'' Y'':Over R} (f:X⟶X') (g:Y⟶Y') (f':X'⟶X'') (g':Y'⟶Y'')
    (p:SyntaxPolynomial (Total.TotalCategory P)) :
    rawAction R X Y X'' Y'' (f≫f') (g≫g') p=
      rawAction R X Y X' Y' f g p ≫ rawAction R X' Y' X'' Y'' f' g' p := by
  rw [rawAction_eq_transported,rawAction_eq_transported,rawAction_eq_transported]
  change (comparison R X Y p).hom ≫
    (p.withParameters R).eval.map ((show (X,Y) ⟶ (X',Y') from (f,g)) ≫
      (show (X',Y') ⟶ (X'',Y'') from (f',g'))) ≫ (comparison R X'' Y'' p).inv = _
  rw [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
