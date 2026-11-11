/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsRawSquares
public import CategoricalEssentialIncompleteness.V46CategoricalLists

/-! # Direct list initiality in every uniform parameter slice

The target algebra is arbitrary. Its nil value is obtained by its actual
uniform morphism, and its cons operation acts only on its prescribed
fiber. The proof of uniqueness uses every candidate algebra morphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
variable {P : Uniform.Family} (R : Total.TotalCategory P) (V : Total.Carrier P)

abbrev consPolynomial : SyntaxPolynomial (Total.TotalCategory P) :=
  .product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term

def parameterAlgebra : ListAlgebra (constantFamily R (⟨V⟩ : Total.TotalCategory P)) where
  carrier := family R V
  nil := (Syntax.Raw.comparison R (family R V) (family R V) .unit).inv ≫ rawNil R V
  cons := (Syntax.Raw.comparison R (family R V) (family R V) (consPolynomial V)).inv ≫ rawCons R V

def targetView (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    ListAlgebra (constantFamily R (⟨V⟩ : Total.TotalCategory P)) where
  carrier := B.a
  nil := coprod.inl ≫ B.str
  cons := coprod.inr ≫ B.str

def targetNil (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    Syntax.Raw.object R B.a B.a .unit ⟶ B.a :=
  (Syntax.Raw.comparison R B.a B.a .unit).hom ≫ (targetView R V B).nil

def targetCons (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    Syntax.Raw.object R B.a B.a (consPolynomial V) ⟶ B.a :=
  (Syntax.Raw.comparison R B.a B.a (consPolynomial V)).hom ≫ (targetView R V B).cons

def parameterFold (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    (parameterAlgebra R V).carrier ⟶ B.a :=
  fold V (targetNil R V B) (targetCons R V B)

private theorem unitChart_eq (X Y : Over R) :
    (Syntax.Raw.comparison R X X .unit).hom=(Syntax.Raw.comparison R Y Y .unit).hom :=
  (terminalIsTerminal (C := Over R)).hom_ext _ _

theorem parameterFold_nil
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    (parameterAlgebra R V).nil ≫ parameterFold R V B=(targetView R V B).nil := by
  apply (cancel_epi (Syntax.Raw.comparison R (family R V) (family R V) .unit).hom).mp
  simp only [parameterAlgebra,parameterFold,Category.assoc,Iso.hom_inv_id_assoc]
  rw [fold_rawNil]
  exact congrArg (fun k => k ≫ (targetView R V B).nil) (unitChart_eq R (family R V) B.a).symm

theorem parameterFold_cons
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    (parameterAlgebra R V).cons ≫ parameterFold R V B=
      prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) (parameterFold R V B) ≫
        (targetView R V B).cons := by
  apply (cancel_epi (Syntax.Raw.comparison R (family R V) (family R V) (consPolynomial V)).hom).mp
  simp only [parameterAlgebra,parameterFold,Category.assoc,Iso.hom_inv_id_assoc]
  rw [fold_rawCons]
  have h := Syntax.Raw.rawAction_comparison R (family R V) (family R V) B.a B.a
    (parameterFold R V B) (parameterFold R V B) (consPolynomial V)
  change Syntax.Raw.rawAction R (family R V) (family R V) B.a B.a
      (parameterFold R V B) (parameterFold R V B) (consPolynomial V) ≫
      (Syntax.Raw.comparison R B.a B.a (consPolynomial V)).hom =
    (Syntax.Raw.comparison R (family R V) (family R V) (consPolynomial V)).hom ≫
      prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) (parameterFold R V B) at h
  simpa only [targetCons,parameterFold,targetView,consPolynomial,Category.assoc] using
    congrArg (fun k => k ≫ (targetView R V B).cons) h

def parameterFoldHom
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P)))) :
    (parameterAlgebra R V).asAlgebra ⟶ B where
  f := parameterFold R V B
  h := by
    change coprod.map (𝟙 _) (prod.map (𝟙 _) (parameterFold R V B)) ≫ B.str=
      coprod.desc (parameterAlgebra R V).nil (parameterAlgebra R V).cons ≫ parameterFold R V B
    apply coprod.hom_ext
    · simp only [← Category.assoc,coprod.inl_map,Category.id_comp,coprod.inl_desc]
      exact (parameterFold_nil R V B).symm
    · simp only [← Category.assoc,coprod.inr_map,coprod.inr_desc]
      rw [Category.assoc]
      exact (parameterFold_cons R V B).symm

theorem candidate_nil
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))))
    (f : (parameterAlgebra R V).asAlgebra ⟶ B) :
    (parameterAlgebra R V).nil ≫ f.f=(targetView R V B).nil := by
  have h := congrArg (fun k => coprod.inl ≫ k) f.h
  change coprod.inl ≫ (coprod.map (𝟙 _) (prod.map (𝟙 _) f.f) ≫ B.str)=
    coprod.inl ≫ (coprod.desc (parameterAlgebra R V).nil (parameterAlgebra R V).cons ≫ f.f) at h
  simpa only [← Category.assoc,coprod.inl_map,Category.id_comp,coprod.inl_desc,targetView] using h.symm

theorem candidate_cons
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))))
    (f : (parameterAlgebra R V).asAlgebra ⟶ B) :
    (parameterAlgebra R V).cons ≫ f.f=
      prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) f.f ≫ (targetView R V B).cons := by
  have h := congrArg (fun k => coprod.inr ≫ k) f.h
  change coprod.inr ≫ (coprod.map (𝟙 _) (prod.map (𝟙 _) f.f) ≫ B.str)=
    coprod.inr ≫ (coprod.desc (parameterAlgebra R V).nil (parameterAlgebra R V).cons ≫ f.f) at h
  simp only [← Category.assoc,coprod.inr_map,coprod.inr_desc] at h
  simpa only [Category.assoc,targetView] using h.symm

theorem candidate_rawNil
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))))
    (f : (parameterAlgebra R V).asAlgebra ⟶ B) :
    rawNil R V ≫ f.f=targetNil R V B := by
  have h := congrArg (fun k =>
    (Syntax.Raw.comparison R (family R V) (family R V) .unit).hom ≫ k) (candidate_nil R V B f)
  simp only [parameterAlgebra,Category.assoc,Iso.hom_inv_id_assoc] at h
  exact h.trans (congrArg (fun k => k ≫ (targetView R V B).nil)
    (unitChart_eq R (family R V) B.a))

theorem candidate_rawCons
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))))
    (f : (parameterAlgebra R V).asAlgebra ⟶ B) :
    rawCons R V ≫ f.f=Syntax.Raw.rawAction R (family R V) (family R V) B.a B.a f.f f.f
      (consPolynomial V) ≫ targetCons R V B := by
  have h := congrArg (fun k =>
    (Syntax.Raw.comparison R (family R V) (family R V) (consPolynomial V)).hom ≫ k)
      (candidate_cons R V B f)
  simp only [parameterAlgebra,Category.assoc,Iso.hom_inv_id_assoc] at h
  have ha := Syntax.Raw.rawAction_comparison R (family R V) (family R V) B.a B.a f.f f.f (consPolynomial V)
  change _ = (Syntax.Raw.comparison R (family R V) (family R V) (consPolynomial V)).hom ≫
    prod.map (𝟙 (constantFamily R (⟨V⟩ : Total.TotalCategory P))) f.f at ha
  exact h.trans (by simpa only [targetCons,Category.assoc] using
    (congrArg (fun k => k ≫ (targetView R V B).cons) ha).symm)

theorem parameterFoldHom_unique
    (B : Endofunctor.Algebra (listFunctor (constantFamily R (⟨V⟩ : Total.TotalCategory P))))
    (f : (parameterAlgebra R V).asAlgebra ⟶ B) : f=parameterFoldHom R V B := by
  apply Endofunctor.Algebra.Hom.ext
  exact fold_unique V (targetNil R V B) (targetCons R V B) f.f
    ((rawNil_square_iff V f.f (targetNil R V B)).mp (candidate_rawNil R V B f))
    ((rawCons_square_iff V f.f (targetCons R V B)).mp (candidate_rawCons R V B f))

/-- Every parameter and every algebra on arbitrary families over it. -/
def parameterInitial : IsInitial (parameterAlgebra R V).asAlgebra :=
  IsInitial.ofUniqueHom (parameterFoldHom R V) (parameterFoldHom_unique R V)

end CategoricalEssentialIncompleteness.V46.Miller.Lists
