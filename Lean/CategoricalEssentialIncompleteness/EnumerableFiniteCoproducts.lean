/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableLimits
import CategoricalEssentialIncompleteness.EnumerableCoproducts

/-! # Finite coproducts of total recursive maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

theorem copair_total {X Y Z : Carrier} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : isTotal f) (hg : isTotal g) : isTotal (copair f g) := by
  change rst (copair f g)=𝟙 _
  rw [restrict_copair,hf,hg,coprod_id]

def totalCoproduct (X Y : Total) : Total := ⟨coproduct X.obj Y.obj⟩
def totalInl (X Y : Total) : X ⟶ totalCoproduct X Y :=
  ⟨inl X.obj Y.obj,RestrictionCoproducts.total_i0 _ _⟩
def totalInr (X Y : Total) : Y ⟶ totalCoproduct X Y :=
  ⟨inr X.obj Y.obj,RestrictionCoproducts.total_i1 _ _⟩

def totalCopair {X Y Z : Total} (f : X ⟶ Z) (g : Y ⟶ Z) : totalCoproduct X Y ⟶ Z :=
  ⟨copair f.hom g.hom,copair_total _ _ f.property g.property⟩

@[simp] theorem totalInl_copair {X Y Z : Total} (f : X ⟶ Z) (g : Y ⟶ Z) :
    totalInl X Y ≫ totalCopair f g=f := by
  apply WideSubcategory.hom_ext
  exact i0_copair f.hom g.hom

@[simp] theorem totalInr_copair {X Y Z : Total} (f : X ⟶ Z) (g : Y ⟶ Z) :
    totalInr X Y ≫ totalCopair f g=g := by
  apply WideSubcategory.hom_ext
  exact i1_copair f.hom g.hom

def coproductIsColimit (X Y : Total) :
    IsColimit (BinaryCofan.mk (totalInl X Y) (totalInr X Y)) :=
  BinaryCofan.isColimitMk (fun s => totalCopair s.inl s.inr)
    (fun _ => totalInl_copair _ _) (fun _ => totalInr_copair _ _) (by
      intro s m hm0 hm1
      apply WideSubcategory.hom_ext
      apply CategoryTheory.HasCoproducts.hom_ext
      · exact congrArg (fun k => k.hom) (hm0.trans (totalInl_copair s.inl s.inr).symm)
      · exact congrArg (fun k => k.hom) (hm1.trans (totalInr_copair s.inl s.inr).symm))

instance totalCoproductHasColimit (X Y : Total) : HasColimit (Limits.pair X Y) :=
  ⟨⟨_,coproductIsColimit X Y⟩⟩
instance : HasBinaryCoproducts Total := hasBinaryCoproducts_of_hasColimit_pair Total

def emptyCarrier : Carrier := ⟨∅,REPred.const False⟩

theorem empty_zero_eq_id : (0 : emptyCarrier ⟶ emptyCarrier)=𝟙 emptyCarrier := by
  apply val_injective
  apply PFun.ext
  intro x y
  change y ∈ (Part.none : Part ℕ) ↔ y ∈ supportIdentity ∅ x
  simp only [mem_supportIdentity,Set.mem_empty_iff_false,false_and]
  exact ⟨fun h => h.1,False.elim⟩

def initialArrow (X : Total) : (⟨emptyCarrier⟩ : Total) ⟶ X :=
  ⟨0,by change rst (0 : emptyCarrier ⟶ X.obj)=𝟙 _
        rw [RestrictionZero.restrict_zero,empty_zero_eq_id]⟩

def initialIsInitial : IsInitial (⟨emptyCarrier⟩ : Total) :=
  IsInitial.ofUniqueHom initialArrow (by
    intro X f
    apply WideSubcategory.hom_ext
    apply val_ext_on_source
    intro x hx
    exact hx.elim)

instance : HasInitial Total := initialIsInitial.hasInitial
instance : HasFiniteCoproducts Total := hasFiniteCoproducts_of_has_binary_and_initial

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
