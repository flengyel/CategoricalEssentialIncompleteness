/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsRawAlgebra

/-! # Literal constructor squares for every actual slice morphism

These equivalences connect the scalar nil/adjoin laws to the actual
polynomial action, using its proved child graph. The recursive source
leaf is the complete family code pair(r,list).
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X : Over R} (V : Total.Carrier P)
variable (f : family R V ⟶ X)
variable (h0 : Syntax.Raw.object R X X .unit ⟶ X)
variable (hc : Syntax.Raw.object R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ X)

theorem rawNil_then_graph (r value : ℕ) (hr : r ∈ R.obj.support) :
    value ∈ Total.val ((rawNil R V) ≫ f).left.hom (Nat.pair r 0) ↔
      value ∈ Total.val f.left.hom (Nat.pair r 0) := by
  change value ∈ Total.val ((rawNil R V).left.hom ≫ f.left.hom) (Nat.pair r 0) ↔ _
  rw [Total.val_comp]
  simp only [Part.mem_bind_iff,rawNil_graph,hr,true_and,exists_eq_left]

theorem rawCons_then_graph (r head tail value : ℕ)
    (hr : r ∈ R.obj.support) (hh : head ∈ V.support) (ht : tail ∈ (carrier V).support) :
    value ∈ Total.val ((rawCons R V) ≫ f).left.hom (Nat.pair r (Nat.pair head (Nat.pair r tail))) ↔
      value ∈ Total.val f.left.hom (Nat.pair r (adjoin head tail)) := by
  change value ∈ Total.val ((rawCons R V).left.hom ≫ f.left.hom)
    (Nat.pair r (Nat.pair head (Nat.pair r tail))) ↔ _
  rw [Total.val_comp]
  simp only [Part.mem_bind_iff,rawCons_graph,hr,hh,ht,true_and,exists_eq_left]

theorem actionCons_then_graph (r head tail value : ℕ)
    (hr : r ∈ R.obj.support) (hh : head ∈ V.support) (ht : tail ∈ (carrier V).support) :
    value ∈ Total.val
      ((Syntax.Raw.rawAction R (family R V) (family R V) X X f f
        (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term)) ≫ hc).left.hom
      (Nat.pair r (Nat.pair head (Nat.pair r tail))) ↔
        ∃ w,w ∈ Total.val f.left.hom (Nat.pair r tail) ∧ value ∈ Syntax.Raw.operation hc (r,Nat.pair head w) := by
  change value ∈ Total.val ((Syntax.Raw.rawAction R (family R V) (family R V) X X f f
    (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term)).left.hom ≫ hc.left.hom)
      (Nat.pair r (Nat.pair head (Nat.pair r tail))) ↔ _
  rw [Total.val_comp,Part.mem_bind_iff]
  constructor
  · rintro ⟨m,hm,hvalue⟩
    have ha := (Syntax.Raw.rawAction_graph R (family R V) (family R V) X X f f
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term)
      r (Nat.pair head (Nat.pair r tail)) (Nat.unpair m).1 (Nat.unpair m).2).mp
      (by simpa only [Nat.pair_unpair] using hm)
    have hp : (Nat.unpair m).1=r := ha.1
    have hl : (Nat.unpair (Nat.unpair m).2).1=head := by
      simpa only [Nat.unpair_pair] using ha.2.1.2.2
    have hw : (Nat.unpair (Nat.unpair m).2).2 ∈ Total.val f.left.hom (Nat.pair r tail) := by
      simpa only [Nat.unpair_pair] using ha.2.2.2
    refine ⟨(Nat.unpair (Nat.unpair m).2).2,hw,?_⟩
    have he : m=Nat.pair r (Nat.pair head (Nat.unpair (Nat.unpair m).2).2) := by
      calc
        m=Nat.pair (Nat.unpair m).1 (Nat.unpair m).2 := (Nat.pair_unpair m).symm
        _=Nat.pair r (Nat.pair head (Nat.unpair (Nat.unpair m).2).2) := by
          rw [hp,← hl,Nat.pair_unpair]
    change value ∈ Total.val hc.left.hom (Nat.pair r (Nat.pair head (Nat.unpair (Nat.unpair m).2).2))
    rw [← he]
    exact hvalue
  · rintro ⟨w,hw,hvalue⟩
    have hf : r ∈ Total.val (family R V).hom.hom (Nat.pair r tail) := by
      change r ∈ Total.val (Total.partialFst R.obj (carrier V)) (Nat.pair r tail)
      apply (Total.mem_partialFst R.obj (carrier V) _ _).mpr
      refine ⟨?_,by simp only [Nat.unpair_pair]⟩
      change (Nat.unpair (Nat.pair r tail)).1 ∈ R.obj.support ∧
        (Nat.unpair (Nat.pair r tail)).2 ∈ (carrier V).support
      simpa only [Nat.unpair_pair] using And.intro hr ht
    refine ⟨Nat.pair r (Nat.pair head w),?_,hvalue⟩
    apply (Syntax.Raw.rawAction_graph R (family R V) (family R V) X X f f
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term)
      r (Nat.pair head (Nat.pair r tail)) r (Nat.pair head w)).mpr
    simpa only [Syntax.Raw.ActionGraph,Nat.unpair_pair] using
      (show r=r ∧ (r ∈ R.obj.support ∧ head ∈ V.support ∧ head=head) ∧
        (r ∈ Total.val (family R V).hom.hom (Nat.pair r tail) ∧
          w ∈ Total.val f.left.hom (Nat.pair r tail)) from ⟨rfl,⟨hr,hh,rfl⟩,hf,hw⟩)

theorem rawNil_square_iff : rawNil R V ≫ f=h0 ↔
    ∀ r ∈ R.obj.support,∀ value,value ∈ Total.val f.left.hom (Nat.pair r 0) ↔
      value ∈ Syntax.Raw.operation h0 (r,0) := by
  constructor
  · intro he r hr value
    have hval := congrArg (fun k => Total.val k.left.hom (Nat.pair r 0)) he
    rw [← rawNil_then_graph V f r value hr]
    exact Iff.of_eq (congrArg (fun z : Part ℕ => value ∈ z) hval)
  · intro h
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    have hr : (Nat.unpair n).1 ∈ R.obj.support := hn.1
    have hzero : (Nat.unpair n).2=0 := hn.2
    have he : n=Nat.pair (Nat.unpair n).1 0 := by simpa only [hzero] using (Nat.pair_unpair n).symm
    apply Part.ext
    intro value
    rw [he,rawNil_then_graph V f _ value hr]
    exact h _ hr value

theorem rawCons_square_iff :
    rawCons R V ≫ f=Syntax.Raw.rawAction R (family R V) (family R V) X X f f
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ≫ hc ↔
    ∀ r ∈ R.obj.support,∀ head ∈ V.support,∀ tail ∈ (carrier V).support,∀ value,
      value ∈ Total.val f.left.hom (Nat.pair r (adjoin head tail)) ↔
        ∃ w,w ∈ Total.val f.left.hom (Nat.pair r tail) ∧ value ∈ Syntax.Raw.operation hc (r,Nat.pair head w) := by
  constructor
  · intro he r hr head hh tail ht value
    have hv := congrArg (fun k => Total.val k.left.hom (Nat.pair r (Nat.pair head (Nat.pair r tail)))) he
    exact (rawCons_then_graph V f r head tail value hr hh ht).symm.trans
      ((Iff.of_eq (congrArg (fun z : Part ℕ => value ∈ z) hv)).trans
        (actionCons_then_graph V f hc r head tail value hr hh ht))
  · intro h
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro n hn
    obtain ⟨r,head,tail,hr,hh,ht,rfl⟩ := rawCons_input R V n hn
    apply Part.ext
    intro value
    exact (rawCons_then_graph V f r head tail value hr hh ht).trans
      ((h r hr head hh tail ht value).trans
        (actionCons_then_graph V f hc r head tail value hr hh ht).symm)

theorem fold_rawNil : rawNil R V ≫ fold V h0 hc=h0 :=
  (rawNil_square_iff V (fold V h0 hc) h0).mpr (fun r _ value => fold_nil V h0 hc r value)

theorem fold_rawCons : rawCons R V ≫ fold V h0 hc=
    Syntax.Raw.rawAction R (family R V) (family R V) X X (fold V h0 hc) (fold V h0 hc)
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ≫ hc :=
  (rawCons_square_iff V (fold V h0 hc) hc).mpr (fun r _ head _ tail _ value => fold_adjoin V h0 hc r head tail value)

end CategoricalEssentialIncompleteness.V46.Miller.Lists
