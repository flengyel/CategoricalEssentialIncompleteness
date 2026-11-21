/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryCoproducts

/-! # Connected points, finite domain joins and uniform partial inverses -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

def support {X : Object z} (a : Idem X) : Set (carrier z X) := {x | (a.hom.val x).Dom}

theorem support_enumerable {X : Object z} (a : Idem X) : Enumerable z (· ∈ support a) := a.hom.represented.domain

theorem mem_idem {X : Object z} (a : Idem X) (x y : carrier z X) :
    y ∈ a.hom.val x ↔ x ∈ support a ∧ y=x := PartialFunctions.mem_idem (toPfnIdem a) x y

theorem le_iff_pfn {X : Object z} (a b : Idem X) :
    a ≤ b ↔ toPfnIdem a ≤ toPfnIdem b := by
  constructor
  · intro h
    exact congrArg Arrow.val h
  · intro h
    exact Arrow.ext h

theorem support_le_iff {X : Object z} (a b : Idem X) :
    a ≤ b ↔ support a ⊆ support b :=
  (le_iff_pfn a b).trans (PartialFunctions.le_iff_support (toPfnIdem a) (toPfnIdem b))

@[simp] theorem toPfnIdem_setIdem (X : Object z) (A : Set (carrier z X))
    (hA : Enumerable z (· ∈ A)) : toPfnIdem (setIdem X A hA)=PartialFunctions.setIdem A := rfl

@[simp] theorem support_setIdem (X : Object z) (A : Set (carrier z X))
    (hA : Enumerable z (· ∈ A)) : support (setIdem X A hA)=A := by
  change PartialFunctions.support (toPfnIdem (setIdem X A hA))=A
  rw [toPfnIdem_setIdem,PartialFunctions.support_setIdem]

instance : BinaryJoins (Object z) where
  join a b := setIdem _ (support a ∪ support b) ((support_enumerable a).or (support_enumerable b))
  le_left a b := (support_le_iff _ _).mpr (by
    rw [support_setIdem]; exact Set.subset_union_left)
  le_right a b := (support_le_iff _ _).mpr (by
    rw [support_setIdem]; exact Set.subset_union_right)
  least a b c ha hb := (support_le_iff _ _).mpr (by
    rw [support_setIdem]
    exact Set.union_subset ((support_le_iff _ _).mp ha) ((support_le_iff _ _).mp hb))

@[simp] theorem toPfnIdem_sup {X : Object z} (a b : Idem X) :
    toPfnIdem (a ⊔ b)=toPfnIdem a ⊔ toPfnIdem b := by
  apply Idem.ext
  apply PFun.ext
  intro x y
  change y ∈ (identityOn X (support a ∪ support b) ((support_enumerable a).or (support_enumerable b))).val x ↔
    y ∈ (toPfnIdem a ⊔ toPfnIdem b).hom x
  rw [mem_identityOn,PartialFunctions.mem_idem,PartialFunctions.support_sup]
  rfl

@[simp] theorem toPfnIdem_inf {X : Object z} (a b : Idem X) :
    toPfnIdem (a ⊓ b)=toPfnIdem a ⊓ toPfnIdem b := rfl

@[simp] theorem toPfnIdem_top {X : Object z} :
    toPfnIdem (⊤ : Idem X)=⊤ := rfl

@[simp] theorem toPfnIdem_bot {X : Object z} :
    toPfnIdem (⊥ : Idem X)=⊥ := rfl

@[simp] theorem toPfnIdem_pull {X Y : Object z} (f : X ⟶ Y) (a : Idem Y) :
    toPfnIdem (Idem.pull f a)=Idem.pull f.val (toPfnIdem a) := rfl

instance : JoinInverse (Object z) where
  pull_sup f a b := by
    apply toPfnIdem_injective
    rw [toPfnIdem_pull,toPfnIdem_sup,JoinInverse.pull_sup,toPfnIdem_sup,
      toPfnIdem_pull,toPfnIdem_pull]


def singletonIdem (X : Object z) (x : carrier z X) : Idem X :=
  setIdem X {x} (Enumerable.of_re
    ((Primrec.eq.comp Primrec.id (Primrec.const x)).computablePred.to_re))

theorem singleton_connected (X : Object z) (x : carrier z X) : Connected (singletonIdem X x) := by
  intro b c he hd
  have he' : PartialFunctions.setIdem ({x} : Set (carrier z X)) =
      toPfnIdem b ⊔ toPfnIdem c := by
    simpa only [singletonIdem,toPfnIdem_setIdem,toPfnIdem_sup] using congrArg toPfnIdem he
  have hd' : toPfnIdem b ⊓ toPfnIdem c = ⊥ := by
    simpa only [toPfnIdem_inf,toPfnIdem_bot] using congrArg toPfnIdem hd
  obtain hb | hc := PartialFunctions.singleton_connected x (toPfnIdem b) (toPfnIdem c) he' hd'
  · exact Or.inl (toPfnIdem_injective (hb.trans (toPfnIdem_bot (X := X)).symm))
  · exact Or.inr (toPfnIdem_injective (hc.trans (toPfnIdem_bot (X := X)).symm))

instance locallyConnected : LocallyConnected (Object z) where
  hom_ext := by
    intro X Y f g h
    apply Arrow.ext
    funext x
    have he := congrArg (fun k : X ⟶ Y => k.val x)
      (h (singletonIdem X x) (singleton_connected X x))
    have hs : x ∈ support (singletonIdem X x) := by
      rw [singletonIdem,support_setIdem]
      rfl
    have hx : (singletonIdem X x).hom.val x = Part.some x :=
      Part.eq_some_iff.mpr ((mem_idem (singletonIdem X x) x x).mpr ⟨hs,rfl⟩)
    change ((singletonIdem X x).hom.val x).bind f.val =
      ((singletonIdem X x).hom.val x).bind g.val at he
    simpa only [hx,Part.bind_some] using he

def Injective {X Y : Object z} (f : X ⟶ Y) : Prop :=
  ∀ x x' y,y ∈ f.val x → y ∈ f.val x' → x = x'

/-- Constant probes are ordinary recursive morphisms. Partial monicity in this category
therefore detects injectivity of its partial graph. -/
theorem injective_of_partialMono {X Y : Object z} (f : X ⟶ Y) (hf : PartialMono f) : Injective f := by
  intro x x' y hy hy'
  let u : N z ⟶ X := totalFromFunction (fun _ => x) (Computable.const x)
  let v : N z ⟶ X := totalFromFunction (fun _ => x') (Computable.const x')
  have hc : u ≫ f = v ≫ f := by
    apply Arrow.ext
    funext n
    simp only [comp_val,u,v,totalFromFunction,ofPartrec,Part.bind_some]
    exact (Part.eq_some_iff.mpr hy).trans (Part.eq_some_iff.mpr hy').symm
  have hr := congrArg (fun h => h.val (0 : ℕ)) (hf u v hc)
  have hu : (rst f).val x = Part.some x :=
    Part.eq_some_iff.mpr ((mem_identityOn X _ f.represented.domain x x).mpr ⟨hy.1,rfl⟩)
  have hv : (rst f).val x' = Part.some x' :=
    Part.eq_some_iff.mpr ((mem_identityOn X _ f.represented.domain x' x').mpr ⟨hy'.1,rfl⟩)
  simp only [comp_val,u,v,totalFromFunction,ofPartrec,Part.bind_some] at hr
  rw [hu,hv] at hr
  exact Part.some_injective hr

def inverse {X Y : Object z} (f : X ⟶ Y) (hf : Injective f) : Y ⟶ X := by
  let s : carrier z Y → Part (carrier z X) := PartialFunctions.chosenSection f.val
  have hs (y : carrier z Y) (x : carrier z X) : x ∈ s y ↔ y ∈ f.val x := by
    constructor
    · exact PartialFunctions.chosenSection_sound f.val y x
    · intro h
      obtain ⟨x',hx'⟩ := (PartialFunctions.chosenSection_domain f.val y).mpr ⟨x,h⟩
      have he : x' = x := hf x' x y (PartialFunctions.chosenSection_sound f.val y x' hx') h
      exact he ▸ hx'
  refine ⟨s,(represented_iff_graph_enumerable z Y.type X.type s).mpr ?_⟩
  exact (Enumerable.comp (Computable.pair Computable.snd Computable.fst) (graph_enumerable f)).of_eq
    (fun a => (hs a.1 a.2).symm)

theorem inverse_graph {X Y : Object z} (f : X ⟶ Y) (hf : Injective f)
    (y : carrier z Y) (x : carrier z X) : x ∈ (inverse f hf).val y ↔ y ∈ f.val x := by
  constructor
  · exact PartialFunctions.chosenSection_sound f.val y x
  · intro h
    obtain ⟨x',hx'⟩ := (PartialFunctions.chosenSection_domain f.val y).mpr ⟨x,h⟩
    have he : x' = x := hf x' x y (PartialFunctions.chosenSection_sound f.val y x' hx') h
    exact he ▸ hx'

theorem inverse_isSection {X Y : Object z} (f : X ⟶ Y) (hf : Injective f) : SectionOf f (inverse f hf) := by
  have h := PartialFunctions.chosenSection_isSection f.val
  exact ⟨Arrow.ext h.comp,Arrow.ext h.receives⟩

instance weakChoice : WeakChoice (Object z) where
  section_exists f hf :=
    ⟨inverse f (injective_of_partialMono f hf),inverse_isSection f (injective_of_partialMono f hf)⟩

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
