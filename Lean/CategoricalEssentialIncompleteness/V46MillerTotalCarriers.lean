/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryInclusion
public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences

/-! # Arbitrary uniformly semidecidable numerical carriers

Morphisms are the original supported split morphisms. In particular, no ordinary
partial-recursive value extension and no inhabited carrier is required. Restriction,
image, and graph computations use the uniform oracle programs already constructed in
Proposition 9.2.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total

structure Carrier (P : Uniform.Family) where
  support : Set ℕ
  enumerable : Uniform.Enumerable P (· ∈ support)

variable {P : Uniform.Family}
attribute [instance 2000] Uniform.nativeRestriction

def supportIdentity (A : Set ℕ) : ℕ → Part ℕ :=
  PartialFunctions.partialIdentity (PartialFun.of ℕ) A

theorem mem_supportIdentity (A : Set ℕ) (x y : ℕ) :
    y ∈ supportIdentity A x ↔ x ∈ A ∧ y=x := PartialFunctions.mem_identity A x y

def partialObject (X : Carrier P) : SplitObject (Uniform.Object P) :=
  ⟨Uniform.N P,Uniform.setIdem (Uniform.N P) X.support X.enumerable⟩

instance carrierCategory : Category (Carrier P) where
  Hom X Y := partialObject X ⟶ partialObject Y
  id X := 𝟙 (partialObject X)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def inclusion : Carrier P ⥤ SplitObject (Uniform.Object P) where
  obj := partialObject
  map f := f

instance : (inclusion (P := P)).Faithful where
  map_injective h := h
instance : (inclusion (P := P)).Full where
  map_surjective f := ⟨f,rfl⟩

instance carrierRestriction : RestrictionCategory (Carrier P) where
  rst f := rst (C := SplitObject (Uniform.Object P)) f
  rst_comp_self f := rst_comp_self (C := SplitObject (Uniform.Object P)) f
  rst_comm f g := rst_comm (C := SplitObject (Uniform.Object P)) f g
  rst_comp_rst f g := rst_comp_rst (C := SplitObject (Uniform.Object P)) f g
  rst_comp f g := rst_comp (C := SplitObject (Uniform.Object P)) f g

instance : HasZeroMorphisms (Carrier P) where
  zero X Y := inferInstanceAs (Zero (partialObject X ⟶ partialObject Y))
  comp_zero := by intros; exact CategoryTheory.Limits.comp_zero (C := SplitObject (Uniform.Object P))
  zero_comp := by intros; exact CategoryTheory.Limits.zero_comp (C := SplitObject (Uniform.Object P))

instance : RestrictionZero (Carrier P) where
  restrict_zero X Y := RestrictionZero.restrict_zero (partialObject X) (partialObject Y)

def toSplitIdem {X : Carrier P} (a : Idem X) : Idem (partialObject X) := ⟨a.hom,a.restriction⟩
def ofSplitIdem {X : Carrier P} (a : Idem (partialObject X)) : Idem X := ⟨a.hom,a.restriction⟩

def idemOrderIso (X : Carrier P) : Idem X ≃o Idem (partialObject X) where
  toFun := toSplitIdem
  invFun := ofSplitIdem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance : Ranges (Carrier P) where
  range f := ofSplitIdem (Ranges.range (C := SplitObject (Uniform.Object P)) f)
  receives f := Ranges.receives (C := SplitObject (Uniform.Object P)) f
  agreement f g h he := Ranges.agreement (C := SplitObject (Uniform.Object P)) f g h he

instance carrierBinaryJoins : BinaryJoins (Carrier P) where
  join a b := ofSplitIdem (toSplitIdem a ⊔ toSplitIdem b)
  le_left a b := (idemOrderIso _).symm.monotone
    (show toSplitIdem a ≤ toSplitIdem a ⊔ toSplitIdem b from le_sup_left)
  le_right a b := (idemOrderIso _).symm.monotone
    (show toSplitIdem b ≤ toSplitIdem a ⊔ toSplitIdem b from le_sup_right)
  least _a _b _c ha hb := (idemOrderIso _).symm.monotone
    (sup_le ((idemOrderIso _).monotone ha) ((idemOrderIso _).monotone hb))

@[simp] theorem toSplitIdem_sup {X : Carrier P} (a b : Idem X) :
    toSplitIdem (a ⊔ b)=toSplitIdem a ⊔ toSplitIdem b := rfl

@[simp] theorem toSplitIdem_pull {X Y : Carrier P} (f : X ⟶ Y) (a : Idem Y) :
    toSplitIdem (Idem.pull (C := Carrier P) f a)=
      Idem.pull (C := SplitObject (Uniform.Object P)) f (toSplitIdem a) := rfl

instance : JoinInverse (Carrier P) where
  pull_sup f a b := by
    apply (idemOrderIso _).injective
    change toSplitIdem (Idem.pull (C := Carrier P) f (a ⊔ b))=
      toSplitIdem (Idem.pull (C := Carrier P) f a ⊔ Idem.pull (C := Carrier P) f b)
    rw [toSplitIdem_pull,toSplitIdem_sup,JoinInverse.pull_sup,toSplitIdem_sup,
      toSplitIdem_pull,toSplitIdem_pull]

def val {X Y : Carrier P} (f : X ⟶ Y) : ℕ → Part ℕ := f.hom.val

theorem val_injective {X Y : Carrier P} : Function.Injective (val (X := X) (Y := Y)) := by
  intro f g h
  exact SplitObject.Hom.ext (Uniform.Arrow.ext h)

@[simp] theorem val_id (X : Carrier P) : val (𝟙 X) = supportIdentity X.support := rfl
@[simp] theorem val_comp {X Y Z : Carrier P} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    val (f ≫ g) n = (val f n).bind (val g) := rfl
@[simp] theorem val_zero (X Y : Carrier P) : val (0 : X ⟶ Y) = fun _ => Part.none := rfl

theorem val_represented {X Y : Carrier P} (f : X ⟶ Y) :
    Uniform.Represented P .nat .nat (val f) := f.hom.represented

theorem graph_enumerable {X Y : Carrier P} (f : X ⟶ Y) :
    Uniform.Enumerable P (fun a : ℕ × ℕ => a.2 ∈ val f a.1) :=
  (Uniform.represented_iff_graph_enumerable P .nat .nat (val f)).mp (val_represented f)

theorem val_restriction {X Y : Carrier P} (f : X ⟶ Y) :
    val (rst f) = rst (C := PartialFunctions.Pfn) (val f) := rfl

theorem val_source {X Y : Carrier P} (f : X ⟶ Y) (x y : ℕ) (h : y ∈ val f x) : x ∈ X.support := by
  have hh : y ∈ (supportIdentity X.support x).bind (val f) := by
    change y ∈ ((partialObject X).domain.hom ≫ f.hom).val x
    rw [f.source]
    exact h
  obtain ⟨n,hn,_⟩ := Part.mem_bind_iff.mp hh
  exact ((mem_supportIdentity X.support x n).mp hn).1

theorem val_target {X Y : Carrier P} (f : X ⟶ Y) (x y : ℕ) (h : y ∈ val f x) : y ∈ Y.support := by
  have hh : y ∈ (val f x).bind (supportIdentity Y.support) := by
    change y ∈ (f.hom ≫ (partialObject Y).domain.hom).val x
    rw [f.target]
    exact h
  obtain ⟨n,_,hn⟩ := Part.mem_bind_iff.mp hh
  obtain ⟨hs,he⟩ := (mem_supportIdentity Y.support n y).mp hn
  exact he ▸ hs

@[simp] theorem mem_val_comp {X Y Z : Carrier P} (f : X ⟶ Y) (g : Y ⟶ Z) (x z : ℕ) :
    z ∈ val (f ≫ g) x ↔ ∃ y,y ∈ val f x ∧ z ∈ val g y := Part.mem_bind_iff

@[simp] theorem mem_val_restriction {X Y : Carrier P} (f : X ⟶ Y) (x y : ℕ) :
    y ∈ val (rst f) x ↔ (∃ z,z ∈ val f x) ∧ y=x := PartialFunctions.mem_rst (val f) x y

theorem total_iff {X Y : Carrier P} (f : X ⟶ Y) :
    isTotal f ↔ ∀ x ∈ X.support,(val f x).Dom := by
  constructor
  · intro hf x hx
    have h : x ∈ val (rst f) x := by
      rw [hf,val_id]
      exact (mem_supportIdentity X.support x x).mpr ⟨hx,rfl⟩
    exact Part.dom_iff_mem.mpr ((mem_val_restriction f x x).mp h).1
  · intro hf
    apply val_injective
    funext x
    apply Part.ext
    intro y
    rw [mem_val_restriction,val_id,mem_supportIdentity]
    constructor
    · rintro ⟨⟨n,hn⟩,he⟩
      exact ⟨val_source f x n hn,he⟩
    · rintro ⟨hx,he⟩
      exact ⟨Part.dom_iff_mem.mp (hf x hx),he⟩

def arrow {X Y : Carrier P} (f : ℕ → Part ℕ) (hf : Uniform.Represented P .nat .nat f)
    (hs : ∀ x y,y ∈ f x → x ∈ X.support) (ht : ∀ x y,y ∈ f x → y ∈ Y.support) : X ⟶ Y :=
  ⟨⟨f,hf⟩,by
    apply Uniform.hom_ext_mem
    intro x y
    change y ∈ (supportIdentity X.support x).bind f ↔ y ∈ f x
    simp only [Part.mem_bind_iff,mem_supportIdentity]
    constructor
    · rintro ⟨n,⟨_,he⟩,hy⟩
      exact he ▸ hy
    · intro hy
      exact ⟨x,⟨hs x y hy,rfl⟩,hy⟩,by
    apply Uniform.hom_ext_mem
    intro x y
    change y ∈ (f x).bind (supportIdentity Y.support) ↔ y ∈ f x
    simp only [Part.mem_bind_iff]
    constructor
    · rintro ⟨n,hn,_,he⟩
      exact he ▸ hn
    · intro hy
      exact ⟨y,hy,ht x y hy,rfl⟩⟩

@[simp] theorem val_arrow {X Y : Carrier P} (f : ℕ → Part ℕ)
    (hf : Uniform.Represented P .nat .nat f)
    (hs : ∀ x y,y ∈ f x → x ∈ X.support) (ht : ∀ x y,y ∈ f x → y ∈ Y.support) :
    val (arrow f hf hs ht) = f := rfl

def support {X : Carrier P} (a : Idem X) : Set ℕ := {n | (val a.hom n).Dom}

theorem mem_val_idem {X : Carrier P} (a : Idem X) (x y : ℕ) :
    y ∈ val a.hom x ↔ x ∈ support a ∧ y=x :=
  Uniform.mem_idem (SplitObject.baseIdem (toSplitIdem a)) x y

theorem support_injective {X : Carrier P} : Function.Injective (support (X := X)) := by
  intro a b he
  apply Idem.ext
  apply val_injective
  funext x
  apply Part.ext
  intro y
  rw [mem_val_idem,mem_val_idem,he]

theorem support_le_iff {X : Carrier P} (a b : Idem X) :
    a ≤ b ↔ support a ⊆ support b :=
  (SplitObject.le_iff_base (toSplitIdem a) (toSplitIdem b)).trans
    (Uniform.support_le_iff (SplitObject.baseIdem (toSplitIdem a)) (SplitObject.baseIdem (toSplitIdem b)))

theorem support_re {X : Carrier P} (a : Idem X) : Uniform.Enumerable P (· ∈ support a) :=
  (val_represented a.hom).domain

@[simp] theorem support_range {X Y : Carrier P} (f : X ⟶ Y) :
    support (Ranges.range f) = {y | ∃ x,y ∈ val f x} := PartialFunctions.support_setIdem _

@[simp] theorem support_top (X : Carrier P) : support (⊤ : Idem X) = X.support := by
  ext x
  change (supportIdentity X.support x).Dom ↔ x ∈ X.support
  rw [Part.dom_iff_mem]
  simp only [mem_supportIdentity,exists_eq_right]

@[simp] theorem support_bot (X : Carrier P) : support (⊥ : Idem X) = ∅ := rfl

theorem support_subset {X : Carrier P} (a : Idem X) : support a ⊆ X.support :=
  fun x hx => val_source a.hom x x ((mem_val_idem a x x).mpr ⟨hx,rfl⟩)

theorem support_pull {X Y : Carrier P} (f : X ⟶ Y) (a : Idem Y) :
    support (Idem.pull f a) = {x | ∃ y,y ∈ val f x ∧ y ∈ support a} :=
  PartialFunctions.support_pull (val f)
    (Uniform.toPfnIdem (SplitObject.baseIdem (toSplitIdem a)))

def relativeIdem {X : Carrier P} (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A))
    (h : A ⊆ X.support) : Idem X :=
  ofSplitIdem (SplitObject.relativeIdem (Uniform.setIdem (Uniform.N P) A hA)
    ((Uniform.support_le_iff _ _).mpr (by
      change A ⊆ Uniform.support (Uniform.setIdem (Uniform.N P) X.support X.enumerable)
      rw [Uniform.support_setIdem]
      exact h)))

@[simp] theorem support_relativeIdem {X : Carrier P} (A : Set ℕ)
    (hA : Uniform.Enumerable P (· ∈ A)) (h : A ⊆ X.support) :
    support (relativeIdem A hA h) = A := Uniform.support_setIdem (Uniform.N P) A hA

@[simp] theorem support_inf {X : Carrier P} (a b : Idem X) :
    support (a ⊓ b) = support a ∩ support b :=
  PartialFunctions.support_inf
    (Uniform.toPfnIdem (SplitObject.baseIdem (toSplitIdem a)))
    (Uniform.toPfnIdem (SplitObject.baseIdem (toSplitIdem b)))

@[simp] theorem support_sup {X : Carrier P} (a b : Idem X) :
    support (a ⊔ b) = support a ∪ support b := by
  change PartialFunctions.support (Uniform.toPfnIdem
      (SplitObject.baseIdem (toSplitIdem (a ⊔ b)))) = _
  rw [toSplitIdem_sup,SplitObject.base_sup,Uniform.toPfnIdem_sup]
  exact PartialFunctions.support_sup _ _

def singletonIdem {X : Carrier P} (x : ℕ) (hx : x ∈ X.support) : Idem X :=
  relativeIdem {x} (Uniform.Enumerable.of_re
    ((Primrec.eq.comp Primrec.id (Primrec.const x)).computablePred.to_re))
    (Set.singleton_subset_iff.mpr hx)

@[simp] theorem support_singletonIdem {X : Carrier P} (x : ℕ) (hx : x ∈ X.support) :
    support (singletonIdem x hx) = {x} := support_relativeIdem _ _ _

theorem eq_at_of_precomp_idem {X Y : Carrier P} (a : Idem X) (f g : X ⟶ Y)
    (he : a.hom ≫ f = a.hom ≫ g) (x : ℕ) (hx : x ∈ support a) : val f x = val g x := by
  have hi : val a.hom x = Part.some x :=
    Part.eq_some_iff.mpr ((mem_val_idem a x x).mpr ⟨hx,rfl⟩)
  have hh := congrArg (fun k => val k x) he
  simpa only [val_comp,hi,Part.bind_some] using hh

theorem val_ext_on_source {X Y : Carrier P} (f g : X ⟶ Y)
    (h : ∀ x ∈ X.support,val f x = val g x) : f = g := by
  apply val_injective
  funext x
  apply Part.ext
  intro y
  by_cases hx : x ∈ X.support
  · rw [h x hx]
  · exact ⟨fun hy => False.elim (hx (val_source f x y hy)),
      fun hy => False.elim (hx (val_source g x y hy))⟩

@[simp] theorem mem_val_precomp_idem {X Y : Carrier P} (a : Idem X)
    (f : X ⟶ Y) (x y : ℕ) :
    y ∈ val (a.hom ≫ f) x ↔ x ∈ support a ∧ y ∈ val f x := by
  rw [mem_val_comp]
  simp only [mem_val_idem]
  aesop

def subcarrier {X : Carrier P} (a : Idem X) : Carrier P := ⟨support a,support_re a⟩

def into {X : Carrier P} (a : Idem X) : subcarrier a ⟶ X :=
  arrow (val a.hom) (val_represented a.hom)
    (fun x y h => ((mem_val_idem a x y).mp h).1) (val_target a.hom)

def outof {X : Carrier P} (a : Idem X) : X ⟶ subcarrier a :=
  arrow (val a.hom) (val_represented a.hom) (val_source a.hom) (by
    intro x y h
    obtain ⟨hx,he⟩ := (mem_val_idem a x y).mp h
    exact he ▸ hx)

theorem into_total {X : Carrier P} (a : Idem X) : isTotal (into a) :=
  (total_iff _).mpr (fun x hx => Part.dom_iff_mem.mpr
    ⟨x,(mem_val_idem a x x).mpr ⟨hx,rfl⟩⟩)

theorem into_outof {X : Carrier P} (a : Idem X) : into a ≫ outof a = 𝟙 (subcarrier a) := by
  apply val_injective
  funext x
  apply Part.ext
  intro y
  change y ∈ (val a.hom x).bind (val a.hom) ↔ y ∈ supportIdentity (support a) x
  simp only [Part.mem_bind_iff,mem_val_idem,mem_supportIdentity]
  aesop

theorem outof_into {X : Carrier P} (a : Idem X) : outof a ≫ into a = a.hom := by
  apply val_injective
  change val (a.hom ≫ a.hom) = val a.hom
  rw [a.idem]

def restrictMap {X Y : Carrier P} (f : X ⟶ Y) (a : Idem X) (b : Idem Y)
    (h : ∀ x y,x ∈ support a → y ∈ val f x → y ∈ support b) : subcarrier a ⟶ subcarrier b :=
  arrow (val (a.hom ≫ f)) (val_represented _)
    (fun x y hh => ((mem_val_precomp_idem a f x y).mp hh).1)
    (fun x y hh => h x y ((mem_val_precomp_idem a f x y).mp hh).1
      ((mem_val_precomp_idem a f x y).mp hh).2)

@[simp] theorem mem_val_restrictMap {X Y : Carrier P} (f : X ⟶ Y) (a : Idem X) (b : Idem Y)
    (h : ∀ x y,x ∈ support a → y ∈ val f x → y ∈ support b) (x y : ℕ) :
    y ∈ val (restrictMap f a b h) x ↔ x ∈ support a ∧ y ∈ val f x := mem_val_precomp_idem a f x y

theorem restrictMap_total {X Y : Carrier P} (f : X ⟶ Y) (hf : isTotal f)
    (a : Idem X) (b : Idem Y)
    (h : ∀ x y,x ∈ support a → y ∈ val f x → y ∈ support b) : isTotal (restrictMap f a b h) := by
  apply (total_iff _).mpr
  intro x hx
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((total_iff f).mp hf x (support_subset a hx))
  exact Part.dom_iff_mem.mpr ⟨y,(mem_val_restrictMap f a b h x y).mpr ⟨hx,hy⟩⟩

theorem mem_support_ofRestrict {X Y : Carrier P} (f : X ⟶ Y) (x : ℕ) :
    x ∈ support (Idem.ofRestrict f) ↔ (val f x).Dom := by
  have h := mem_val_idem (Idem.ofRestrict f) x x
  change x ∈ val (rst f) x ↔ _ at h
  simpa only [mem_val_restriction,eq_self_iff_true,and_true,← Part.dom_iff_mem] using h.symm

def onDomain {X Y : Carrier P} (f : X ⟶ Y) : subcarrier (Idem.ofRestrict f) ⟶ Y :=
  arrow (val f) (val_represented f)
    (fun x _ h => (mem_support_ofRestrict f x).mpr h.1) (val_target f)

theorem onDomain_total {X Y : Carrier P} (f : X ⟶ Y) : isTotal (onDomain f) :=
  (total_iff _).mpr (fun x hx => (mem_support_ofRestrict f x).mp hx)

instance : Splits (Carrier P) where
  splitting a := ⟨subcarrier a,into a,outof a,into_total a,into_outof a,outof_into a⟩

abbrev TotalCategory (P : Uniform.Family) := WideSubcategory (isTotal (C := Carrier P))
abbrev PointTotal (z : Point) := TotalCategory (Uniform.Family.ofPoint z)

end CategoricalEssentialIncompleteness.V46.Miller.Total
