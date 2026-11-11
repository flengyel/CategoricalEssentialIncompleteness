/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableInverses
public import CategoricalEssentialIncompleteness.ClassicalRanges
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Finite limits of total maps between c.e. carriers -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def commonValue {X Y : Carrier} (f g : X ⟶ Y) : Set ℕ :=
  {x | ∃ y, y ∈ val f x ∧ y ∈ val g x}

theorem commonValue_re {X Y : Carrier} (f g : X ⟶ Y) : REPred (· ∈ commonValue f g) :=
  (REPred.comp (Computable.pair Computable.snd Computable.fst)
    ((ClassicalRecursion.partrec_graph_enumerable (val_partrec f)).and
      (ClassicalRecursion.partrec_graph_enumerable (val_partrec g)))).projection

def equalizerIdem {X Y : Carrier} (f g : X ⟶ Y) : Idem X :=
  relativeIdem (commonValue f g) (commonValue_re f g)
    (fun _ h => by obtain ⟨y,hy,_⟩ := h; exact val_source f _ y hy)

@[simp] theorem support_equalizerIdem {X Y : Carrier} (f g : X ⟶ Y) :
    support (equalizerIdem f g) = commonValue f g := support_relativeIdem _ _ _

theorem commonValue_eq {X Y : Carrier} (f g : X ⟶ Y) (x : ℕ)
    (hx : x ∈ commonValue f g) : val f x = val g x := by
  obtain ⟨y,hf,hg⟩ := hx
  exact (Part.eq_some_iff.mpr hf).trans (Part.eq_some_iff.mpr hg).symm

theorem equalizerIdem_condition {X Y : Carrier} (f g : X ⟶ Y) :
    (equalizerIdem f g).hom ≫ f = (equalizerIdem f g).hom ≫ g := by
  apply val_injective
  apply PFun.ext
  intro x y
  simp only [mem_val_precomp_idem, support_equalizerIdem]
  constructor
  · rintro ⟨hx,hy⟩
    exact ⟨hx, commonValue_eq f g x hx ▸ hy⟩
  · rintro ⟨hx,hy⟩
    exact ⟨hx, (commonValue_eq f g x hx).symm ▸ hy⟩

theorem equalizing_output {W X Y : Carrier} (f g : X ⟶ Y) (hf : isTotal f)
    (k : W ⟶ X) (he : k ≫ f = k ≫ g) (x y : ℕ) (hxy : y ∈ val k x) :
    y ∈ commonValue f g := by
  obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp ((total_iff f).mp hf y (val_target k x y hxy))
  have hh : z ∈ val (k ≫ g) x := by
    rw [← he]
    exact (mem_val_comp _ _ _ _).mpr ⟨y,hxy,hz⟩
  obtain ⟨y',hy',hz'⟩ := (mem_val_comp _ _ _ _).mp hh
  have hy : y'=y := Part.mem_unique hy' hxy
  exact ⟨z,hz,hy ▸ hz'⟩

def intoSubcarrier {W X : Carrier} (k : W ⟶ X) (a : Idem X)
    (h : ∀ x y, y ∈ val k x → y ∈ support a) : W ⟶ subcarrier a :=
  arrow (val k) (val_partrec k) (val_source k) h

theorem intoSubcarrier_total {W X : Carrier} (k : W ⟶ X) (hk : isTotal k)
    (a : Idem X) (h : ∀ x y, y ∈ val k x → y ∈ support a) :
    isTotal (intoSubcarrier k a h) := (total_iff _).mpr ((total_iff k).mp hk)

theorem intoSubcarrier_fac {W X : Carrier} (k : W ⟶ X) (a : Idem X)
    (h : ∀ x y, y ∈ val k x → y ∈ support a) : intoSubcarrier k a h ≫ into a = k := by
  apply val_injective
  apply PFun.ext
  intro x y
  change y ∈ (val k x).bind (val a.hom) ↔ y ∈ val k x
  rw [Part.mem_bind_iff]
  constructor
  · rintro ⟨z,hz,hy⟩
    obtain ⟨_,he⟩ := (mem_val_idem a z y).mp hy
    exact he ▸ hz
  · intro hy
    exact ⟨y,hy,(mem_val_idem a y y).mpr ⟨h x y hy,rfl⟩⟩

theorem mono_of_total_injective {X Y : Carrier} (f : X ⟶ Y)
    (hf : isTotal f) (hi : Injective f) : Mono f where
  right_cancellation g h he := by
    have hh := partialMono_of_injective f hi g h he
    simpa only [show rst f=𝟙 X from hf, Category.comp_id] using hh

instance into_mono {X : Carrier} (a : Idem X) : Mono (into a) :=
  mono_of_total_injective _ (into_total a) (by
    intro x x' y h h'
    exact ((mem_val_idem a x y).mp h).2.symm.trans ((mem_val_idem a x' y).mp h').2)

def totalProduct (X Y : Total) : Total := ⟨product X.obj Y.obj⟩
def totalFst (X Y : Total) : totalProduct X Y ⟶ X := ⟨partialFst _ _,partialFst_total _ _⟩
def totalSnd (X Y : Total) : totalProduct X Y ⟶ Y := ⟨partialSnd _ _,partialSnd_total _ _⟩

theorem partialPair_total {W X Y : Carrier} (f : W ⟶ X) (g : W ⟶ Y)
    (hf : isTotal f) (hg : isTotal g) : isTotal (partialPair f g) := by
  change rst (partialPair f g)=𝟙 W
  rw [rst_partialPair,hf,hg,Category.id_comp]

def totalPair {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ totalProduct X Y :=
  ⟨partialPair f.hom g.hom,partialPair_total _ _ f.property g.property⟩

@[simp] theorem totalPair_fst {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    totalPair f g ≫ totalFst X Y = f := by
  apply WideSubcategory.hom_ext
  change partialPair f.hom g.hom ≫ partialFst _ _=f.hom
  rw [partialPair_fst,g.property,Category.id_comp]

@[simp] theorem totalPair_snd {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    totalPair f g ≫ totalSnd X Y = g := by
  apply WideSubcategory.hom_ext
  change partialPair f.hom g.hom ≫ partialSnd _ _=g.hom
  rw [partialPair_snd,f.property,Category.id_comp]

def productIsLimit (X Y : Total) : IsLimit (BinaryFan.mk (totalFst X Y) (totalSnd X Y)) :=
  BinaryFan.isLimitMk (fun s => totalPair s.fst s.snd)
    (fun _ => totalPair_fst _ _) (fun _ => totalPair_snd _ _) (by
      intro s m hm0 hm1
      apply WideSubcategory.hom_ext
      apply partial_product_hom_ext
      · exact congrArg (fun k => k.hom) (hm0.trans (totalPair_fst s.fst s.snd).symm)
      · exact congrArg (fun k => k.hom) (hm1.trans (totalPair_snd s.fst s.snd).symm))

instance totalProductHasLimit (X Y : Total) : HasLimit (Limits.pair X Y) :=
  ⟨⟨_,productIsLimit X Y⟩⟩
instance : HasBinaryProducts Total := hasBinaryProducts_of_hasLimit_pair Total

def terminalCarrier : Carrier := ⟨{0},
  (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred.to_re⟩

def terminalArrow (X : Total) : X ⟶ (⟨terminalCarrier⟩ : Total) :=
  ⟨totalFromFunction (X := X.obj) (Y := terminalCarrier)
      (fun _ => 0) (.const 0) (fun _ _ => rfl),
    totalFromFunction_total (X := X.obj) (Y := terminalCarrier)
      _ (.const 0) (fun _ _ => rfl)⟩

def terminalIsTerminal : IsTerminal (⟨terminalCarrier⟩ : Total) :=
  IsTerminal.ofUniqueHom terminalArrow (by
    intro X f
    apply WideSubcategory.hom_ext
    apply val_ext_on_source
    intro x hx
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((total_iff f.hom).mp f.property x hx)
    have hy0 : y=0 := val_target f.hom x y hy
    subst y
    exact (Part.eq_some_iff.mpr hy).trans
      (Part.eq_some_iff.mpr ((mem_totalFromFunction (X := X.obj) (Y := terminalCarrier)
        (fun _ => 0) (.const 0) (fun _ _ => rfl) x 0).mpr
        ⟨hx,rfl⟩)).symm)

instance : HasTerminal Total := terminalIsTerminal.hasTerminal

def totalEqualizer {X Y : Total} (f g : X ⟶ Y) : Total :=
  ⟨subcarrier (equalizerIdem f.hom g.hom)⟩
def equalizerι {X Y : Total} (f g : X ⟶ Y) : totalEqualizer f g ⟶ X :=
  ⟨into (equalizerIdem f.hom g.hom),into_total _⟩

theorem equalizer_condition {X Y : Total} (f g : X ⟶ Y) : equalizerι f g ≫ f=equalizerι f g ≫ g := by
  apply WideSubcategory.hom_ext
  apply val_injective
  exact congrArg (fun k : X.obj ⟶ Y.obj => val k) (equalizerIdem_condition f.hom g.hom)

instance equalizerι_mono {X Y : Total} (f g : X ⟶ Y) : Mono (equalizerι f g) where
  right_cancellation u v he := by
    apply WideSubcategory.hom_ext
    exact (cancel_mono (into (equalizerIdem f.hom g.hom))).mp (congrArg (fun k => k.hom) he)

def totalEqualizerLift {W X Y : Total} (f g : X ⟶ Y) (k : W ⟶ X) (he : k ≫ f=k ≫ g) :
    W ⟶ totalEqualizer f g :=
  let bound : ∀ x y, y ∈ val k.hom x → y ∈ support (equalizerIdem f.hom g.hom) := by
    intro x y hxy
    rw [support_equalizerIdem]
    exact equalizing_output f.hom g.hom f.property k.hom (congrArg (fun k => k.hom) he) x y hxy
  ⟨intoSubcarrier k.hom _ bound,intoSubcarrier_total k.hom k.property _ bound⟩

@[simp] theorem totalEqualizerLift_fac {W X Y : Total} (f g : X ⟶ Y)
    (k : W ⟶ X) (he : k ≫ f=k ≫ g) : totalEqualizerLift f g k he ≫ equalizerι f g=k := by
  apply WideSubcategory.hom_ext
  exact intoSubcarrier_fac k.hom (equalizerIdem f.hom g.hom) (fun x y hxy => by
    rw [support_equalizerIdem]
    exact equalizing_output f.hom g.hom f.property k.hom
      (congrArg (fun k => k.hom) he) x y hxy)

def equalizerIsLimit {X Y : Total} (f g : X ⟶ Y) :
    IsLimit (Limits.Fork.ofι (equalizerι f g) (equalizer_condition f g)) :=
  Limits.Fork.IsLimit.mk _ (fun s => totalEqualizerLift f g s.ι s.condition)
    (fun s => totalEqualizerLift_fac f g s.ι s.condition) (by
      intro s m hm
      apply (cancel_mono (equalizerι f g)).mp
      exact hm.trans (totalEqualizerLift_fac f g s.ι s.condition).symm)

instance totalEqualizerHasLimit {X Y : Total} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  ⟨⟨_,equalizerIsLimit f g⟩⟩
instance : HasEqualizers Total := hasEqualizers_of_hasLimit_parallelPair Total
instance : HasFiniteProducts Total := hasFiniteProducts_of_has_binary_and_terminal
instance : HasFiniteLimits Total := hasFiniteLimits_of_hasEqualizers_and_finite_products

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
