/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCategoryConnected
import CategoricalEssentialIncompleteness.DisjointJoins

/-! # Finite compatible unions of the actual uniform partial graphs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

def Compatible {X Y : Object z} (f g : X ⟶ Y) : Prop := rst f ≫ g = rst g ≫ f
def Below {X Y : Object z} (f g : X ⟶ Y) : Prop := rst f ≫ g = f

theorem below_iff {X Y : Object z} (f g : X ⟶ Y) :
    Below f g ↔ ∀ x y,y ∈ f.val x → y ∈ g.val x := by
  constructor
  · intro h x y hy
    have hm : y ∈ (rst f ≫ g).val x := by rw [h]; exact hy
    obtain ⟨v,hv,hg⟩ := Part.mem_bind_iff.mp hm
    have hvx : v = x := ((PartialFunctions.mem_rst f.val x v).mp hv).2
    exact hvx ▸ hg
  · intro h
    apply hom_ext_mem
    intro x y
    change y ∈ (rst (C := PartialFunctions.Pfn) f.val x).bind g.val ↔ y ∈ f.val x
    simp only [Part.mem_bind_iff,PartialFunctions.mem_rst]
    constructor
    · rintro ⟨v,⟨⟨w,hw⟩,hvx⟩,hy⟩
      subst v
      exact Part.mem_unique (h x w hw) hy ▸ hw
    · intro hy
      exact ⟨x,⟨⟨y,hy⟩,rfl⟩,h x y hy⟩

theorem compatible_iff {X Y : Object z} (f g : X ⟶ Y) :
    Compatible f g ↔ ∀ x a b,a ∈ f.val x → b ∈ g.val x → a = b := by
  constructor
  · intro h x a b ha hb
    have hm : b ∈ (rst f ≫ g).val x :=
      Part.mem_bind_iff.mpr ⟨x,(PartialFunctions.mem_rst f.val x x).mpr ⟨⟨a,ha⟩,rfl⟩,hb⟩
    rw [h] at hm
    obtain ⟨v,hv,hf⟩ := Part.mem_bind_iff.mp hm
    have hvx := ((PartialFunctions.mem_rst g.val x v).mp hv).2
    exact Part.mem_unique ha (hvx ▸ hf)
  · intro h
    apply hom_ext_mem
    intro x y
    change y ∈ (rst (C := PartialFunctions.Pfn) f.val x).bind g.val ↔
      y ∈ (rst (C := PartialFunctions.Pfn) g.val x).bind f.val
    simp only [Part.mem_bind_iff,PartialFunctions.mem_rst]
    constructor
    · rintro ⟨v,⟨⟨a,ha⟩,hvx⟩,hy⟩
      subst v
      exact ⟨x,⟨⟨y,hy⟩,rfl⟩,h x a y ha hy ▸ ha⟩
    · rintro ⟨v,⟨⟨b,hb⟩,hvx⟩,hy⟩
      subst v
      exact ⟨x,⟨⟨y,hy⟩,rfl⟩,(h x y b hy hb).symm ▸ hb⟩

private def unionRaw {α β : Type} (f g : α → Part β) (x : α) : Part β := by
  classical
  exact ⟨(f x).Dom ∨ (g x).Dom,fun h =>
    if hf : (f x).Dom then (f x).get hf else (g x).get (h.resolve_left hf)⟩

private theorem mem_unionRaw {α β : Type} (f g : α → Part β)
    (hc : ∀ x a b,a ∈ f x → b ∈ g x → a = b) (x : α) (y : β) :
    y ∈ unionRaw f g x ↔ y ∈ f x ∨ y ∈ g x := by
  classical
  constructor
  · intro hy
    obtain ⟨hd,he⟩ := Part.mem_mk_iff.mp hy
    by_cases hf : (f x).Dom
    · left
      have he' : (f x).get hf = y := by simpa only [unionRaw,dite_eq_left hf] using he
      exact he' ▸ Part.get_mem hf
    · right
      have he' : (g x).get (hd.resolve_left hf) = y := by simpa only [unionRaw,dite_eq_right hf] using he
      exact he' ▸ Part.get_mem _
  · intro h
    obtain h | h := h
    · refine Part.mem_mk_iff.mpr ⟨Or.inl h.1,?_⟩
      simpa only [unionRaw,dite_eq_left h.1] using h.2
    · refine Part.mem_mk_iff.mpr ⟨Or.inr h.1,?_⟩
      by_cases hf : (f x).Dom
      · simpa only [unionRaw,dite_eq_left hf] using hc x ((f x).get hf) y (Part.get_mem hf) h
      · simpa only [unionRaw,dite_eq_right hf] using h.2

def join {X Y : Object z} (f g : X ⟶ Y) (hc : Compatible f g) : X ⟶ Y :=
  ⟨unionRaw f.val g.val,(represented_iff_graph_enumerable z X.type Y.type _).mpr
    (((graph_enumerable f).or (graph_enumerable g)).of_eq
      (fun a => (mem_unionRaw f.val g.val ((compatible_iff f g).mp hc) a.1 a.2).symm))⟩

theorem join_graph {X Y : Object z} (f g : X ⟶ Y) (hc : Compatible f g)
    (x : carrier z X) (y : carrier z Y) :
    y ∈ (join f g hc).val x ↔ y ∈ f.val x ∨ y ∈ g.val x :=
  mem_unionRaw f.val g.val ((compatible_iff f g).mp hc) x y

theorem join_left {X Y : Object z} (f g : X ⟶ Y) (hc : Compatible f g) : Below f (join f g hc) :=
  (below_iff _ _).mpr (fun x y h => (join_graph f g hc x y).mpr (.inl h))

theorem join_right {X Y : Object z} (f g : X ⟶ Y) (hc : Compatible f g) : Below g (join f g hc) :=
  (below_iff _ _).mpr (fun x y h => (join_graph f g hc x y).mpr (.inr h))

theorem join_least {X Y : Object z} (f g h : X ⟶ Y) (hc : Compatible f g)
    (hf : Below f h) (hg : Below g h) : Below (join f g hc) h :=
  (below_iff _ _).mpr (fun x y hy => ((join_graph f g hc x y).mp hy).elim
    ((below_iff f h).mp hf x y) ((below_iff g h).mp hg x y))

theorem zero_below {X Y : Object z} (f : X ⟶ Y) : Below (0 : X ⟶ Y) f :=
  (below_iff _ _).mpr (fun _ _ h => h.1.elim)

theorem compatible_comp_left {W X Y : Object z} (h : W ⟶ X) (f g : X ⟶ Y)
    (hc : Compatible f g) : Compatible (h ≫ f) (h ≫ g) := by
  apply (compatible_iff _ _).mpr
  intro x a b ha hb
  obtain ⟨y,hy,ha⟩ := Part.mem_bind_iff.mp ha
  obtain ⟨y',hy',hb⟩ := Part.mem_bind_iff.mp hb
  have he : y' = y := Part.mem_unique hy' hy
  subst y'
  exact (compatible_iff f g).mp hc y a b ha hb

theorem compatible_comp_right {X Y Z : Object z} (f g : X ⟶ Y) (h : Y ⟶ Z)
    (hc : Compatible f g) : Compatible (f ≫ h) (g ≫ h) := by
  apply (compatible_iff _ _).mpr
  intro x a b ha hb
  obtain ⟨y,hy,ha⟩ := Part.mem_bind_iff.mp ha
  obtain ⟨y',hy',hb⟩ := Part.mem_bind_iff.mp hb
  have he : y = y' := (compatible_iff f g).mp hc x y y' hy hy'
  subst y'
  exact Part.mem_unique ha hb

theorem comp_join {W X Y : Object z} (h : W ⟶ X) (f g : X ⟶ Y) (hc : Compatible f g) :
    h ≫ join f g hc = join (h ≫ f) (h ≫ g) (compatible_comp_left h f g hc) := by
  apply hom_ext_mem
  intro x y
  simp only [comp_val,Part.mem_bind_iff,join_graph]
  aesop

theorem join_comp {X Y Z : Object z} (f g : X ⟶ Y) (h : Y ⟶ Z) (hc : Compatible f g) :
    join f g hc ≫ h = join (f ≫ h) (g ≫ h) (compatible_comp_right f g h hc) := by
  apply hom_ext_mem
  intro x y
  simp only [comp_val,Part.mem_bind_iff,join_graph]
  aesop

theorem compatible_of_disjoint {X Y : Object z} (f g : X ⟶ Y)
    (hd : Idem.ofRestrict f ⊓ Idem.ofRestrict g = ⊥) : Compatible f g := by
  apply (compatible_iff f g).mpr
  intro x a b ha hb
  have he := congrArg Idem.hom hd
  change rst f ≫ rst g = (0 : X ⟶ X) at he
  have hm : x ∈ (rst f ≫ rst g).val x := Part.mem_bind_iff.mpr
    ⟨x,(mem_identityOn X _ f.represented.domain x x).mpr ⟨ha.1,rfl⟩,
      (mem_identityOn X _ g.represented.domain x x).mpr ⟨hb.1,rfl⟩⟩
  rw [he] at hm
  exact hm.1.elim

instance disjointArrowJoins : DisjointArrowJoins (Object z) where
  exists_join f g hd :=
    ⟨join f g (compatible_of_disjoint f g hd),
      join_left f g (compatible_of_disjoint f g hd),
      join_right f g (compatible_of_disjoint f g hd),
      fun h hf hg => join_least f g h (compatible_of_disjoint f g hd) hf hg⟩

/-- This finite family hypothesis is exactly agreement of its actual
partial outputs where both are defined. It contains no oracle index
condition beyond the one already proved for every morphism. -/
def PairwiseCompatible {X Y : Object z} (L : List (X ⟶ Y)) : Prop :=
  ∀ f ∈ L,∀ g ∈ L,Compatible f g

private theorem finiteGraph_enumerable {X Y : Object z} (L : List (X ⟶ Y)) :
    Enumerable z (fun a : carrier z X × carrier z Y => ∃ f ∈ L,a.2 ∈ f.val a.1) := by
  induction L with
  | nil =>
    exact (Enumerable.of_re (REPred.const False)).of_eq (fun a => by simp)
  | cons f L ih =>
    exact ((graph_enumerable f).or ih).of_eq (fun a => by simp)

private def graphFunction {α β : Type} (P : α → β → Prop) (x : α) : Part β :=
  ⟨∃ y,P x y,fun h => Classical.choose h⟩

private theorem mem_graphFunction {α β : Type} (P : α → β → Prop)
    (hP : ∀ x a b,P x a → P x b → a=b) (x : α) (y : β) :
    y ∈ graphFunction P x ↔ P x y := by
  constructor
  · intro h
    obtain ⟨hd,he⟩ := Part.mem_mk_iff.mp h
    exact he ▸ Classical.choose_spec hd
  · intro h
    let hd : ∃ y,P x y := ⟨y,h⟩
    exact Part.mem_mk_iff.mpr ⟨hd,hP x _ y (Classical.choose_spec hd) h⟩

private theorem finiteGraph_functional {X Y : Object z} (L : List (X ⟶ Y))
    (hc : PairwiseCompatible L) (x : carrier z X) (a b : carrier z Y)
    (ha : ∃ f ∈ L,a ∈ f.val x) (hb : ∃ g ∈ L,b ∈ g.val x) : a=b := by
  obtain ⟨f,hf,ha⟩ := ha
  obtain ⟨g,hg,hb⟩ := hb
  exact (compatible_iff f g).mp (hc f hf g hg) x a b ha hb

def finiteJoin {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) : X ⟶ Y :=
  ⟨graphFunction (fun x y => ∃ f ∈ L,y ∈ f.val x),
    (represented_iff_graph_enumerable z X.type Y.type _).mpr
      ((finiteGraph_enumerable L).of_eq (fun a =>
        (mem_graphFunction _ (finiteGraph_functional L hc) a.1 a.2).symm))⟩

theorem finiteJoin_graph {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L)
    (x : carrier z X) (y : carrier z Y) :
    y ∈ (finiteJoin L hc).val x ↔ ∃ f ∈ L,y ∈ f.val x :=
  mem_graphFunction _ (finiteGraph_functional L hc) x y

theorem le_finiteJoin {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L)
    (f : X ⟶ Y) (hf : f ∈ L) : Below f (finiteJoin L hc) :=
  (below_iff _ _).mpr (fun x y hy => (finiteJoin_graph L hc x y).mpr ⟨f,hf,hy⟩)

theorem finiteJoin_least {X Y : Object z} (L : List (X ⟶ Y)) (hc : PairwiseCompatible L)
    (h : X ⟶ Y) (hh : ∀ f ∈ L,Below f h) : Below (finiteJoin L hc) h := by
  apply (below_iff _ _).mpr
  intro x y hy
  obtain ⟨f,hf,hy⟩ := (finiteJoin_graph L hc x y).mp hy
  exact (below_iff _ _).mp (hh f hf) x y hy

theorem finiteJoin_nil {X Y : Object z} (hc : PairwiseCompatible ([] : List (X ⟶ Y))) :
    finiteJoin [] hc = (0 : X ⟶ Y) := by
  apply hom_ext_mem
  intro x y
  simp only [finiteJoin_graph,List.not_mem_nil,false_and,exists_false,zero_val,Part.notMem_none]

theorem pairwiseCompatible_comp_left {W X Y : Object z} (h : W ⟶ X)
    (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    PairwiseCompatible (L.map (fun f => h ≫ f)) := by
  intro f' hf' g' hg'
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hf'
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg'
  exact compatible_comp_left h f g (hc f hf g hg)

theorem pairwiseCompatible_comp_right {X Y Z : Object z} (L : List (X ⟶ Y))
    (h : Y ⟶ Z) (hc : PairwiseCompatible L) :
    PairwiseCompatible (L.map (fun f => f ≫ h)) := by
  intro f' hf' g' hg'
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hf'
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg'
  exact compatible_comp_right f g h (hc f hf g hg)

theorem comp_finiteJoin {W X Y : Object z} (h : W ⟶ X)
    (L : List (X ⟶ Y)) (hc : PairwiseCompatible L) :
    h ≫ finiteJoin L hc =
      finiteJoin (L.map (fun f => h ≫ f)) (pairwiseCompatible_comp_left h L hc) := by
  apply hom_ext_mem
  intro x y
  simp only [mem_comp,finiteJoin_graph,List.mem_map]
  aesop

theorem finiteJoin_comp {X Y Z : Object z} (L : List (X ⟶ Y))
    (h : Y ⟶ Z) (hc : PairwiseCompatible L) :
    finiteJoin L hc ≫ h =
      finiteJoin (L.map (fun f => f ≫ h)) (pairwiseCompatible_comp_right L h hc) := by
  apply hom_ext_mem
  intro x y
  simp only [mem_comp,finiteJoin_graph,List.mem_map]
  aesop

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
