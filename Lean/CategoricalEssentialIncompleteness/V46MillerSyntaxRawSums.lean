/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw
public import Mathlib.CategoryTheory.Limits.Over

/-! # Literal tagged sums in every uniform parameter slice

The outer pair stores the common parameter. The inner pair stores the
ordered value and tag 0 or 1. Copairing uses the supplied supported
uniform morphisms themselves, including their partial values off their
source carriers; no total recursive extension is required.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family}

def sumTag (n : ℕ) : ℕ := (Nat.unpair (Nat.unpair n).2).2
def sumChild (n : ℕ) : ℕ := Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1
def sumLift (i n : ℕ) : ℕ := Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 i)

theorem sumChild_lift (i n : ℕ) : sumChild (sumLift i n)=n := by
  simp only [sumChild,sumLift,Nat.unpair_pair,Nat.pair_unpair]

theorem sumTag_lift (i n : ℕ) : sumTag (sumLift i n)=i := by
  simp only [sumTag,sumLift,Nat.unpair_pair]

theorem sumLift_rebuild (n : ℕ) : sumLift (sumTag n) (sumChild n)=n := by
  simp only [sumLift,sumTag,sumChild,Nat.unpair_pair,Nat.pair_unpair]

theorem sumChild_computable : Computable sumChild :=
  Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.unpair)
    (Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair)))

theorem sumTag_primrec : Primrec sumTag :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

def sumCopairValue (f g : ℕ → Part ℕ) (n : ℕ) : Part ℕ :=
  if sumTag n=0 then f (sumChild n)
  else if sumTag n=1 then g (sumChild n) else Part.none

theorem mem_sumCopairValue (f g : ℕ → Part ℕ) (n m : ℕ) :
    m∈sumCopairValue f g n ↔
      (sumTag n=0 ∧ m∈f (sumChild n)) ∨ (sumTag n=1 ∧ m∈g (sumChild n)) := by
  by_cases h0 : sumTag n=0
  · have h1 : sumTag n≠1 := by omega
    simp [sumCopairValue,h0]
  · by_cases h1 : sumTag n=1 <;> simp [sumCopairValue,h0,h1]

theorem sumCopairValue_represented (f g : ℕ → Part ℕ)
    (hf : Uniform.Represented P .nat .nat f) (hg : Uniform.Represented P .nat .nat g) :
    Uniform.Represented P .nat .nat (sumCopairValue f g) := by
  have hd : Computable (fun a : ℕ×ℕ => (sumChild a.1,a.2)) :=
    Computable.pair (sumChild_computable.comp Computable.fst) Computable.snd
  have h0 : REPred (fun a : ℕ×ℕ => sumTag a.1=0) :=
    (Primrec.eq.comp (sumTag_primrec.comp Primrec.fst) (.const 0)).computablePred.to_re
  have h1 : REPred (fun a : ℕ×ℕ => sumTag a.1=1) :=
    (Primrec.eq.comp (sumTag_primrec.comp Primrec.fst) (.const 1)).computablePred.to_re
  have ef := Uniform.Enumerable.comp hd
    ((Uniform.represented_iff_graph_enumerable P .nat .nat f).mp hf)
  have eg := Uniform.Enumerable.comp hd
    ((Uniform.represented_iff_graph_enumerable P .nat .nat g).mp hg)
  apply (Uniform.represented_iff_graph_enumerable P .nat .nat _).mpr
  exact (((Uniform.Enumerable.of_re h0).and ef).or
    ((Uniform.Enumerable.of_re h1).and eg)).of_eq
      (fun a => (mem_sumCopairValue f g a.1 a.2).symm)

variable (R : Total.TotalCategory P) (X Y : Over R) (a b : SyntaxPolynomial (Total.TotalCategory P))

def sumCopairArrow {Z : Total.TotalCategory P}
    (f : (object R X Y a).left ⟶ Z) (g : (object R X Y b).left ⟶ Z) :
    (fiberCarrier R X Y (.sum a b)) ⟶ Z.obj :=
  Total.arrow (sumCopairValue (Total.val f.hom) (Total.val g.hom))
    (sumCopairValue_represented _ _ (Total.val_represented f.hom) (Total.val_represented g.hom))
    (by
      intro n m hm
      change fiber R X Y (.sum a b) (Nat.unpair n)
      rcases (mem_sumCopairValue _ _ n m).mp hm with ⟨ht,hf⟩ | ⟨ht,hg⟩
      · have hs := Total.val_source f.hom _ _ hf
        have ha : fiber R X Y a ((Nat.unpair n).1,(Nat.unpair (Nat.unpair n).2).1) := by
          change fiber R X Y a (Nat.unpair (sumChild n)) at hs
          simpa only [sumChild,Nat.unpair_pair] using hs
        exact Or.inl ⟨ht,ha⟩
      · have hs := Total.val_source g.hom _ _ hg
        have hb : fiber R X Y b ((Nat.unpair n).1,(Nat.unpair (Nat.unpair n).2).1) := by
          change fiber R X Y b (Nat.unpair (sumChild n)) at hs
          simpa only [sumChild,Nat.unpair_pair] using hs
        exact Or.inr ⟨ht,hb⟩)
    (by
      intro n m hm
      exact ((mem_sumCopairValue _ _ n m).mp hm).elim
        (fun h => Total.val_target f.hom _ _ h.2)
        (fun h => Total.val_target g.hom _ _ h.2))

theorem sumCopairArrow_total {Z : Total.TotalCategory P}
    (f : (object R X Y a).left ⟶ Z) (g : (object R X Y b).left ⟶ Z) :
    isTotal (sumCopairArrow R X Y a b f g) := by
  apply (Total.total_iff _).mpr
  intro n hn
  change fiber R X Y (.sum a b) (Nat.unpair n) at hn
  rcases hn with ⟨ht,ha⟩ | ⟨ht,hb⟩
  · have hs : sumChild n∈(fiberCarrier R X Y a).support := by
      change fiber R X Y a (Nat.unpair (sumChild n))
      simpa only [sumChild,Nat.unpair_pair] using ha
    obtain ⟨m,hm⟩ := Part.dom_iff_mem.mp ((Total.total_iff f.hom).mp f.property _ hs)
    exact Part.dom_iff_mem.mpr ⟨m,(mem_sumCopairValue _ _ n m).mpr (Or.inl ⟨ht,hm⟩)⟩
  · have hs : sumChild n∈(fiberCarrier R X Y b).support := by
      change fiber R X Y b (Nat.unpair (sumChild n))
      simpa only [sumChild,Nat.unpair_pair] using hb
    obtain ⟨m,hm⟩ := Part.dom_iff_mem.mp ((Total.total_iff g.hom).mp g.property _ hs)
    exact Part.dom_iff_mem.mpr ⟨m,(mem_sumCopairValue _ _ n m).mpr (Or.inr ⟨ht,hm⟩)⟩

def sumCopairTotal {Z : Total.TotalCategory P}
    (f : (object R X Y a).left ⟶ Z) (g : (object R X Y b).left ⟶ Z) :
    (object R X Y (.sum a b)).left ⟶ Z :=
  ⟨sumCopairArrow R X Y a b f g,sumCopairArrow_total R X Y a b f g⟩

theorem sumCopairTotal_graph {Z : Total.TotalCategory P}
    (f : (object R X Y a).left ⟶ Z) (g : (object R X Y b).left ⟶ Z) (n m : ℕ) :
    m∈Total.val (sumCopairTotal R X Y a b f g).hom n ↔
      (sumTag n=0 ∧ m∈Total.val f.hom (sumChild n)) ∨
      (sumTag n=1 ∧ m∈Total.val g.hom (sumChild n)) := mem_sumCopairValue _ _ _ _

theorem sumInl_value (n : ℕ) (hn : n∈(fiberCarrier R X Y a).support) :
    Total.val (sumInl R X Y a b).left.hom n=Part.some (sumLift 0 n) := by
  apply Part.eq_some_iff.mpr
  simpa only [Nat.pair_unpair] using
    (sumInl_graph R X Y a b (Nat.unpair n).1 (Nat.unpair n).2 (sumLift 0 n)).mpr ⟨hn,rfl⟩

theorem sumInr_value (n : ℕ) (hn : n∈(fiberCarrier R X Y b).support) :
    Total.val (sumInr R X Y a b).left.hom n=Part.some (sumLift 1 n) := by
  apply Part.eq_some_iff.mpr
  simpa only [Nat.pair_unpair] using
    (sumInr_graph R X Y a b (Nat.unpair n).1 (Nat.unpair n).2 (sumLift 1 n)).mpr ⟨hn,rfl⟩

theorem sumInl_copairTotal {Z : Total.TotalCategory P}
    (f : (object R X Y a).left ⟶ Z) (g : (object R X Y b).left ⟶ Z) :
    (sumInl R X Y a b).left ≫ sumCopairTotal R X Y a b f g=f := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  change Total.val ((sumInl R X Y a b).left.hom ≫
    (sumCopairTotal R X Y a b f g).hom) n=Total.val f.hom n
  rw [Total.val_comp,sumInl_value R X Y a b n hn,Part.bind_some]
  change sumCopairValue (Total.val f.hom) (Total.val g.hom) (sumLift 0 n)=_
  simp [sumCopairValue,sumTag_lift,sumChild_lift]

theorem sumInr_copairTotal {Z : Total.TotalCategory P}
    (f : (object R X Y a).left ⟶ Z) (g : (object R X Y b).left ⟶ Z) :
    (sumInr R X Y a b).left ≫ sumCopairTotal R X Y a b f g=g := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  change Total.val ((sumInr R X Y a b).left.hom ≫
    (sumCopairTotal R X Y a b f g).hom) n=Total.val g.hom n
  rw [Total.val_comp,sumInr_value R X Y a b n hn,Part.bind_some]
  change sumCopairValue (Total.val f.hom) (Total.val g.hom) (sumLift 1 n)=_
  simp [sumCopairValue,sumTag_lift,sumChild_lift]

/-- Arbitrary total targets and morphisms, proved by ordered tag decoding. -/
theorem sum_total_hom_ext {Z : Total.TotalCategory P}
    {f g : (object R X Y (.sum a b)).left ⟶ Z}
    (hl : (sumInl R X Y a b).left ≫ f=(sumInl R X Y a b).left ≫ g)
    (hr : (sumInr R X Y a b).left ≫ f=(sumInr R X Y a b).left ≫ g) : f=g := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  change fiber R X Y (.sum a b) (Nat.unpair n) at hn
  rcases hn with ⟨ht,ha⟩ | ⟨ht,hb⟩
  · have hs : sumChild n∈(fiberCarrier R X Y a).support := by
      change fiber R X Y a (Nat.unpair (sumChild n))
      simpa only [sumChild,Nat.unpair_pair] using ha
    have hv := congrArg (fun h => Total.val h.hom (sumChild n)) hl
    change Total.val ((sumInl R X Y a b).left.hom ≫ f.hom) (sumChild n)=
      Total.val ((sumInl R X Y a b).left.hom ≫ g.hom) (sumChild n) at hv
    rw [Total.val_comp,Total.val_comp,sumInl_value R X Y a b _ hs,
      Part.bind_some,Part.bind_some] at hv
    have he : sumLift 0 (sumChild n)=n := by
      have he := sumLift_rebuild n
      rwa [show sumTag n=0 from ht] at he
    rwa [he] at hv
  · have hs : sumChild n∈(fiberCarrier R X Y b).support := by
      change fiber R X Y b (Nat.unpair (sumChild n))
      simpa only [sumChild,Nat.unpair_pair] using hb
    have hv := congrArg (fun h => Total.val h.hom (sumChild n)) hr
    change Total.val ((sumInr R X Y a b).left.hom ≫ f.hom) (sumChild n)=
      Total.val ((sumInr R X Y a b).left.hom ≫ g.hom) (sumChild n) at hv
    rw [Total.val_comp,Total.val_comp,sumInr_value R X Y a b _ hs,
      Part.bind_some,Part.bind_some] at hv
    have he : sumLift 1 (sumChild n)=n := by
      have he := sumLift_rebuild n
      rwa [show sumTag n=1 from ht] at he
    rwa [he] at hv

def sumCopair {Z : Over R} (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) :
    object R X Y (.sum a b) ⟶ Z :=
  Over.homMk (sumCopairTotal R X Y a b f.left g.left) (by
    apply sum_total_hom_ext R X Y a b
    · calc
        (sumInl R X Y a b).left ≫ (sumCopairTotal R X Y a b f.left g.left ≫ Z.hom) =
            ((sumInl R X Y a b).left ≫ sumCopairTotal R X Y a b f.left g.left) ≫ Z.hom :=
          (Category.assoc _ _ _).symm
        _ = f.left ≫ Z.hom := congrArg (fun h => h ≫ Z.hom) (sumInl_copairTotal R X Y a b _ _)
        _ = (object R X Y a).hom := f.w
        _ = (sumInl R X Y a b).left ≫ (object R X Y (.sum a b)).hom := (sumInl R X Y a b).w.symm
    · calc
        (sumInr R X Y a b).left ≫ (sumCopairTotal R X Y a b f.left g.left ≫ Z.hom) =
            ((sumInr R X Y a b).left ≫ sumCopairTotal R X Y a b f.left g.left) ≫ Z.hom :=
          (Category.assoc _ _ _).symm
        _ = g.left ≫ Z.hom := congrArg (fun h => h ≫ Z.hom) (sumInr_copairTotal R X Y a b _ _)
        _ = (object R X Y b).hom := g.w
        _ = (sumInr R X Y a b).left ≫ (object R X Y (.sum a b)).hom := (sumInr R X Y a b).w.symm)

theorem sumCopair_graph {Z : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) (n m : ℕ) :
    m∈Total.val (sumCopair R X Y a b f g).left.hom n ↔
      (sumTag n=0 ∧ m∈Total.val f.left.hom (sumChild n)) ∨
      (sumTag n=1 ∧ m∈Total.val g.left.hom (sumChild n)) :=
  sumCopairTotal_graph R X Y a b f.left g.left n m

theorem sumCopair_inl_graph {Z : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) (r u m : ℕ) :
    m∈Total.val (sumCopair R X Y a b f g).left.hom (Nat.pair r (Nat.pair u 0)) ↔
      m∈Total.val f.left.hom (Nat.pair r u) := by
  simp only [sumCopair_graph,sumTag,sumChild,Nat.unpair_pair]
  simp

theorem sumCopair_inr_graph {Z : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) (r u m : ℕ) :
    m∈Total.val (sumCopair R X Y a b f g).left.hom (Nat.pair r (Nat.pair u 1)) ↔
      m∈Total.val g.left.hom (Nat.pair r u) := by
  simp only [sumCopair_graph,sumTag,sumChild,Nat.unpair_pair]
  simp

theorem sumCopair_domain {Z : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) (n : ℕ) :
    (Total.val (sumCopair R X Y a b f g).left.hom n).Dom ↔
      fiber R X Y (.sum a b) (Nat.unpair n) := by
  constructor
  · intro h
    obtain ⟨m,hm⟩ := Part.dom_iff_mem.mp h
    exact Total.val_source (sumCopair R X Y a b f g).left.hom n m hm
  · intro hn
    exact (Total.total_iff (sumCopair R X Y a b f g).left.hom).mp
      (sumCopair R X Y a b f g).left.property n hn

theorem sumCopair_parameter {Z : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) :
    (sumCopair R X Y a b f g).left ≫ Z.hom=projection R X Y (.sum a b) :=
  (sumCopair R X Y a b f g).w

theorem sumCopair_invalidTag {Z : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) (n : ℕ)
    (h0 : sumTag n≠0) (h1 : sumTag n≠1) :
    Total.val (sumCopair R X Y a b f g).left.hom n=Part.none := by
  change sumCopairValue (Total.val f.left.hom) (Total.val g.left.hom) n=Part.none
  simp only [sumCopairValue,ite_eq_right h0,ite_eq_right h1]

theorem sumInl_copair {Z : Over R} (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) :
    sumInl R X Y a b ≫ sumCopair R X Y a b f g=f := by
  apply Over.OverMorphism.ext
  exact sumInl_copairTotal R X Y a b f.left g.left

theorem sumInr_copair {Z : Over R} (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) :
    sumInr R X Y a b ≫ sumCopair R X Y a b f g=g := by
  apply Over.OverMorphism.ext
  exact sumInr_copairTotal R X Y a b f.left g.left

theorem sum_hom_ext {Z : Over R} {f g : object R X Y (.sum a b) ⟶ Z}
    (hl : sumInl R X Y a b ≫ f=sumInl R X Y a b ≫ g)
    (hr : sumInr R X Y a b ≫ f=sumInr R X Y a b ≫ g) : f=g := by
  apply Over.OverMorphism.ext
  exact sum_total_hom_ext R X Y a b
    (congrArg (fun h => h.left) hl) (congrArg (fun h => h.left) hr)

theorem sumCopair_comp {Z W : Over R}
    (f : object R X Y a ⟶ Z) (g : object R X Y b ⟶ Z) (h : Z ⟶ W) :
    sumCopair R X Y a b f g ≫ h=sumCopair R X Y a b (f ≫ h) (g ≫ h) := by
  apply sum_hom_ext R X Y a b
  · rw [← Category.assoc,sumInl_copair,sumInl_copair]
  · rw [← Category.assoc,sumInr_copair,sumInr_copair]

/-- The actual raw tagged object has the full universal property in Over R. -/
def sumIsColimit : IsColimit (BinaryCofan.mk (sumInl R X Y a b) (sumInr R X Y a b)) :=
  BinaryCofan.isColimitMk (fun s => sumCopair R X Y a b s.inl s.inr)
    (fun s => sumInl_copair R X Y a b s.inl s.inr)
    (fun s => sumInr_copair R X Y a b s.inl s.inr) (by
      intro s m h0 h1
      apply sum_hom_ext R X Y a b
      · exact h0.trans (sumInl_copair R X Y a b s.inl s.inr).symm
      · exact h1.trans (sumInr_copair R X Y a b s.inl s.inr).symm)

/-- Comparison to the chosen slice coproduct preserves both ordered tags. -/
def sumIso : object R X Y (.sum a b) ≅ (object R X Y a ⨿ object R X Y b) where
  hom := sumCopair R X Y a b coprod.inl coprod.inr
  inv := coprod.desc (sumInl R X Y a b) (sumInr R X Y a b)
  hom_inv_id := by
    apply sum_hom_ext R X Y a b
    · rw [← Category.assoc,sumInl_copair,coprod.inl_desc,Category.comp_id]
    · rw [← Category.assoc,sumInr_copair,coprod.inr_desc,Category.comp_id]
  inv_hom_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc,coprod.inl_desc,sumInl_copair,Category.comp_id]
    · rw [← Category.assoc,coprod.inr_desc,sumInr_copair,Category.comp_id]

theorem sumIso_inl : sumInl R X Y a b ≫ (sumIso R X Y a b).hom=coprod.inl :=
  sumInl_copair R X Y a b _ _

theorem sumIso_inr : sumInr R X Y a b ≫ (sumIso R X Y a b).hom=coprod.inr :=
  sumInr_copair R X Y a b _ _

theorem sumIso_inv_inl : coprod.inl ≫ (sumIso R X Y a b).inv=sumInl R X Y a b :=
  coprod.inl_desc _ _

theorem sumIso_inv_inr : coprod.inr ≫ (sumIso R X Y a b).inv=sumInr R X Y a b :=
  coprod.inr_desc _ _

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
