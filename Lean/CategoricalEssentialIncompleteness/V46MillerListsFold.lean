/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsEvaluation

/-! # Parameter-preserving list folds and compatible-map uniqueness

Both list constructors are evaluated through uniformly represented operations. The
uniqueness theorem covers every candidate morphism with the original nil and adjoin
equations; no ordinary-recursive extension or inhabited target is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open SyntacticSyntax.NatVectors Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X : Over R} (V : Total.Carrier P)
variable (h0 : Syntax.Raw.object R X X .unit ⟶ X)
variable (hc : Syntax.Raw.object R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ X)

def evaluation (x : ℕ) : Part ℕ :=
  ⟨∃ v,Evaluates V h0 hc (Nat.unpair x).1 (Nat.natToList (Nat.unpair x).2) v,fun h => Classical.choose h⟩

theorem mem_evaluation (x v : ℕ) : v ∈ evaluation V h0 hc x ↔
    Evaluates V h0 hc (Nat.unpair x).1 (Nat.natToList (Nat.unpair x).2) v := by
  constructor
  · intro hv
    obtain ⟨hd,he⟩ := Part.mem_mk_iff.mp hv
    exact he ▸ Classical.choose_spec hd
  · intro hv
    let hd : ∃ v,Evaluates V h0 hc (Nat.unpair x).1 (Nat.natToList (Nat.unpair x).2) v := ⟨v,hv⟩
    exact Part.mem_mk_iff.mpr ⟨hd,evaluates_functional V h0 hc (Classical.choose_spec hd) hv⟩

theorem evaluation_represented : Uniform.Represented P .nat .nat (evaluation V h0 hc) := by
  have hc' : Computable (fun a : ℕ × ℕ =>
      (((Nat.unpair a.1).1,Nat.natToList (Nat.unpair a.1).2),a.2)) :=
    (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
      (Primrec.nat_natToList.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))) Primrec.snd).to_comp
  exact (Uniform.represented_iff_graph_enumerable P .nat .nat _).mpr
    ((Uniform.Enumerable.comp hc' (evaluates_enumerable V h0 hc)).of_eq
      (fun a => (mem_evaluation V h0 hc a.1 a.2).symm))

def foldArrow : (family R V).left.obj ⟶ X.left.obj :=
  Total.arrow (evaluation V h0 hc) (evaluation_represented V h0 hc) (by
    intro x v hv
    have hs := evaluates_source V h0 hc ((mem_evaluation V h0 hc x v).mp hv)
    exact hs) (by
    intro x v hv
    exact Total.val_source X.hom.hom _ _
      (evaluates_fiber V h0 hc ((mem_evaluation V h0 hc x v).mp hv)))

theorem foldArrow_total : isTotal (foldArrow V h0 hc) := by
  apply (Total.total_iff _).mpr
  intro x hx
  obtain ⟨v,hv⟩ := evaluates_exists V h0 hc (Nat.unpair x).1 (Nat.natToList (Nat.unpair x).2) hx.1 hx.2
  exact Part.dom_iff_mem.mpr ⟨v,(mem_evaluation V h0 hc x v).mpr hv⟩

def foldLeft : (family R V).left ⟶ X.left := ⟨foldArrow V h0 hc,foldArrow_total V h0 hc⟩

theorem fold_parameter : foldLeft V h0 hc ≫ X.hom=(family R V).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff _).mp (foldArrow_total V h0 hc) x hx)
  have hp := evaluates_fiber V h0 hc ((mem_evaluation V h0 hc x v).mp hv)
  have he : Total.val (foldLeft V h0 hc).hom x=Part.some v := Part.eq_some_iff.mpr hv
  have hep : Total.val X.hom.hom v=Part.some (Nat.unpair x).1 := Part.eq_some_iff.mpr hp
  have hes : Total.val (family R V).hom.hom x=Part.some (Nat.unpair x).1 :=
    Part.eq_some_iff.mpr ((Total.mem_partialFst _ _ x _).mpr ⟨hx,rfl⟩)
  change Total.val ((foldLeft V h0 hc).hom ≫ X.hom.hom) x =
    Total.val (family R V).hom.hom x
  rw [Total.val_comp,he,Part.bind_some,hep,hes]

def fold : family R V ⟶ X := Over.homMk (foldLeft V h0 hc) (fold_parameter V h0 hc)

theorem fold_graph (r list value : ℕ) :
    value ∈ Total.val (fold V h0 hc).left.hom (Nat.pair r list) ↔
      Evaluates V h0 hc r (Nat.natToList list) value := by
  change value ∈ evaluation V h0 hc (Nat.pair r list) ↔ _
  simpa only [Nat.unpair_pair] using mem_evaluation V h0 hc (Nat.pair r list) value

theorem fold_nil (r value : ℕ) :
    value ∈ Total.val (fold V h0 hc).left.hom (Nat.pair r 0) ↔ value ∈ operation h0 (r,0) := by
  rw [fold_graph]
  simp only [Nat.natToList]
  constructor
  · intro h;cases h with | nil hv => exact hv
  · exact fun hv => .nil hv

theorem fold_adjoin (r a list value : ℕ) :
    value ∈ Total.val (fold V h0 hc).left.hom (Nat.pair r (adjoin a list)) ↔
      ∃ tailValue,tailValue ∈ Total.val (fold V h0 hc).left.hom (Nat.pair r list) ∧
        value ∈ operation hc (r,Nat.pair a tailValue) := by
  simp only [fold_graph,natToList_adjoin]
  constructor
  · intro h;cases h with | cons ht hv => exact ⟨_,ht,hv⟩
  · rintro ⟨w,hw,hv⟩;exact .cons hw hv

/-- These are the scalar forms of the literal nil/adjoin constructor squares for any
candidate morphism. No existence or uniqueness of the candidate is assumed. -/
theorem fold_unique (f : family R V ⟶ X)
    (hzero : ∀ r ∈ R.obj.support,∀ value,
      value ∈ Total.val f.left.hom (Nat.pair r 0) ↔ value ∈ operation h0 (r,0))
    (hcons : ∀ r ∈ R.obj.support,∀ a ∈ V.support,∀ list ∈ (carrier V).support,∀ value,
      value ∈ Total.val f.left.hom (Nat.pair r (adjoin a list)) ↔
        ∃ w,w ∈ Total.val f.left.hom (Nat.pair r list) ∧ value ∈ operation hc (r,Nat.pair a w)) :
    f=fold V h0 hc := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  have aux : ∀ L : List ℕ,(∀ a ∈ L,a ∈ V.support) → ∀ value,
      value ∈ Total.val f.left.hom (Nat.pair (Nat.unpair x).1 (pack L)) ↔
        Evaluates V h0 hc (Nat.unpair x).1 L value := by
    intro L
    induction L with
    | nil =>
        intro _ value
        rw [pack_nil,hzero (Nat.unpair x).1 hx.1 value]
        constructor
        · intro hv;exact .nil hv
        · intro h;cases h with | nil hv => exact hv
    | cons a L ih =>
        intro hL value
        have hmem := List.forall_mem_cons.mp hL
        have hp : pack (a::L)=adjoin a (pack L) := by
          simp [pack,FiniteSigmaOne.canonical_adjoin,nat_pair_eq]
        rw [hp,hcons (Nat.unpair x).1 hx.1 a hmem.1 (pack L) ((pack_mem V L).mpr hmem.2) value]
        simp only [ih hmem.2]
        constructor
        · rintro ⟨w,hw,hv⟩;exact .cons hw hv
        · intro h;cases h with | cons hw hv => exact ⟨_,hw,hv⟩
  apply Part.ext
  intro value
  have he := aux (Nat.natToList (Nat.unpair x).2) hx.2 value
  change value ∈ Total.val f.left.hom x ↔ value ∈ evaluation V h0 hc x
  simpa only [pack_natToList,Nat.pair_unpair] using he.trans (mem_evaluation V h0 hc x value).symm

end CategoricalEssentialIncompleteness.V46.Miller.Lists
