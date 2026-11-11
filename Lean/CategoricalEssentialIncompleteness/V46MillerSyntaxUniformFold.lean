/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxCarriers
public import CategoricalEssentialIncompleteness.V46MillerSyntaxFold

/-! # Actual slice fold morphisms for arbitrary uniformly enumerable coefficients

Both the coefficient objects and the target families are arbitrary.
Totality follows from the constructed positive-record evaluator and its
singleton simulation. The source is the unchanged successful postfix
word, paired only with the external parameter.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

def uniformSelectedValue (x : ℕ) : Part ℕ := (evaluation hT hF x).map extract

theorem uniformSelectedValue_represented : Uniform.Represented P .nat .nat (uniformSelectedValue hT hF) := by
  have he : Uniform.Represented P .nat .nat (fun x : ℕ => Part.some (extract x)) :=
    Uniform.Represented.of_partrec extract_primrec.to_comp.partrec
  apply (Uniform.Represented.comp (evaluation_represented hT hF) he).of_eq
  intro x
  change (evaluation hT hF x).bind (fun z : ℕ => Part.some (extract z)) =
    (evaluation hT hF x).map extract
  exact Part.bind_some_eq_map extract (evaluation hT hF x)

theorem uniformSelectedValue_fiber (formula : Bool) {r word value : ℕ}
    (hr : r ∈ R.obj.support) (hw : word ∈ (uniformWords formula p q).support)
    (hv : value ∈ uniformSelectedValue hT hF (Nat.pair r word)) :
    r ∈ Total.val (if formula then Y else X).hom.hom value := by
  obtain ⟨s,hs,hvalue⟩ := (Part.mem_map_iff _).mp hv
  obtain ⟨v,he⟩ := uniformWords_singleton hT hF formula hw hs
  have hsI := evaluation_status hT hF (uniformWords_coefficientWord formula p q r word hr hw) hs
  rw [he] at hsI hvalue
  have hvv : v=value := by simpa only [extract_singleton] using hvalue
  rw [← hvv]
  simp only [Nat.unpair_pair] at hsI
  have hst := ((status_succ R X Y r _).mp hsI).2
  have hb := ((fiberStack_adjoin R X Y r _ 0).mp hst).1
  cases formula
  · exact (fiberBlock_term R X Y r v).mp hb
  · exact (fiberBlock_formula R X Y r v).mp hb

def uniformFoldArrow (formula : Bool) :
    (uniformWordFamily R formula p q).left.obj ⟶ (if formula then Y else X).left.obj :=
  let r : Uniform.N P ⟶ Uniform.N P := ⟨uniformSelectedValue hT hF,uniformSelectedValue_represented hT hF⟩
  let k := Uniform.identityOn (Uniform.N P) (uniformWordFamily R formula p q).left.obj.support
    (uniformWordFamily R formula p q).left.obj.enumerable ≫ r
  Total.arrow k.val k.represented (by
    intro x y hy
    obtain ⟨u,hu,_⟩ := Part.mem_bind_iff.mp hy
    exact ((Total.mem_supportIdentity _ x u).mp hu).1) (by
    intro x y hy
    obtain ⟨u,hu,huy⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨hx,hux⟩ := (Total.mem_supportIdentity _ x u).mp hu
    subst u
    have hf := uniformSelectedValue_fiber hT hF formula hx.1 hx.2
      (by simpa only [Nat.pair_unpair] using huy)
    cases formula
    · exact Total.val_source X.hom.hom _ _ hf
    · exact Total.val_source Y.hom.hom _ _ hf)

theorem uniformFoldArrow_graph (formula : Bool) (x y : ℕ) :
    y ∈ Total.val (uniformFoldArrow hT hF formula) x ↔
      x ∈ (uniformWordFamily R formula p q).left.obj.support ∧ y ∈ uniformSelectedValue hT hF x := by
  change y ∈ (Total.supportIdentity _ x).bind (uniformSelectedValue hT hF) ↔ _
  simp only [Part.mem_bind_iff,Total.mem_supportIdentity]
  aesop

theorem uniformFoldArrow_total (formula : Bool) : isTotal (uniformFoldArrow hT hF formula) := by
  apply (Total.total_iff _).mpr
  intro x hx
  obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp (evaluation_total hT hF
    (uniformWords_coefficientWord formula p q (Nat.unpair x).1 (Nat.unpair x).2 hx.1 hx.2))
  exact Part.dom_iff_mem.mpr ⟨extract s,(uniformFoldArrow_graph hT hF formula x _).mpr
    ⟨hx,(Part.mem_map_iff _).mpr ⟨s,by simpa only [Nat.pair_unpair] using hs,rfl⟩⟩⟩

def uniformFoldLeft (formula : Bool) :
    (uniformWordFamily R formula p q).left ⟶ (if formula then Y else X).left :=
  ⟨uniformFoldArrow hT hF formula,uniformFoldArrow_total hT hF formula⟩

theorem uniformFold_parameter (formula : Bool) :
    uniformFoldLeft hT hF formula ≫ (if formula then Y else X).hom=
      (uniformWordFamily R formula p q).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((Total.total_iff _).mp
    (uniformFoldLeft hT hF formula).property x hx)
  have hvalue := ((uniformFoldArrow_graph hT hF formula x y).mp hy).2
  have hp := uniformSelectedValue_fiber hT hF formula hx.1 hx.2
    (by simpa only [Nat.pair_unpair] using hvalue)
  have hyEq : Total.val (uniformFoldLeft hT hF formula).hom x=Part.some y := Part.eq_some_iff.mpr hy
  have hpEq : Total.val (if formula then Y else X).hom.hom y=Part.some (Nat.unpair x).1 :=
    Part.eq_some_iff.mpr hp
  have hxEq : Total.val (uniformWordFamily R formula p q).hom.hom x=Part.some (Nat.unpair x).1 :=
    Part.eq_some_iff.mpr ((Total.mem_partialFst _ _ x _).mpr ⟨hx,rfl⟩)
  change Total.val ((uniformFoldLeft hT hF formula).hom ≫ (if formula then Y else X).hom.hom) x =
    Total.val (uniformWordFamily R formula p q).hom.hom x
  rw [Total.val_comp,hyEq,Part.bind_some,hpEq,hxEq]

def uniformFold (formula : Bool) : uniformWordFamily R formula p q ⟶ (if formula then Y else X) :=
  Over.homMk (uniformFoldLeft hT hF formula) (uniformFold_parameter hT hF formula)

@[simp] theorem uniformWordFamily_support (formula : Bool) (r word : ℕ) :
    Nat.pair r word ∈ (uniformWordFamily R formula p q).left.obj.support ↔
      r ∈ R.obj.support ∧ word ∈ (uniformWords formula p q).support := by
  change ((Nat.unpair (Nat.pair r word)).1 ∈ R.obj.support ∧
    (Nat.unpair (Nat.pair r word)).2 ∈ (uniformWords formula p q).support) ↔ _
  rw [Nat.unpair_pair]

theorem uniformFold_graph (formula : Bool) (r word value : ℕ) :
    value ∈ Total.val (uniformFold hT hF formula).left.hom (Nat.pair r word) ↔
      r ∈ R.obj.support ∧ word ∈ (uniformWords formula p q).support ∧
        adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ evaluation hT hF (Nat.pair r word) := by
  change value ∈ Total.val (uniformFoldArrow hT hF formula) (Nat.pair r word) ↔ _
  rw [uniformFoldArrow_graph,uniformWordFamily_support]
  constructor
  · rintro ⟨⟨hr,hw⟩,hv⟩
    have hv0 : value ∈ (evaluation hT hF (Nat.pair r word)).map extract := hv
    obtain ⟨s,hs,hv⟩ := (Part.mem_map_iff extract).mp hv0
    obtain ⟨v,he⟩ := uniformWords_singleton (P := P) (R := R) (X := X) (Y := Y)
      hT hF formula (r := r) (word := word) (new := s) hw hs
    have hvv : v=value := by simpa only [he,extract_singleton] using hv
    rw [← hvv]
    exact ⟨hr,hw,he ▸ hs⟩
  · rintro ⟨hr,hw,hs⟩
    exact ⟨⟨hr,hw⟩,(Part.mem_map_iff _).mpr ⟨_,hs,extract_singleton formula value⟩⟩

theorem uniformFold_mapped_graph (a b : SyntacticSyntax.RawPolynomial)
    (hT : object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
    (hF : object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)
    (formula : Bool) (r word value : ℕ) :
    value ∈ Total.val (uniformFold hT hF formula).left.hom (Nat.pair r word) ↔
      value ∈ Total.val (fold a b hT hF formula).left.hom (Nat.pair r word) := by
  rw [uniformFold_graph,fold_graph,uniformWords_mapped]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
