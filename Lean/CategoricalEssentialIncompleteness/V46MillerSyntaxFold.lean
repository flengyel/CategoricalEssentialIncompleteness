/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxSource

/-! # Actual arbitrary-slice fold morphisms on the original literal words

The selected evaluator is restricted to the original syntax word
predicate. The singleton and fiber theorems prove support, totality and
the parameter equation. Constructor compatibility and the universal
property are not assumptions of this construction.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable (a b : SyntacticSyntax.RawPolynomial)
variable (hT : object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
variable (hF : object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)

def wordFamily (formula : Bool) : Over R :=
  Over.mk (Total.totalFst R (⟨words P formula a b⟩ : Total.TotalCategory P))

@[simp] theorem wordFamily_support (formula : Bool) (r word : ℕ) :
    Nat.pair r word ∈ (wordFamily (R := R) a b formula).left.obj.support ↔
      r ∈ R.obj.support ∧ word ∈ (words P formula a b).support := by
  change ((Nat.unpair (Nat.pair r word)).1 ∈ R.obj.support ∧
    (Nat.unpair (Nat.pair r word)).2 ∈ (words P formula a b).support) ↔ _
  rw [Nat.unpair_pair]

def extract (s : ℕ) : ℕ := π₁ (fstIdx (s-1))

theorem extract_primrec : Primrec extract :=
  NatVectors.pi1_primrec.comp (NatVectors.fstIdx_primrec.comp
    (Primrec.nat_sub.comp Primrec.id (.const 1)))

@[simp] theorem extract_singleton (formula : Bool) (v : ℕ) :
    extract (adjoin (Nat.pair v (if formula then 1 else 0)) 0+1)=v := by
  simp [extract,FiniteSigmaOne.nat_pi₁_eq]

def selectedValue (x : ℕ) : Part ℕ := (evaluation hT hF x).map extract

theorem selectedValue_represented : Uniform.Represented P .nat .nat (selectedValue a b hT hF) := by
  have he : Uniform.Represented P .nat .nat (fun x : ℕ => Part.some (extract x)) :=
    Uniform.Represented.of_partrec extract_primrec.to_comp.partrec
  apply (Uniform.Represented.comp (evaluation_represented hT hF) he).of_eq
  intro x
  change (evaluation hT hF x).bind (fun z : ℕ => Part.some (extract z)) =
    (evaluation hT hF x).map extract
  exact Part.bind_some_eq_map extract (evaluation hT hF x)

theorem selectedValue_fiber (formula : Bool) {r word value : ℕ}
    (hr : r ∈ R.obj.support) (hw : word ∈ (words P formula a b).support)
    (hv : value ∈ selectedValue a b hT hF (Nat.pair r word)) :
    r ∈ Total.val (if formula then Y else X).hom.hom value := by
  obtain ⟨s,hs,hvalue⟩ := (Part.mem_map_iff _).mp hv
  obtain ⟨v,he⟩ := source_evaluation_singleton a b hT hF formula hw hs
  have hsI := evaluation_status hT hF (source_coefficientWord a b formula r word hr hw) hs
  rw [he] at hsI hvalue
  have hvv : v=value := by simpa only [extract_singleton] using hvalue
  rw [← hvv]
  simp only [Nat.unpair_pair] at hsI
  have hst := ((status_succ R X Y r _).mp hsI).2
  have hblock := ((fiberStack_adjoin R X Y r _ 0).mp hst).1
  cases formula
  · exact (fiberBlock_term R X Y r v).mp hblock
  · exact (fiberBlock_formula R X Y r v).mp hblock

def foldArrow (formula : Bool) :
    (wordFamily (R := R) a b formula).left.obj ⟶ (if formula then Y else X).left.obj :=
  let r : Uniform.N P ⟶ Uniform.N P :=
    ⟨selectedValue a b hT hF,selectedValue_represented a b hT hF⟩
  let k := Uniform.identityOn (Uniform.N P) (wordFamily (R := R) a b formula).left.obj.support
    (wordFamily (R := R) a b formula).left.obj.enumerable ≫ r
  Total.arrow k.val k.represented (by
    intro x y hy
    obtain ⟨u,hu,_⟩ := Part.mem_bind_iff.mp hy
    exact ((Total.mem_supportIdentity _ x u).mp hu).1) (by
    intro x y hy
    obtain ⟨u,hu,huy⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨hx,hux⟩ := (Total.mem_supportIdentity _ x u).mp hu
    subst u
    have hf := selectedValue_fiber a b hT hF formula hx.1 hx.2
      (by simpa only [Nat.pair_unpair] using huy)
    cases formula
    · exact Total.val_source X.hom.hom _ _ hf
    · exact Total.val_source Y.hom.hom _ _ hf)

theorem foldArrow_graph (formula : Bool) (x y : ℕ) :
    y ∈ Total.val (foldArrow a b hT hF formula) x ↔
      x ∈ (wordFamily (R := R) a b formula).left.obj.support ∧ y ∈ selectedValue a b hT hF x := by
  change y ∈ (Total.supportIdentity _ x).bind (selectedValue a b hT hF) ↔ _
  simp only [Part.mem_bind_iff,Total.mem_supportIdentity]
  aesop

theorem foldArrow_total (formula : Bool) : isTotal (foldArrow a b hT hF formula) := by
  apply (Total.total_iff _).mpr
  intro x hx
  have hm := evaluation_total hT hF
    (source_coefficientWord a b formula (Nat.unpair x).1 (Nat.unpair x).2 hx.1 hx.2)
  obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp hm
  exact Part.dom_iff_mem.mpr ⟨extract s,(foldArrow_graph a b hT hF formula x _).mpr
    ⟨hx,(Part.mem_map_iff _).mpr ⟨s,by simpa only [Nat.pair_unpair] using hs,rfl⟩⟩⟩

def foldLeft (formula : Bool) :
    (wordFamily (R := R) a b formula).left ⟶ (if formula then Y else X).left :=
  ⟨foldArrow a b hT hF formula,foldArrow_total a b hT hF formula⟩

theorem fold_parameter (formula : Bool) :
    foldLeft a b hT hF formula ≫ (if formula then Y else X).hom=
      (wordFamily (R := R) a b formula).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((Total.total_iff _).mp
    (foldLeft a b hT hF formula).property x hx)
  have hvalue := ((foldArrow_graph a b hT hF formula x y).mp hy).2
  have hp := selectedValue_fiber a b hT hF formula hx.1 hx.2
    (by simpa only [Nat.pair_unpair] using hvalue)
  have hyEq : Total.val (foldLeft a b hT hF formula).hom x=Part.some y := Part.eq_some_iff.mpr hy
  have hpEq : Total.val (if formula then Y else X).hom.hom y=
      Part.some (Nat.unpair x).1 := Part.eq_some_iff.mpr hp
  have hxEq : Total.val (wordFamily (R := R) a b formula).hom.hom x=Part.some (Nat.unpair x).1 :=
    Part.eq_some_iff.mpr ((Total.mem_partialFst _ _ x _).mpr ⟨hx,rfl⟩)
  change Total.val ((foldLeft a b hT hF formula).hom ≫ (if formula then Y else X).hom.hom) x =
    Total.val (wordFamily (R := R) a b formula).hom.hom x
  rw [Total.val_comp,hyEq,Part.bind_some,hpEq,hxEq]

def fold (formula : Bool) : wordFamily (R := R) a b formula ⟶ (if formula then Y else X) :=
  Over.homMk (foldLeft a b hT hF formula) (fold_parameter a b hT hF formula)

theorem fold_graph (formula : Bool) (r word value : ℕ) :
    value ∈ Total.val (fold a b hT hF formula).left.hom (Nat.pair r word) ↔
      r ∈ R.obj.support ∧ word ∈ (words P formula a b).support ∧
        adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 ∈ evaluation hT hF (Nat.pair r word) := by
  change value ∈ Total.val (foldArrow a b hT hF formula) (Nat.pair r word) ↔ _
  rw [foldArrow_graph]
  rw [wordFamily_support]
  constructor
  · rintro ⟨⟨hr,hw⟩,hv⟩
    have hv0 : value ∈ (evaluation hT hF (Nat.pair r word)).map extract := hv
    obtain ⟨s,hs,hv⟩ := (Part.mem_map_iff extract).mp hv0
    obtain ⟨v,he⟩ := source_evaluation_singleton (P := P) (R := R) (X := X) (Y := Y)
      a b hT hF formula (r := r) (word := word) (new := s) hw hs
    have hvv : v=value := by simpa only [he,extract_singleton] using hv
    rw [← hvv]
    exact ⟨hr,hw,he ▸ hs⟩
  · rintro ⟨hr,hw,hs⟩
    exact ⟨⟨hr,hw⟩,(Part.mem_map_iff _).mpr
      ⟨_,hs,extract_singleton formula value⟩⟩

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
