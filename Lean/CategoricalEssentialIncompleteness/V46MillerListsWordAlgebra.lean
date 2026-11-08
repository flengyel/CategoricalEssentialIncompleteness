/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerListsWordInverse
import CategoricalEssentialIncompleteness.V46MillerListsStable

/-! # Full constructor comparison between numerical lists and literal words

The carrier maps are the previously constructed ordinary code programs.
Their nil and ordered cons equations are proved before using the resulting
algebra isomorphism. Thus no universal property is inferred from a bare
carrier bijection.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Lists
open Syntax.Raw
variable {P : Uniform.Family} (V : Total.Carrier P)

abbrev literalPair := wordAlgebra (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit

def literalAlgebra : ListAlgebra (⟨V⟩ : Total.TotalCategory P) where
  carrier := (literalPair V).a.1
  nil := coprod.inl ≫ (literalPair V).str.1
  cons := coprod.inr ≫ (literalPair V).str.1

def mapConsInput :
    Total.totalProduct (⟨V⟩ : Total.TotalCategory P) (object V) ⟶
      Total.totalProduct (⟨V⟩ : Total.TotalCategory P) (literalAlgebra V).carrier :=
  Total.totalPair (Total.totalFst (⟨V⟩ : Total.TotalCategory P) (object V))
    (Total.totalSnd (⟨V⟩ : Total.TotalCategory P) (object V) ≫ wordMap V)

theorem mapConsInput_value (n : ℕ) (hn : n∈(Total.product V (carrier V)).support) :
    Total.val (mapConsInput V).hom n=
      Part.some (Nat.pair (Nat.unpair n).1 (wordOfCode V (Nat.unpair n).2)) := by
  apply Part.eq_some_iff.mpr
  apply (Total.mem_partialPair _ _ n _).mpr
  refine ⟨(Nat.unpair n).1,(Total.mem_partialFst _ _ n _).mpr ⟨hn,rfl⟩,
    wordOfCode V (Nat.unpair n).2,?_,rfl⟩
  change wordOfCode V (Nat.unpair n).2 ∈ Total.val
    ((Total.totalSnd (⟨V⟩ : Total.TotalCategory P) (object V)).hom ≫ (wordMap V).hom) n
  rw [Total.val_comp]
  apply Part.mem_bind_iff.mpr
  exact ⟨(Nat.unpair n).2,(Total.mem_partialSnd _ _ n _).mpr ⟨hn,rfl⟩,
    (wordMap_graph V _ _).mpr ⟨hn.2,rfl⟩⟩

private theorem baseConsInput (A X Y : Total.TotalCategory P) (f : X ⟶ Y) :
    (baseProductIso A X).hom ≫ prod.map (𝟙 A) f =
      Total.totalPair (Total.totalFst A X) (Total.totalSnd A X ≫ f) ≫ (baseProductIso A Y).hom := by
  apply prod.hom_ext
  · rw [Category.assoc,prod.map_fst,← Category.assoc,baseProductIso_fst,Category.comp_id,
      Category.assoc,baseProductIso_fst,Total.totalPair_fst]
  · rw [Category.assoc,prod.map_snd,← Category.assoc,baseProductIso_snd,
      Category.assoc,baseProductIso_snd,Total.totalPair_snd]

theorem mapConsInput_chart :
    (baseComparison (object V) (object V) (consPolynomial V)).hom ≫
        prod.map (𝟙 (⟨V⟩ : Total.TotalCategory P)) (wordMap V)=
      mapConsInput V ≫
        (baseComparison (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)).hom := by
  simp only [consPolynomial,baseComparison,Iso.trans_hom,prod.mapIso_hom,Iso.refl_hom]
  change ((baseProductIso (⟨V⟩ : Total.TotalCategory P) (object V)).hom ≫ prod.map (𝟙 _) (𝟙 _)) ≫
    prod.map (𝟙 _) (wordMap V)=mapConsInput V ≫
      ((baseProductIso (⟨V⟩ : Total.TotalCategory P) (literalAlgebra V).carrier).hom ≫ prod.map (𝟙 _) (𝟙 _))
  erw [prod.map_id_id,Category.comp_id,prod.map_id_id,Category.comp_id]
  exact baseConsInput (⟨V⟩ : Total.TotalCategory P) (object V) (literalAlgebra V).carrier (wordMap V)

private theorem raw_nil_word :
    nil V ≫ wordMap V=
      taggedInl (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
        (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫
          rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hn0 : n=0 := hn
  have hl := Part.eq_some_iff.mpr (wordMap_nil V n hn)
  have ht : Total.val
      (taggedInl (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
        (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V))).hom n=
      Part.some (Nat.pair 0 0) := by
    apply Part.eq_some_iff.mpr
    exact (Total.mem_totalFromFunction (fun n => Nat.pair n 0)
      (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
      (taggedInl_supported _ _) n _).mpr ⟨hn,by rw [hn0]⟩
  have hr : nilWord V ∈ Total.val
      (rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false).hom (Nat.pair 0 0) := by
    apply (rawWordConstructor_graph _ _ false _ _).mpr
    refine ⟨?_,rfl⟩
    exact taggedInl_supported
      (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
      (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) 0 rfl
  have hright : nilWord V ∈ Total.val
      (taggedInl (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
        (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫
          rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false).hom n := by
    change nilWord V ∈ Total.val ((taggedInl
      (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
        (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V))).hom ≫
          (rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false).hom) n
    exact (Total.mem_val_comp _ _ n _).mpr ⟨Nat.pair 0 0,Part.eq_some_iff.mp ht,hr⟩
  exact hl.trans (Part.eq_some_iff.mpr hright).symm

private theorem raw_cons_word :
    adjoinMap V ≫ wordMap V=
      mapConsInput V ≫
        taggedInr (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
          (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫
            rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  let head := (Nat.unpair n).1
  let tail := (Nat.unpair n).2
  let word := wordOfCode V tail
  have hw : word∈(wordObject false (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit).obj.support :=
    wordOfList_mem V (Nat.natToList tail) hn.2
  have hs : Nat.pair head word ∈ (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)).obj.support := by
    change (Nat.unpair (Nat.pair head word)).1 ∈ V.support ∧
      (Nat.unpair (Nat.pair head word)).2 ∈ (literalAlgebra V).carrier.obj.support
    rw [Nat.unpair_pair]
    exact ⟨hn.1,hw⟩
  have hi := mapConsInput_value V n hn
  have ht : Total.val
      (taggedInr (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
        (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V))).hom (Nat.pair head word)=
      Part.some (Nat.pair (Nat.pair head word) 1) := by
    apply Part.eq_some_iff.mpr
    exact (Total.mem_totalFromFunction (fun n => Nat.pair n 1)
      (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
      (taggedInr_supported _ _) _ _).mpr ⟨hs,rfl⟩
  have hr : consWord V head word ∈ Total.val
      (rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false).hom
        (Nat.pair (Nat.pair head word) 1) := by
    apply (rawWordConstructor_graph _ _ false _ _).mpr
    exact ⟨taggedInr_supported
      (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
      (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) _ hs,rfl⟩
  have hl : consWord V head word ∈ Total.val ((adjoinMap V) ≫ wordMap V).hom n := by
    simpa only [head,tail,word,Nat.pair_unpair] using
      (wordMap_adjoin V head tail (consWord V head word)).mpr ⟨hn.1,hn.2,rfl⟩
  have hright : consWord V head word ∈ Total.val
      (mapConsInput V ≫
        taggedInr (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
          (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫
            rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false).hom n := by
    change consWord V head word ∈ Total.val ((mapConsInput V).hom ≫
      ((taggedInr (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
        (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V))).hom ≫
          (rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false).hom)) n
    exact (Total.mem_val_comp _ _ n _).mpr ⟨Nat.pair head word,Part.eq_some_iff.mp hi,
      (Total.mem_val_comp _ _ _ _).mpr ⟨Nat.pair (Nat.pair head word) 1,Part.eq_some_iff.mp ht,hr⟩⟩
  exact (Part.eq_some_iff.mpr hl).trans (Part.eq_some_iff.mpr hright).symm

theorem wordMap_nil_constructor : (algebra V).nil ≫ (wordIso V).hom=(literalAlgebra V).nil := by
  apply (cancel_epi (baseComparison (object V) (object V) .unit).hom).mp
  simp only [algebra,Category.assoc,Iso.hom_inv_id_assoc,wordIso]
  rw [raw_nil_word]
  rw [← wordAlgebra_term_constructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit]
  erw [← Category.assoc,baseComparison_sum_inl (literalPair V).a.1 (literalPair V).a.2 .unit (consPolynomial V)]
  simp only [Category.assoc,literalAlgebra]
  rfl

theorem wordMap_cons_constructor :
    (algebra V).cons ≫ (wordIso V).hom=
      prod.map (𝟙 (⟨V⟩ : Total.TotalCategory P)) (wordIso V).hom ≫ (literalAlgebra V).cons := by
  apply (cancel_epi (baseComparison (object V) (object V) (consPolynomial V)).hom).mp
  simp only [algebra,Category.assoc,Iso.hom_inv_id_assoc,wordIso]
  rw [raw_cons_word]
  have hb := baseComparison_sum_inr (literalPair V).a.1 (literalPair V).a.2 .unit (consPolynomial V)
  have hb' := congrArg (fun k => mapConsInput V ≫ (k ≫ (literalPair V).str.1)) hb
  have hc := congrArg (fun k => k ≫ (coprod.inr ≫ (literalPair V).str.1)) (mapConsInput_chart V).symm
  simp only [Category.assoc] at hb' hc
  have he := hb'.trans hc
  have hr := wordAlgebra_term_constructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit
  change (baseComparison (literalPair V).a.1 (literalPair V).a.2 (polynomial (⟨V⟩ : Total.TotalCategory P))).hom ≫
    (literalPair V).str.1=rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false at hr
  have hr' := congrArg (fun k => mapConsInput V ≫ (taggedInr
    (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
      (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫ k)) hr
  change mapConsInput V ≫ taggedInr
      (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
      (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫
        (baseComparison (literalPair V).a.1 (literalPair V).a.2 (polynomial (⟨V⟩ : Total.TotalCategory P))).hom ≫
          (literalPair V).str.1 = _ at he
  have he' := hr'.symm.trans he
  change mapConsInput V ≫ taggedInr
      (baseObject (literalPair V).a.1 (literalPair V).a.2 .unit)
      (baseObject (literalPair V).a.1 (literalPair V).a.2 (consPolynomial V)) ≫
        rawWordConstructor (polynomial (⟨V⟩ : Total.TotalCategory P)) .unit false =
    (baseComparison (object V) (object V) (consPolynomial V)).hom ≫
      prod.map (𝟙 (⟨V⟩ : Total.TotalCategory P)) (wordMap V) ≫ coprod.inr ≫ (literalPair V).str.1
  exact he' 

/-- Both code programs and their exact constructors form a full algebra
isomorphism; membership witnesses do not become extra labels. -/
def wordAlgebraIso : (algebra V).asAlgebra ≅ (literalAlgebra V).asAlgebra :=
  SyntacticLists.Transport.constructorsIso _ _ (wordIso V)
    (wordMap_nil_constructor V) (wordMap_cons_constructor V)

def literalInitial : IsInitial (literalAlgebra V).asAlgebra :=
  (initial V).ofIso (wordAlgebraIso V)

end CategoricalEssentialIncompleteness.V46.Miller.Lists
