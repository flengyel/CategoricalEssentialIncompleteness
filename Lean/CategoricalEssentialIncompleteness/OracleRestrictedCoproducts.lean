/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleRestrictedPCategory

/-! # Tagged restriction coproducts in the oracle-domain category -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable {S : Set ℕ}
attribute [instance 2000] nativeRestriction

@[implicit_reducible] def coproduct (X Y : Restricted S) : Restricted S := ⟨.coproduct X.type Y.type⟩

theorem sum_domain {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → Part γ} {g : β → Part γ}
    (hf : FiniteOracleRE S (fun x => (f x).Dom))
    (hg : FiniteOracleRE S (fun y => (g y).Dom)) :
    FiniteOracleRE S (fun t : α ⊕ β => (Sum.elim f g t).Dom) := by
  have hl : REPred (fun p : (α ⊕ β) × α => p.1=Sum.inl p.2) :=
    (Primrec.eq.comp Primrec.fst (Primrec.sumInl.comp Primrec.snd)).computablePred.to_re
  have hr : REPred (fun p : (α ⊕ β) × β => p.1=Sum.inr p.2) :=
    (Primrec.eq.comp Primrec.fst (Primrec.sumInr.comp Primrec.snd)).computablePred.to_re
  apply (((FiniteOracleRE.of_re hl).and (hf.comp Computable.snd)).projection.or
    ((FiniteOracleRE.of_re hr).and (hg.comp Computable.snd)).projection).of_eq
  intro t
  cases t <;> simp

def copairRaw {X Y Z : Restricted S} (f : X ⟶ Z) (g : Y ⟶ Z) : coproduct X Y ⟶ Z := by
  refine ⟨Sum.elim f.val g.val,sum_domain f.domain g.domain,?_⟩
  obtain ⟨f₀,hf,he⟩ := f.extension
  obtain ⟨g₀,hg,hge⟩ := g.extension
  refine ⟨Sum.elim f₀ g₀,Partrec.sumCasesOn Computable.id
    (hf.comp Computable.snd).to₂ (hg.comp Computable.snd).to₂,?_⟩
  intro x y h
  cases x with
  | inl x => exact he x y h
  | inr x => exact hge x y h

def inl (X Y : Restricted S) : X ⟶ coproduct X Y := totalFromFunction Sum.inl Computable.sumInl
def inr (X Y : Restricted S) : Y ⟶ coproduct X Y := totalFromFunction Sum.inr Computable.sumInr

def sumMap {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) : coproduct W Y ⟶ coproduct X Z :=
  copairRaw (f ≫ inl X Z) (g ≫ inr X Z)

def codiagonal (X : Restricted S) : coproduct X X ⟶ X :=
  totalFromFunction (Sum.elim id id) (Computable.sumCasesOn Computable.id Computable.snd.to₂ Computable.snd.to₂)

instance coproductStruct : CoprodStruct (Restricted S) where
  coprod := coproduct
  coprod_map := sumMap
  codiag := codiagonal
  i0 := inl
  i1 := inr

@[simp] theorem inl_val (X Y : Restricted S) : (inl X Y).val=fun x => Part.some (Sum.inl x) := rfl
@[simp] theorem inr_val (X Y : Restricted S) : (inr X Y).val=fun y => Part.some (Sum.inr y) := rfl
@[simp] theorem codiagonal_val (X : Restricted S) :
    (codiagonal X).val=fun s => Part.some (s.elim id id) := rfl

theorem sumMap_val {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) :
    (sumMap f g).val=PartialFunctions.sumMap f.val g.val := by
  funext s
  cases s <;> simp only [sumMap,copairRaw,comp_val,inl_val,inr_val,
    Part.bind_some_eq_map,PartialFunctions.sumMap]

theorem coproduct_map_val {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) :
    (coprod_map f g).val=coprod_map (C := PartialFunctions.Pfn) f.val g.val := sumMap_val f g

@[simp] theorem i0_val (X Y : Restricted S) :
    (i0 X Y).val=fun x => Part.some (Sum.inl x) := rfl
@[simp] theorem i1_val (X Y : Restricted S) :
    (i1 X Y).val=fun y => Part.some (Sum.inr y) := rfl
@[simp] theorem codiag_val (X : Restricted S) :
    (CoprodStruct.codiag X).val=fun s => Part.some (s.elim id id) := rfl
@[simp] theorem coprod_map_rawVal {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) :
    (coprod_map f g).val=PartialFunctions.sumMap f.val g.val := sumMap_val f g

instance coproducts : CategoryTheory.HasCoproducts (Restricted S) where
  coprod_id X Y := by
    apply Arrow.ext
    change (sumMap (𝟙 X) (𝟙 Y)).val=(𝟙 (coproduct X Y) : coproduct X Y ⟶ coproduct X Y).val
    rw [sumMap_val,id_val,id_val,id_val]
    exact CategoryTheory.HasCoproducts.coprod_id (C := PartialFunctions.Pfn)
      ((inclusion S).obj X) ((inclusion S).obj Y)
  coprod_comp f g h k := by
    apply Arrow.ext
    simp only [comp_val,coproduct_map_val]
    exact CategoryTheory.HasCoproducts.coprod_comp (C := PartialFunctions.Pfn) f.val g.val h.val k.val
  i0_codiag X := by
    apply Arrow.ext
    change ((inl X X) ≫ codiagonal X).val=(𝟙 X : X ⟶ X).val
    simp only [comp_val,inl_val,codiagonal_val,id_val,Part.bind_some]
    rfl
  i1_codiag X := by
    apply Arrow.ext
    change ((inr X X) ≫ codiagonal X).val=(𝟙 X : X ⟶ X).val
    simp only [comp_val,inr_val,codiagonal_val,id_val,Part.bind_some]
    rfl
  i0_i1_codiag X Y := by
    apply Arrow.ext
    funext s
    cases s <;> simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,sumMap_val,comp_val,inl_val,inr_val,codiagonal_val,
      id_val,PartialFunctions.sumMap]
  codiag_nat f := by
    apply Arrow.ext
    funext s
    cases s <;> simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,sumMap_val,comp_val,codiagonal_val,PartialFunctions.sumMap,
      Part.bind_some_eq_map,Part.bind_map,Part.bind_some_right]
    all_goals rw [Part.map_map]; exact Part.map_id' (fun _ => rfl) _
  i0_nat f := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,sumMap_val,comp_val,inl_val,PartialFunctions.sumMap,Part.bind_some_eq_map]
  i0_nat_right g := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,sumMap_val,comp_val,inl_val,id_val,PartialFunctions.sumMap]
  i1_nat f := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,sumMap_val,comp_val,inr_val,PartialFunctions.sumMap,Part.bind_some_eq_map]
  i1_nat_left f := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,sumMap_val,comp_val,inr_val,id_val,PartialFunctions.sumMap]

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
