/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalPredicates
public import CategoricalEssentialIncompleteness.CharacteristicArrows

/-!
# The Boolean PER

Equality on the support `{0, 1}` is a coproduct of two terminal PERs.
Its two constant points correspond to the coproduct injections.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def booleanSupport : Set ℕ := {n | n = 0 ∨ n = 1}

def boolean : NumericalPER := discrete booleanSupport

theorem toNat_mem_booleanSupport (b : Bool) : b.toNat ∈ booleanSupport := by
  cases b <;> simp [booleanSupport]

def booleanConstantRepresentative (R : NumericalPER) (b : Bool) :
    Representative R boolean where
  val _ := Part.some b.toNat
  computable := (Computable.const b.toNat).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a c _ ha hc
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hc
    exact ⟨toNat_mem_booleanSupport b, rfl⟩

def booleanConstant (R : NumericalPER) (b : Bool) : R ⟶ boolean :=
  ofRepresentative (booleanConstantRepresentative R b)

def booleanPoint (b : Bool) : ⊤_ NumericalPER ⟶ boolean := booleanConstant _ b

@[simp, reassoc] theorem comp_booleanConstant {R S : NumericalPER} (f : R ⟶ S) (b : Bool) :
    f ≫ booleanConstant S b = booleanConstant R b := by
  induction f using Quotient.inductionOn with | _ f =>
    apply Quotient.sound
    intro n hn a ha c hc
    obtain ⟨k, _, ha⟩ := Part.mem_bind_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hc
    exact ⟨toNat_mem_booleanSupport b, rfl⟩

def coproductBooleanRepresentative : Representative (coproduct unitPER unitPER) boolean where
  val n := Part.some (Nat.unpair n).1
  computable := (Computable.fst.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    rcases h with ⟨hn, hm, _⟩ | ⟨hn, hm, _⟩
    · exact ⟨Or.inl hn, hn.trans hm.symm⟩
    · exact ⟨Or.inr hn, hn.trans hm.symm⟩

def booleanCoproductRepresentative : Representative boolean (coproduct unitPER unitPER) where
  val n := Part.some (Nat.pair n 0)
  computable := (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0)).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    obtain ⟨hn, rfl⟩ := h
    rcases hn with rfl | rfl
    · exact (coproduct_rel_inl unitPER unitPER 0 0).mpr trivial
    · exact (coproduct_rel_inr unitPER unitPER 0 0).mpr trivial

def coproductBooleanIso : coproduct unitPER unitPER ≅ boolean where
  hom := ofRepresentative coproductBooleanRepresentative
  inv := ofRepresentative booleanCoproductRepresentative
  hom_inv_id := by
    apply Quotient.sound
    intro n hn a ha b hb
    change a ∈ (Part.some (Nat.unpair n).1).bind
      (fun k ↦ Part.some (Nat.pair k 0)) at ha
    simp only [Part.bind_some, Part.mem_some_iff] at ha
    obtain rfl := ha
    obtain rfl := Part.mem_some_iff.mp hb
    rcases hn with ⟨hn, _, _⟩ | ⟨hn, _, _⟩
    · exact Or.inl ⟨by simp [hn], hn, trivial⟩
    · exact Or.inr ⟨by simp [hn], hn, trivial⟩
  inv_hom_id := by
    apply Quotient.sound
    apply Representative.equiv_of_val_eq
    funext n
    simp [Representative.compose, booleanCoproductRepresentative,
      coproductBooleanRepresentative, Representative.identity]

def booleanUnitCofanIsColimit :
    IsColimit (BinaryCofan.mk (booleanConstant unitPER false) (booleanConstant unitPER true)) :=
  (coproductIsColimit unitPER unitPER).ofIsoColimit
    (BinaryCofan.ext coproductBooleanIso
      (by
        apply Quotient.sound
        apply Representative.equiv_of_val_eq
        funext n
        simp [inl, Representative.compose, inlRepresentative,
          coproductBooleanRepresentative, booleanConstant, booleanConstantRepresentative])
      (by
        apply Quotient.sound
        apply Representative.equiv_of_val_eq
        funext n
        simp [inr, Representative.compose, inrRepresentative,
          coproductBooleanRepresentative, booleanConstant, booleanConstantRepresentative]))

def booleanCofanIsColimit :
    IsColimit (BinaryCofan.mk (booleanPoint false) (booleanPoint true)) := by
  let e : ⊤_ NumericalPER ≅ unitPER := terminalIsTerminal.uniqueUpToIso unitIsTerminal
  have h := BinaryCofan.isColimitCompLeftIso _ e.hom booleanUnitCofanIsColimit
  have h' := BinaryCofan.isColimitCompRightIso _ e.hom h
  change IsColimit (BinaryCofan.mk (e.hom ≫ booleanConstant unitPER false)
    (e.hom ≫ booleanConstant unitPER true)) at h'
  simpa only [comp_booleanConstant, booleanPoint] using h'

/-- The chosen coproduct of terminal objects is the explicit Boolean PER. -/
def booleanIso : Two NumericalPER ≅ boolean :=
  (coprodIsCoprod (⊤_ NumericalPER) (⊤_ NumericalPER)).coconePointUniqueUpToIso
    booleanCofanIsColimit

@[simp, reassoc] theorem booleanIso_point (b : Bool) :
    Two.point b ≫ booleanIso.hom = booleanPoint b := by
  cases b
  · exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod (⊤_ NumericalPER) (⊤_ NumericalPER)) booleanCofanIsColimit ⟨WalkingPair.left⟩
  · exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod (⊤_ NumericalPER) (⊤_ NumericalPER)) booleanCofanIsColimit ⟨WalkingPair.right⟩

/-- Equality on a singleton support is a terminal PER. -/
def singletonIsTerminal (n : ℕ) : IsTerminal (discrete {n}) :=
  IsTerminal.ofUniqueHom (fun R ↦ ofRepresentative
    { val _ := Part.some n
      computable := (Computable.const n).partrec
      total := fun _ _ ↦ Part.some_dom _
      respects := by
        intro k l a b _ ha hb
        obtain rfl := Part.mem_some_iff.mp ha
        obtain rfl := Part.mem_some_iff.mp hb
        exact ⟨rfl, rfl⟩ }) (by
    intro R f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      intro k hk a ha b hb
      obtain rfl := Part.mem_some_iff.mp hb
      exact ⟨(f.output_supported hk ha).1, (f.output_supported hk ha).1⟩)

theorem singleton_subset_booleanSupport (b : Bool) : {b.toNat} ⊆ booleanSupport := by
  intro n hn
  obtain rfl := hn
  exact toNat_mem_booleanSupport b

set_option backward.isDefEq.respectTransparency false in
/-- A Boolean point represents its singleton support inclusion. -/
theorem booleanPoint_subobject (b : Bool) :
    Subobject.mk (booleanPoint b) =
      supportSubobject {b.toNat} (singleton_subset_booleanSupport b) := by
  let e : ⊤_ NumericalPER ≅ discrete {b.toNat} :=
    terminalIsTerminal.uniqueUpToIso (singletonIsTerminal b.toNat)
  apply Subobject.mk_eq_mk_of_comm (booleanPoint b)
    (inclusion (singleton_subset_booleanSupport b)) e
  change e.hom ≫ inclusion (singleton_subset_booleanSupport b) = booleanPoint b
  have hf : ∀ f : ⊤_ NumericalPER ⟶ discrete {b.toNat},
      f ≫ inclusion (singleton_subset_booleanSupport b) = booleanPoint b := by
    intro f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      intro n hn a ha c hc
      obtain ⟨k, hk, ha⟩ := Part.mem_bind_iff.mp ha
      obtain rfl := Part.mem_some_iff.mp ha
      obtain rfl := Part.mem_some_iff.mp hc
      exact ⟨singleton_subset_booleanSupport b (f.output_supported hn hk).1,
        (f.output_supported hn hk).1⟩
  exact hf e.hom

end NumericalPER
end CategoricalEssentialIncompleteness
