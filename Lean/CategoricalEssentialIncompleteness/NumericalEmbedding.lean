/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalPER

/-!
# The numerical functor into PERs

The total-arrow category of the numerical restriction category maps to equality
PERs. Restricting a representing function to the recursive source support proves fullness;
extensional equality of canonical partial maps proves faithfulness.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace Numerical

abbrev Total := WideSubcategory (RestrictionCategory.isTotal (C := Numerical))

def totalObject (X : Numerical) : Total := ⟨X⟩

def totalRepresentative {X Y : Total} (f : X ⟶ Y) :
    NumericalPER.Representative (NumericalPER.discrete X.obj.carrier)
      (NumericalPER.discrete Y.obj.carrier) where
  val := f.hom.val
  computable := f.hom.computable
  total := fun n hn ↦ (total_iff f.hom).mp f.property n hn.1
  respects := by
    intro n m a b h ha hb
    obtain ⟨_, rfl⟩ := h
    exact ⟨f.hom.target ha, Part.mem_unique ha hb⟩

/-- The manuscript's functor J on the numerical total-arrow category. -/
def toPER : Total ⥤ NumericalPER where
  obj X := NumericalPER.discrete X.obj.carrier
  map f := NumericalPER.ofRepresentative (totalRepresentative f)
  map_id X := by
    apply Quotient.sound
    intro n hn a ha b hb
    obtain ⟨haX, rfl⟩ := (mem_supportIdentity _ _ _).mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact ⟨haX, rfl⟩
  map_comp f g := rfl

instance toPER_faithful : toPER.Faithful where
  map_injective := by
    intro X Y f g h
    have hv := (NumericalPER.discrete_arrow_eq_iff
      (totalRepresentative f) (totalRepresentative g)).mp h
    apply WideSubcategory.hom_ext
    apply Hom.ext
    funext n
    by_cases hn : n ∈ X.obj.carrier
    · exact hv n ⟨hn, rfl⟩
    · apply Part.ext
      intro m
      exact ⟨fun hm ↦ (hn (f.hom.source hm)).elim, fun hm ↦ (hn (g.hom.source hm)).elim⟩

/-- Canonical partial map obtained by restricting a representing function to its source. -/
def ofDiscreteRepresentative {X Y : Numerical}
    (f : NumericalPER.Representative (NumericalPER.discrete X.carrier)
      (NumericalPER.discrete Y.carrier)) : X ⟶ Y where
  val n := (supportIdentity X.carrier n).bind f.val
  computable := (supportIdentity_partrec _ X.recursive.to_re).bind
    (f.computable.comp Computable.snd).to₂
  source := by
    intro n m h
    obtain ⟨k, hk, _⟩ := Part.mem_bind_iff.mp h
    exact (mem_supportIdentity _ _ _).mp hk |>.1
  target := by
    intro n m h
    obtain ⟨k, hk, hm⟩ := Part.mem_bind_iff.mp h
    obtain ⟨hn, rfl⟩ := (mem_supportIdentity _ _ _).mp hk
    exact f.output_supported ⟨hn, rfl⟩ hm |>.1

theorem ofDiscreteRepresentative_total {X Y : Numerical}
    (f : NumericalPER.Representative (NumericalPER.discrete X.carrier)
      (NumericalPER.discrete Y.carrier)) :
    RestrictionCategory.isTotal (ofDiscreteRepresentative f) := by
  apply (total_iff _).mpr
  intro n hn
  change ((supportIdentity X.carrier n).bind f.val).Dom
  rw [supportIdentity, Part.assert_pos hn, Part.bind_some]
  exact f.total n ⟨hn, rfl⟩

instance toPER_full : toPER.Full where
  map_surjective := by
    intro X Y f
    induction f using Quotient.inductionOn with | _ f =>
      refine ⟨⟨ofDiscreteRepresentative f, ofDiscreteRepresentative_total f⟩, ?_⟩
      apply NumericalPER.discrete_arrow_eq_iff _ _ |>.mpr
      intro n hn
      change (supportIdentity X.obj.carrier n).bind f.val = f.val n
      rw [supportIdentity, Part.assert_pos hn.1, Part.bind_some]

/-- A total recursive numerical function, as a total categorical morphism. -/
def natArrow (f : ℕ → ℕ) (hf : Computable f) : totalObject nat ⟶ totalObject nat where
  hom :=
    { val n := Part.some (f n)
      computable := hf
      source := fun _ ↦ Set.mem_univ _
      target := fun _ ↦ Set.mem_univ _ }
  property := (total_iff _).mpr (fun _ _ ↦ Part.some_dom _)

/-- The ordinary numerical function denoted by a total morphism on ℕ. -/
def natFunction (f : totalObject nat ⟶ totalObject nat) (n : ℕ) : ℕ :=
  (f.hom.val n).get ((total_iff f.hom).mp f.property n (Set.mem_univ _))

theorem natFunction_computable (f : totalObject nat ⟶ totalObject nat) :
    Computable (natFunction f) := f.hom.computable.of_eq_tot (fun _ ↦ Part.get_mem _)

@[simp] theorem natFunction_natArrow (f : ℕ → ℕ) (hf : Computable f) :
    natFunction (natArrow f hf) = f := rfl

theorem natArrow_natFunction (f : totalObject nat ⟶ totalObject nat) :
    natArrow (natFunction f) (natFunction_computable f) = f := by
  apply WideSubcategory.hom_ext
  apply Hom.ext
  funext n
  exact Part.some_get _

end Numerical
end CategoricalEssentialIncompleteness
