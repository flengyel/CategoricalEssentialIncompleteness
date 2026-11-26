module

import CategoricalEssentialIncompleteness.V46DominicalDiagonal
import CategoricalEssentialIncompleteness.V46RegularImage
import CategoricalEssentialIncompleteness.V46MachineOracleTuring
import CategoricalEssentialIncompleteness.V46SelectorGraph

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness

universe v u

section Introduction

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

example {Y Z : C} (f : Y ⟶ Z) (s : Z ⟶ Y) (hs : IsSection f s) :
    IsRange (s ≫ f) f := by
  rw [hs.comp_eq_rst]
  exact hs.isRange

example {Y Z W : C} (f : Y ⟶ Z) (s : Z ⟶ Y)
    (u v : Z ⟶ W) (h : f ≫ u = f ≫ v) :
    (s ≫ f) ≫ u = (s ≫ f) ≫ v := by
  rw [Category.assoc, h, Category.assoc]

variable [HasZeroMorphisms C] [RestrictionZero C] [Ranges C]
  [CoprodStruct C] [CategoryTheory.HasCoproducts C]

example {X : C} (c d : Idem X) : coprod X X ⟶ X := copair c.hom d.hom

example {X : C} (c d : Idem X) (h : Complementary c d) (g : X ⟶ X)
    (hc : Idem.pull g c = ⊥) (hd : Idem.pull g d = ⊥) :
    g = 0 := CategoricalEssentialIncompleteness.V46.DominicalDiagonal.zero_of_empty_preimages h g hc hd

end Introduction

section AppendixA

open CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness.V46
variable {S : Type u} [Category.{v} S] [RestrictionCategory S] [Ranges S] [Splits S]

example {X I Y : TotalCategory S} (e : X ⟶ I) (m : I ⟶ Y) [IsRegularEpi e]
    (r : Y.obj ⟶ I.obj) (hmr : m.hom ≫ r = 𝟙 I.obj) (hrm : r ≫ m.hom = rst r) :
    let a := Ranges.range (e.hom ≫ m.hom)
    a ≤ Idem.ofRestrict r ∧ Idem.ofRestrict r ≤ a := by
  have eqDom : Ranges.range (e.hom ≫ m.hom) = Idem.ofRestrict r := by
    apply Idem.ext
    exact (range_regularImage e m r hmr hrm).trans hrm
  exact ⟨eqDom.le,eqDom.ge⟩

end AppendixA

section AppendixC

open CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
open CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

example : ∀ n m : ℕ, n ∈ K ↔ Nat.pair (Encodable.encode (simulationCode n)) m ∈ A :=
  fun n m => K_iff_simulation_mem_A n m

example (s : ℕ →. (ℕ ⊕ ℕ))
    (h₀ : ∀ x, (∃ y : ℕ, Sum.inl y ∈ s x) ↔ x ∉ A)
    (h₁ : ∀ x, (∃ y : ℕ, Sum.inr y ∈ s x) ↔ x ∈ A) :
    ∀ ℓ : N K ⟶ coprod (N K) (N K), (inclusion K).map ℓ ≠ s := by
  intro candidate hc
  exact no_lift_of_output_summands s h₀ h₁ ⟨candidate,hc⟩

end AppendixC

section Selector

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.FiniteSigmaOne

example (m : ℕ) (L : 𝚺₁.Semisentence 2) (D : Fin (m+1) → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (selectedEntry L D) :=
  selected_entries_PA L D

end Selector

#print axioms CategoryTheory.IsSection.isRange
#print axioms CategoricalEssentialIncompleteness.V46.DominicalDiagonal.zero_of_empty_preimages
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.V46.range_regularImage
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.K_iff_simulation_mem_A
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted.no_lift_of_output_summands
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted.machine_no_lift
#print axioms CategoricalEssentialIncompleteness.V46.FiniteSigmaOne.selected_entries_PA
