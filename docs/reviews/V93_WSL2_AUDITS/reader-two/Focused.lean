module

import CategoricalEssentialIncompleteness.V46DominicalDiagonal
import CategoricalEssentialIncompleteness.V46SelectorGraph
import CategoricalEssentialIncompleteness.V46MachineOracleTuring
import CategoricalEssentialIncompleteness.V46RegularImage
import CategoricalEssentialIncompleteness.V46MillerFixedPoint
import CategoricalEssentialIncompleteness.V46MillerCutReduction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CEI93ReaderTwo

section Dominical
open CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.V46.DominicalDiagonal
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

theorem section_range {X Y : C} (f : X ⟶ Y) (s : Y ⟶ X) (hs : IsSection f s) :
    IsRange (PCategoryStruct.rst s) f ∧
    (∀ {W : C} (g g' : Y ⟶ W), f ≫ g = f ≫ g' →
      PCategoryStruct.rst s ≫ g = PCategoryStruct.rst s ≫ g') :=
  ⟨hs.isRange, fun g g' he => hs.isRange.uniq g g' he⟩

variable [HasZeroMorphisms C] [CoprodStruct C] [CategoryTheory.HasCoproducts C]

open CategoryTheory.RestrictionCategory
variable [RestrictionZero C] [RestrictionCoproducts C] [Ranges C] [HasChoice C]

theorem copair_section {X : C} (c d : Idem X) (H : Complementary c d) :
    ∃ (p : coprod X X ⟶ X), p = CategoryTheory.CoprodStruct.copair c.hom d.hom ∧
    (∃ σ : X ⟶ coprod X X, IsSection p σ ∧ σ ≫ p = 𝟙 X) ∧
    ∃ s : X ⟶ coprod X X, isTotal s ∧
      Idem.pull s (summand0 X X) = c ∧ Idem.pull s (summand1 X X) = d := by
  let f : coprod X X ⟶ X := CategoryTheory.CoprodStruct.copair c.hom d.hom
  obtain ⟨σ, hσ⟩ := HasChoice.exists_isSection f
  have he := Ranges.agreement f (σ ≫ f) (𝟙 X) (by rw [hσ.comp_self, Category.comp_id])
  have full : σ ≫ f = 𝟙 X := by
    simpa only [f, range_copair_idem, H.cover, Idem.top_hom, Category.id_comp] using he
  exact ⟨f, rfl, ⟨σ, hσ, full⟩, complementary_section c d H⟩

omit [RestrictionCoproducts C] [HasChoice C] in
theorem two_empty {X Y : C} (c d : Idem Y) (h : Complementary c d) (f : X ⟶ Y)
    (a : Idem.pull f c = ⊥) (b : Idem.pull f d = ⊥) : f = 0 :=
  zero_of_empty_preimages h f a b
end Dominical

section Image
open CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness.V46
variable {S : Type u} [Category.{v} S] [RestrictionCategory S] [Ranges S] [Splits S]

theorem both_range_inequalities {X I Y : TotalCategory S} (e : X ⟶ I) (m : I ⟶ Y)
    [IsRegularEpi e] (r : Y.obj ⟶ I.obj) (hmr : m.hom ≫ r = 𝟙 I.obj)
    (hrm : r ≫ m.hom = rst r) :
    Ranges.range (e.hom ≫ m.hom) ≤ Idem.ofRestrict r ∧
      Idem.ofRestrict r ≤ Ranges.range (e.hom ≫ m.hom) := by
  have he : Ranges.range (e.hom ≫ m.hom) = Idem.ofRestrict r :=
    Idem.ext ((range_regularImage e m r hmr hrm).trans hrm)
  exact ⟨he.le, he.ge⟩

theorem every_fixing_domain {X I Y : TotalCategory S} (e : X ⟶ I) (m : I ⟶ Y)
    [IsRegularEpi e] (r : Y.obj ⟶ I.obj) (hmr : m.hom ≫ r = 𝟙 I.obj)
    (hrm : r ≫ m.hom = rst r) (a : Idem Y.obj)
    (hfix : (e.hom ≫ m.hom) ≫ a.hom = e.hom ≫ m.hom) :
    Idem.ofRestrict r ≤ a := by
  have lower := (both_range_inequalities e m r hmr hrm).2
  exact lower.trans (Ranges.least _ _ hfix)

omit [Ranges S] [Splits S] in
theorem unique_factor_through_a_splitting {X I Y : TotalCategory S} (e : X ⟶ I) (m : I ⟶ Y)
    [IsRegularEpi e] (a : Idem Y.obj) (hfix : (e.hom ≫ m.hom) ≫ a.hom = e.hom ≫ m.hom)
    (J : TotalCategory S) (j : J ⟶ Y) (t : Y.obj ⟶ J.obj)
    (hjt : j.hom ≫ t = 𝟙 J.obj) (htj : t ≫ j.hom = a.hom) :
    ∃! v : I ⟶ J, v ≫ j = m := by
  let : Mono j := total_split_mono j t hjt
  have fac : ((e.hom ≫ m.hom) ≫ t) ≫ j.hom = e.hom ≫ m.hom := by
    rw [Category.assoc, htj, hfix]
  have total : isTotal ((e.hom ≫ m.hom) ≫ t) := by
    change rst ((e.hom ≫ m.hom) ≫ t) = 𝟙 X.obj
    rw [← rst_comp_of_isTotal _ j.property, fac]
    exact isTotal_comp e.property m.property
  let g : X ⟶ J := ⟨_, total⟩
  have square : CommSq g e j m := ⟨by apply WideSubcategory.hom_ext; exact fac⟩
  refine ⟨square.lift, square.fac_right, ?_⟩
  intro v hv
  exact (cancel_mono j).mp (hv.trans square.fac_right.symm)
end Image

section Selector
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.FiniteSigmaOne

theorem all_selected_entries {m : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin m → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    ((finiteMembership (selectedEntry L D)).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin m,
        L.val.Evalb ![nth a i, ORingStructure.numeral j.val] ∧ (D j).val.Evalb ![nth a i]) ∧
      𝗣𝗔 ⊢ finiteMembershipSentence (selectedEntry L D) :=
  ⟨selected_entries_model L D a, selected_entries_PA L D⟩
end Selector

section Oracle
open CategoryTheory.CoprodStruct CategoryTheory.RestrictionCategory
open OracleComputation OracleComputation.Restricted
attribute [local instance 2000] nativeRestriction

theorem one_simulator : ∃ h : ℕ → ℕ, Computable h ∧ ∀ n a : ℕ,
    ordinaryDiagonal (Nat.pair (h n) a) = (ordinaryEval n n).map (fun _ => 0) ∧
      (n ∈ K ↔ Nat.pair (h n) a ∈ A) :=
  ⟨fun n => Encodable.encode (simulationCode n), Computable.encode.comp simulationCode_computable,
    fun n a => ⟨ordinaryDiagonal_simulation n a, K_iff_simulation_mem_A n a⟩⟩

theorem machine_parameters (S : Set ℕ) : RecursionCategory.IsTuringMorphism (machineTau S) :=
  machineTau_isTuring S

theorem machine_diagonal_domains : machinePair0 K ≤ separator ∧ machinePair1 K ≤ separatorComplement :=
  machine_separator_bounds

theorem arbitrary_candidate (s : ℕ →. (ℕ ⊕ ℕ))
    (h₀ : ∀ n, (∃ y : ℕ, Sum.inl y ∈ s n) ↔ n ∉ A)
    (h₁ : ∀ n, (∃ y : ℕ, Sum.inr y ∈ s n) ↔ n ∈ A) :
    (∀ n, (s n).Dom) ∧ (¬ ∃ f : ℕ → ℕ ⊕ ℕ, Computable f ∧ s = fun n => Part.some (f n)) ∧
      ¬ ∃ l : N K ⟶ coprod (N K) (N K), (inclusion K).map l = s := by
  obtain ⟨total, nonrecursive⟩ := total_and_noncomputable_of_output_summands s h₀ h₁
  exact ⟨total, nonrecursive, no_lift_of_output_summands s h₀ h₁⟩

theorem categorical_candidate (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ))
    (h₀ : Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) = (rangeFunctor K).mapIdem separatorComplement)
    (h₁ : Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) = (rangeFunctor K).mapIdem separator) :
    ¬ ∃ l : N K ⟶ coprod (N K) (N K), (inclusion K).map l = s ≫ ((rangeFunctor K).comparison (N K) (N K)).hom :=
  machine_no_lift s h₀ h₁
end Oracle

section Miller
open CategoricalEssentialIncompleteness.V46.Miller

theorem fixed_numbering_witness : ∃ a : Point, ∀ d : ℕ, ∀ r : Set.Icc (0 : ℝ) 1,
    (∀ p ∈ representations a, ∀ k : ℕ, ∃ i : ℕ, i ∈ OracleProgram.numberedEval d p k ∧
      |(Rationals.q i : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) → a d = r :=
  exists_isMiller

theorem realized_cut_reduction : ∃ a : Point, IsMiller a ∧ ∃ h : ℕ → ℕ, Computable h ∧
    h ⁻¹' CutDigits.lowerCut a = {e | ∃ m, m ∈ Unanimity.tau a e e ∧ m % 2 = 0} ∧
    h ⁻¹' CutDigits.upperCut a = {e | ∃ m, m ∈ Unanimity.tau a e e ∧ m % 2 = 1} := by
  obtain ⟨a, ha⟩ := exists_isMiller
  obtain ⟨h, hh, he⟩ := Cut.uniform_cut_reduction
  exact ⟨a, ha, h, hh, he a ha⟩
end Miller

end CEI93ReaderTwo

#print axioms CEI93ReaderTwo.section_range
#print axioms CEI93ReaderTwo.copair_section
#print axioms CEI93ReaderTwo.two_empty
#print axioms CEI93ReaderTwo.both_range_inequalities
#print axioms CEI93ReaderTwo.every_fixing_domain
#print axioms CEI93ReaderTwo.unique_factor_through_a_splitting
#print axioms CEI93ReaderTwo.all_selected_entries
#print axioms CEI93ReaderTwo.one_simulator
#print axioms CEI93ReaderTwo.machine_parameters
#print axioms CEI93ReaderTwo.machine_diagonal_domains
#print axioms CEI93ReaderTwo.arbitrary_candidate
#print axioms CEI93ReaderTwo.categorical_candidate
#print axioms CEI93ReaderTwo.fixed_numbering_witness
#print axioms CEI93ReaderTwo.realized_cut_reduction
