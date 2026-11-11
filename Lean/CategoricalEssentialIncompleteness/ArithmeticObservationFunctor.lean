/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticCategoricalIncompleteness
public import CategoricalEssentialIncompleteness.RecursivePairs

/-! # Numeral observations as a functor on consistent c.e. PA extensions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication

abbrev Theory := {T : ArithmeticTheory // T.RE ∧ 𝗣𝗔 ⪯ T ∧ Consistent T}

instance (T : Theory) : T.val.RE := T.property.1
instance (T : Theory) : 𝗣𝗔 ⪯ T.val := T.property.2.1

def positiveObservations (T : ArithmeticTheory) : Set ℕ :=
  {n | T ⊢ thetaSentence n}
def negativeObservations (T : ArithmeticTheory) : Set ℕ :=
  {n | T ⊢ ∼thetaSentence n}

theorem observations_enumerable (T : ArithmeticTheory) [T.RE] :
    REPred (· ∈ positiveObservations T) ∧ REPred (· ∈ negativeObservations T) := by
  constructor
  · exact ((theoremCodes_re T).comp thetaCode_computable).of_eq
      (fun n => mem_theoremCodes_encode T (thetaSentence n))
  · exact ((theoremCodes_re T).comp (negationCode_computable.comp thetaCode_computable)).of_eq
      (fun n => by rw [thetaCode,negationCode_encode,mem_theoremCodes_encode]; rfl)

theorem observations_disjoint (T : ArithmeticTheory) (hT : Consistent T) :
    Disjoint (positiveObservations T) (negativeObservations T) := by
  letI := hT
  exact Set.disjoint_left.mpr (fun n hp hn =>
    ArithmeticRepresentation.consistent_not_both T (thetaSentence n) ⟨hp,hn⟩)

def observedPair (T : Theory) : RecursivePairs.Object where
  carrier := ClassicalPrograms.U
  positive := ClassicalPrograms.supportIdem (positiveObservations T.val)
    (observations_enumerable T.val).1
  negative := ClassicalPrograms.supportIdem (negativeObservations T.val)
    (observations_enumerable T.val).2
  disjoint := RecursivePairs.supportIdems_disjoint _ _ _ _
    (observations_disjoint T.val T.property.2.2)

theorem observations_mono {T T' : ArithmeticTheory} [T ⪯ T'] :
    positiveObservations T ⊆ positiveObservations T' ∧
      negativeObservations T ⊆ negativeObservations T' :=
  ⟨fun _ h => WeakerThan.pbl h,fun _ h => WeakerThan.pbl h⟩

def observationFunctor : Theory ⥤ RecursivePairs.Object where
  obj := observedPair
  map {T T'} f := by
    haveI : T.val ⪯ T'.val := Axiomatized.le_of_subset (show T.val ⊆ T'.val from leOfHom f)
    exact
      { map := 𝟙 ClassicalPrograms.U
        total := rst_id _
        positive := by
          change ClassicalPrograms.supportIdem (positiveObservations T.val) (observations_enumerable T.val).1 ≤
            Idem.pull (𝟙 ClassicalPrograms.U)
              (ClassicalPrograms.supportIdem (positiveObservations T'.val) (observations_enumerable T'.val).1)
          rw [Idem.pull_id]
          exact ClassicalPrograms.supportIdem_le _ _ (observations_mono (T := T.val)).1
        negative := by
          change ClassicalPrograms.supportIdem (negativeObservations T.val) (observations_enumerable T.val).2 ≤
            Idem.pull (𝟙 ClassicalPrograms.U)
              (ClassicalPrograms.supportIdem (negativeObservations T'.val) (observations_enumerable T'.val).2)
          rw [Idem.pull_id]
          exact ClassicalPrograms.supportIdem_le _ _ (observations_mono (T := T.val)).2 }
  map_id _ := by apply RecursivePairs.Hom.ext; rfl
  map_comp _ _ := by
    apply RecursivePairs.Hom.ext
    exact (Category.id_comp (𝟙 ClassicalPrograms.U)).symm

theorem observations_bounds (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PartialFunctions.support (ClassicalPrograms.inclusionRangeFunctor.mapIdem ClassicalPrograms.evenDiagonal) ⊆ positiveObservations T ∧
      PartialFunctions.support (ClassicalPrograms.inclusionRangeFunctor.mapIdem ClassicalPrograms.oddDiagonal) ⊆ negativeObservations T := by
  constructor
  · intro n hn
    exact WeakerThan.pbl (ClassicalPrograms.output_numeral_provable 0 n ((ClassicalPrograms.evenDiagonal_support n).mp hn))
  · intro n hn
    exact WeakerThan.pbl (ClassicalPrograms.odd_output_refutes_even n ((ClassicalPrograms.oddDiagonal_support n).mp hn))

def diagonalPair : RecursivePairs.Object where
  carrier := ClassicalPrograms.U
  positive := ClassicalPrograms.evenDiagonal
  negative := ClassicalPrograms.oddDiagonal
  disjoint := ClassicalPrograms.diagonal_inseparable.disjoint

theorem le_supportIdem_iff (a : Idem ClassicalPrograms.U) (P : Set ℕ)
    (hP : REPred (· ∈ P)) : a ≤ ClassicalPrograms.supportIdem P hP ↔
      PartialFunctions.support (ClassicalPrograms.inclusionRangeFunctor.mapIdem a) ⊆ P := by
  constructor
  · intro h
    have hm := ClassicalPrograms.inclusionRangeFunctor.map_mono h
    rw [PartialFunctions.le_iff_support,ClassicalPrograms.supportIdem_image,
      PartialFunctions.support_setIdem] at hm
    exact hm
  · intro h
    have hm : ClassicalPrograms.inclusionRangeFunctor.mapIdem a ≤
        ClassicalPrograms.inclusionRangeFunctor.mapIdem (ClassicalPrograms.supportIdem P hP) := by
      rw [ClassicalPrograms.supportIdem_image,PartialFunctions.le_iff_support,
        PartialFunctions.support_setIdem]
      exact h
    apply Idem.le_def.mpr
    apply ClassicalPrograms.J.map_injective
    rw [ClassicalPrograms.J.map_comp]
    exact Idem.le_def.mp hm

/-- The identity pair morphism from the actual categorical diagonal pair. -/
def diagonalToObservation (T : Theory) : diagonalPair ⟶ observedPair T where
  map := 𝟙 ClassicalPrograms.U
  total := rst_id _
  positive := by
    change ClassicalPrograms.evenDiagonal ≤ Idem.pull (𝟙 ClassicalPrograms.U)
      (ClassicalPrograms.supportIdem (positiveObservations T.val) (observations_enumerable T.val).1)
    rw [Idem.pull_id,le_supportIdem_iff]
    exact (observations_bounds T.val).1
  negative := by
    change ClassicalPrograms.oddDiagonal ≤ Idem.pull (𝟙 ClassicalPrograms.U)
      (ClassicalPrograms.supportIdem (negativeObservations T.val) (observations_enumerable T.val).2)
    rw [Idem.pull_id,le_supportIdem_iff]
    exact (observations_bounds T.val).2

theorem recursiveSupport_complementary (D : Set ℕ) (hD : ComputablePred (· ∈ D)) :
    Complementary (ClassicalPrograms.supportIdem D hD.to_re)
      (ClassicalPrograms.supportIdem Dᶜ hD.not.to_re) := by
  have hi : Function.Injective
      (ClassicalPrograms.inclusionRangeFunctor.mapIdem (X := ClassicalPrograms.U)) := by
    intro a b h
    exact Idem.ext (ClassicalPrograms.J.map_injective (congrArg Idem.hom h))
  constructor
  · apply hi
    rw [RangeFunctor.map_inf,RangeFunctor.map_bot,ClassicalPrograms.supportIdem_image,
      ClassicalPrograms.supportIdem_image]
    apply PartialFunctions.support_injective
    simp
  · apply hi
    rw [RangeFunctor.map_sup,RangeFunctor.map_top,ClassicalPrograms.supportIdem_image,
      ClassicalPrograms.supportIdem_image]
    apply PartialFunctions.support_injective
    simp

/-- The parameter observations inherit recursive inseparability from the
new categorical diagonal construction, under consistency alone. -/
theorem observations_recursivelyInseparable (T : ArithmeticTheory)
    [𝗣𝗔 ⪯ T] [T.RE] (hT : Consistent T) :
    Numerical.RecursivelyInseparable (positiveObservations T) (negativeObservations T) := by
  refine ⟨observations_disjoint T hT,?_⟩
  rintro ⟨D,hD,hp,hn⟩
  apply ClassicalPrograms.diagonal_inseparable.no_separator
  refine ⟨ClassicalPrograms.supportIdem D hD.to_re,
    ClassicalPrograms.supportIdem Dᶜ hD.not.to_re,recursiveSupport_complementary D hD,?_,?_⟩
  · rw [le_supportIdem_iff]
    exact (observations_bounds T).1.trans hp
  · rw [le_supportIdem_iff]
    intro n hmem hd
    exact Set.disjoint_left.mp hn hd ((observations_bounds T).2 hmem)

end CategoricalEssentialIncompleteness.LocalConnectedness.ArithmeticApplication
