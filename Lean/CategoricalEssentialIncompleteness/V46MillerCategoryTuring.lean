/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryJoins
public import CategoricalEssentialIncompleteness.V46MillerUnanimity

/-! # The unanimous evaluator is a Turing morphism

The realizer of tau is the fixed program from Lemma8.1. A parameter
compiler uses only the ordinary recursive specialization of a supplied
uniform index, before choosing any representation.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
attribute [instance 2000] nativeRestriction

def tau (z : Point) : product (N (Family.ofPoint z)) (N (Family.ofPoint z)) ⟶ N (Family.ofPoint z) :=
  ⟨fun a => Unanimity.tau z a.1 a.2,⟨Unanimity.unanimityIndex,by
    intro p hp a m
    exact (Unanimity.tau_graph z a.1 a.2 m).trans
      (Unanimity.unanimityIndex_graph z p hp a.1 a.2 m).symm⟩⟩

theorem tau_graph (z : Point) (e n m : ℕ) :
    m ∈ (tau z).val (e,n) ↔ ∀ p ∈ representations z,
      m ∈ OracleProgram.numberedEval e p n := Unanimity.tau_graph z e n m

theorem tau_is_literal (z : Point) (e n : ℕ) :
    (tau z).val (e,n) = Unanimity.tau z e n := rfl

def parameterIndex {P : Family} (e : ℕ) (X : Object P) (x : carrier P X) : ℕ :=
  OracleProgram.specializationIndex e (X.type.toNat x)

theorem parameterIndex_computable {P : Family} (e : ℕ) (X : Object P) : Computable (parameterIndex e X) :=
  OracleProgram.specializationIndex_computable.comp (Computable.const e) X.type.toNat_computable

theorem parameterIndex_eval {P : Family} (e : ℕ) (X : Object P) (x : carrier P X) (p : Bits) (n : ℕ) :
    OracleProgram.numberedEval (parameterIndex e X x) p n =
      OracleProgram.numberedEval e p (Nat.pair (X.type.toNat x) n) :=
  OracleProgram.specializationIndex_eval e (X.type.toNat x) p n

theorem tau_parameterization (z : Point) (Y : PointObject z)
    (f : product Y (N (Family.ofPoint z)) ⟶ N (Family.ofPoint z)) :
    ∃ r : Y ⟶ N (Family.ofPoint z),isTotal r ∧ productMap r (𝟙 (N (Family.ofPoint z))) ≫ tau z = f := by
  obtain ⟨e,he⟩ := f.represented
  let r : Y ⟶ N (Family.ofPoint z) := totalFromFunction (parameterIndex e Y) (parameterIndex_computable e Y)
  refine ⟨r,totalFromFunction_total _ _,?_⟩
  apply hom_ext_mem
  rintro ⟨y,n⟩ m
  simp only [comp_val,productMap_val,id_val,r,totalFromFunction,ofPartrec,
    Part.bind_some,Part.map_some,parameterIndex]
  rw [tau_graph]
  constructor
  · intro h
    obtain ⟨p,hp⟩ := representations_nonempty z
    have hm := h p hp
    rw [OracleProgram.specializationIndex_eval] at hm
    exact (he p hp (y,n) m).mpr hm
  · intro h p hp
    rw [OracleProgram.specializationIndex_eval]
    exact (he p hp (y,n) m).mp h

theorem tau_isTuring (z : Point) : RecursionCategory.IsTuringMorphism (tau z) := by
  intro Y f
  obtain ⟨r,hr,he⟩ := tau_parameterization z Y f
  refine ⟨r,?_,he⟩
  change PCategoryStruct.rst r = 𝟙 Y
  rw [induced_restriction]
  exact hr

instance recursionCategory (z : Point) : RecursionCategory.PRecursionCategory (PointObject z) where
  W := N (Family.ofPoint z)
  X := N (Family.ofPoint z)
  Y := N (Family.ofPoint z)
  tau := tau z
  is_turing := tau_isTuring z

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
