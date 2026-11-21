/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedCoding
public import CategoricalEssentialIncompleteness.OracleProgramSpecialization

/-! # The oracle-domain Turing morphism with ordinary recursive values -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable (S : Set ℕ)
attribute [instance 2000] nativeRestriction

def tau : product (N S) (N S) ⟶ N S := by
  let D (p : ℕ × ℕ) := oracleDomain S (Nat.unpair p.1).2 p.2
  let f₀ (p : ℕ × ℕ) := ordinaryEval (Nat.unpair p.1).1 p.2
  have hd : Computable (fun p : ℕ × ℕ => ((Nat.unpair p.1).2,p.2)) := Computable.pair
    (Computable.snd.comp (Computable.unpair.comp Computable.fst)) Computable.snd
  have hD : FiniteOracleRE S D := FiniteOracleRE.comp
    (p := fun q : ℕ × ℕ => oracleDomain S q.1 q.2)
    (f := fun p : ℕ × ℕ => ((Nat.unpair p.1).2,p.2)) hd (oracleDomain_uniform S)
  have hf : Partrec f₀ := ordinaryEval_partrec.comp
    (Computable.fst.comp (Computable.unpair.comp Computable.fst)) Computable.snd
  refine ⟨fun p => Part.assert (D p) (fun _ => f₀ p),?_,⟨f₀,hf,?_⟩⟩
  · exact (hD.and (FiniteOracleRE.of_re hf.dom_re)).of_eq (fun p => by simp [Part.assert])
  · intro p y hy
    obtain ⟨_,hy⟩ := Part.mem_assert_iff.mp hy
    exact hy

theorem mem_tau (q x y : ℕ) : y ∈ (tau S).val (q,x) ↔
    oracleDomain S (Nat.unpair q).2 x ∧ y ∈ ordinaryEval (Nat.unpair q).1 x := by
  simp only [tau,Part.mem_assert_iff,exists_prop]

/-- Both the ordinary extension program and the oracle-domain program are
specialized by ordinary recursive compilers. Equality includes all domains. -/
theorem tau_parameterization (Y : Restricted S) (f : product Y (N S) ⟶ N S) :
    ∃ r : Y ⟶ N S,isTotal r ∧ productMap r (𝟙 (N S)) ≫ tau S=f := by
  obtain ⟨f₀,hf,he⟩ := f.extension
  have hf' : Partrec (fun p : carrier S Y × ℕ => f₀ p) := hf
  obtain ⟨e,hec,hev⟩ := ordinary_program_specialization hf'
  have hd : FiniteOracleRE S (fun p : carrier S Y × ℕ => (f.val p).Dom) := f.domain
  obtain ⟨a,hac,hav⟩ := oracleDomain_specialization S hd
  let r : Y ⟶ N S := totalFromFunction (fun z => Nat.pair (e z) (a z))
    (Primrec₂.natPair.to_comp.comp hec hac)
  refine ⟨r,totalFromFunction_total _ _,?_⟩
  apply hom_ext_mem
  rintro ⟨z,x⟩ y
  simp only [comp_val,productMap_val,id_val,r,totalFromFunction,ofPartrec,
    Part.bind_some,Part.map_some]
  rw [mem_tau,Nat.unpair_pair,hev,hav]
  exact (he.mem_iff (z,x) y).symm

theorem tau_isTuring : RecursionCategory.IsTuringMorphism (tau S) := by
  intro Y f
  obtain ⟨r,hr,he⟩ := tau_parameterization S Y f
  refine ⟨r,?_,he⟩
  change PCategoryStruct.rst r=𝟙 Y
  rw [induced_restriction]
  exact hr

instance recursionCategory : RecursionCategory.PRecursionCategory (Restricted S) where
  W := N S
  X := N S
  Y := N S
  tau := tau S
  is_turing := tau_isTuring S

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
