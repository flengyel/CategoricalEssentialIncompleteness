/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalRealization

/-! # The recursive isomorphism between the formal N² and N types -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.TypedRecursionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

def U2 : Rec := Q.obj (object 𝗣𝗔 (.product .omega .omega))

def pairCodeIso : U2 ≅ U := Q.mapIso (omegaProductIso 𝗣𝗔)

theorem pairCode_mem (x : ℕ × ℕ) (y : ℕ) :
    y ∈ J.map pairCodeIso.hom x ↔ y=Nat.pair x.1 x.2 := by
  change y ∈ J.map (Q.map (arrowOfIndex 𝗣𝗔 (.product .omega .omega) .omega
    Kleene.identityIndex)) x ↔ _
  rw [mem_standard_index,Kleene.identityIndex_spec]
  change y ∈ Part.some (SyntacticModel.codingEquiv 𝗣𝗔 ℕ (.product .omega .omega) x).val ↔ _
  simp only [Part.mem_some_iff]
  change (y=⟪x.1,x.2⟫) ↔ y=Nat.pair x.1 x.2
  rw [nat_pair_eq]

theorem pair_pull_support (A : Set ℕ) (hA : REPred (· ∈ A)) (x : ℕ × ℕ) :
    x ∈ J.map (Idem.pull pairCodeIso.hom (supportIdem A hA)).hom x ↔
      Nat.pair x.1 x.2 ∈ A := by
  change x ∈ J.map (RestrictionCategory.rst (pairCodeIso.hom ≫ (supportIdem A hA).hom)) x ↔ _
  rw [J_rst,J.map_comp,PartialFunctions.mem_rst]
  simp only [PartialFunctions.mem_comp,and_true]
  change (∃ z : ℕ,∃ y : ℕ,y ∈ J.map pairCodeIso.hom x ∧ z ∈ supportIdentity A y) ↔ _
  simp only [pairCode_mem,mem_supportIdentity,exists_eq_left,exists_eq_right]

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
