/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecode

/-! # The decoded operation agrees with the categorical operation -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {P : PredicateCategory T} (X : Over P × Over P)
variable (a : SyntaxPolynomial (PredicateCategory T)) {Z : Over P}

/-- Fixing a raw coordinate fixes its slice-polynomial point. Decoding the operation
therefore loses no information about its value. -/
theorem decodedOperation_model (f : (a.withParameters P).eval.obj X ⟶ Z)
    (p : Obj T M P) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj X).left) (v : Obj T M Z.left)
    (hz : (fiberRepresentation T P X a).val.Evalb ![p.val, u, z.val]) :
    (decodedOperation T X a f).val.Evalb ![p.val, u, v.val] ↔
      (F T M).map f.left z = v := by
  constructor
  · intro h
    obtain ⟨z', hz', hfv⟩ := (decodedOperation_eval T X a f p.val u v.val).mp h
    have hs := fiberRepresentation_support T M P X a p.val u z.val hz
    obtain ⟨z₀, _, hzu⟩ := fiberRepresentation_existsUnique T M P X a p u hs.1
    let zz' : Obj T M ((a.withParameters P).eval.obj X).left :=
      ⟨z', (fiberRepresentation_support T M P X a p.val u z' hz').2.1⟩
    have he : zz' = z := (hzu zz' hz').trans (hzu z hz).symm
    have hf := (chosenGraph_map_iff T M f.left zz' v).mp hfv
    rw [he] at hf
    exact hf
  · intro h
    exact (decodedOperation_eval T X a f p.val u v.val).mpr
      ⟨z.val, hz, (chosenGraph_map_iff T M f.left z v).mpr h⟩

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
