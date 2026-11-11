/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFibers

/-! # Ternary graphs of actual morphisms from constant parameter families -/

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
variable {P C : PredicateCategory T} {X : Over P}

/-- A candidate categorical fold supplies its own ternary graph. The
source coordinate is the child word, rather than the full product code. -/
def rawArrow (f : constantFamily P C ⟶ X) : TernaryGraph :=
  let R := constantLeaf T P C
  let g := (chosenGraph T f.left).graph
  .mkSigma “p u v. ∃ z, !R.val p u z ∧ !g.val z v”

@[simp] theorem rawArrow_eval {M : Type} [ORingStructure M]
    (f : constantFamily P C ⟶ X) (p u v : M) :
    (rawArrow T f).val.Evalb ![p, u, v] ↔ ∃ z : M,
      (constantLeaf T P C).val.Evalb ![p, u, z] ∧
        (chosenGraph T f.left).graph.val.Evalb ![z, v] := by
  simp [rawArrow]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- A candidate graph has the full source and target-fiber support solely
because the original arrow is a morphism over the parameter. -/
theorem rawArrow_support (f : constantFamily P C ⟶ X) (p u v : M)
    (h : (rawArrow T f).val.Evalb ![p, u, v]) :
    P.val.Evalb ![p] ∧ C.val.Evalb ![u] ∧ X.left.val.Evalb ![v] ∧
      (chosenGraph T X.hom).graph.val.Evalb ![v, p] := by
  obtain ⟨z, hz, hfv⟩ := (rawArrow_eval T f p u v).mp h
  have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z, p] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z, u] := by
    simpa [constantLeaf] using hz
  have hs₁ := (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).support_model M z p hh.1
  have hs₂ := (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).support_model M z u hh.2
  exact ⟨hs₁.2, hs₂.2, ((chosenGraph T f.left).support_model M z v hfv).2,
    overGraph_target T M f z v p hfv hh.1⟩

/-- The graph is evaluated on every parameter and coefficient point,
including nonstandard elements in nonstandard models. -/
theorem rawArrow_existsUnique (f : constantFamily P C ⟶ X)
    (p : Obj T M P) (u : Obj T M C) :
    ∃! v : Obj T M X.left, (rawArrow T f).val.Evalb ![p.val, u.val, v.val] := by
  obtain ⟨z, hz, hzu⟩ := constantLeaf_existsUnique T M P C p u
  let v := (F T M).map f.left z
  refine ⟨v, (rawArrow_eval T f p.val u.val v.val).mpr
    ⟨z.val, hz.1, (chosenGraph_map_iff T M f.left z v).mpr rfl⟩, ?_⟩
  intro v' hv'
  obtain ⟨z', hz', hfv'⟩ := (rawArrow_eval T f p.val u.val v'.val).mp hv'
  have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z', p.val] ∧
      (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z', u.val] := by
    simpa [constantLeaf] using hz'
  let zz' : Obj T M (P ⨯ C) :=
    ⟨z', ((chosenGraph T (prod.fst : P ⨯ C ⟶ P)).support_model M z' p.val hh.1).1⟩
  have he := hzu zz' ⟨hz', (chosenGraph_map_iff T M prod.fst zz' p).mp hh.1⟩
  have hf := (chosenGraph_map_iff T M f.left zz' v').mp hfv'
  exact hf.symm.trans (congrArg ((F T M).map f.left) he)


/-- On the unique product point over the given parameter and child word,
the ternary candidate graph is exactly the original categorical arrow. -/
theorem rawArrow_model (f : constantFamily P C ⟶ X)
    (p : Obj T M P) (u : Obj T M C) (z : Obj T M (P ⨯ C))
    (v : Obj T M X.left)
    (hz : (constantLeaf T P C).val.Evalb ![p.val, u.val, z.val]) :
    (rawArrow T f).val.Evalb ![p.val, u.val, v.val] ↔ (F T M).map f.left z = v := by
  constructor
  · intro h
    obtain ⟨z', hz', hfv⟩ := (rawArrow_eval T f p.val u.val v.val).mp h
    have hh : (chosenGraph T (prod.fst : P ⨯ C ⟶ P)).graph.val.Evalb ![z', p.val] ∧
        (chosenGraph T (prod.snd : P ⨯ C ⟶ C)).graph.val.Evalb ![z', u.val] := by
      simpa [constantLeaf] using hz'
    let zz' : Obj T M (P ⨯ C) :=
      ⟨z', ((chosenGraph T (prod.fst : P ⨯ C ⟶ P)).support_model M z' p.val hh.1).1⟩
    obtain ⟨hz₁, hz₂⟩ := (constantLeaf_model T M P C p u z).mp hz
    obtain ⟨hz₁', hz₂'⟩ := (constantLeaf_model T M P C p u zz').mp hz'
    have he : zz' = z := modelProduct_ext T M (hz₁'.trans hz₁.symm) (hz₂'.trans hz₂.symm)
    have hf := (chosenGraph_map_iff T M f.left zz' v).mp hfv
    rw [he] at hf
    exact hf
  · intro h
    exact (rawArrow_eval T f p.val u.val v.val).mpr
      ⟨z.val, hz, (chosenGraph_map_iff T M f.left z v).mpr h⟩


/-- Applying an actual slice arrow changes the raw child-word coordinate
into the full underlying target value, while retaining the parameter. -/
theorem rawArrow_fiberLeaf (f : constantFamily P C ⟶ X)
    (p : Obj T M P) (u v : M) (z : Obj T M (P ⨯ C))
    (hz : (constantLeaf T P C).val.Evalb ![p.val, u, z.val])
    (h : (rawArrow T f).val.Evalb ![p.val, u, v]) :
    (fiberLeaf T P X).val.Evalb ![p.val, v, ((F T M).map f.left z).val] := by
  obtain ⟨_, hu, hv, hvp⟩ := rawArrow_support T M f p.val u v h
  let uu : Obj T M C := ⟨u, hu⟩
  let vv : Obj T M X.left := ⟨v, hv⟩
  have he := (rawArrow_model T M f p uu z vv hz).mp h
  apply (fiberLeaf_model T M P X p vv ((F T M).map f.left z)).mpr
  refine ⟨he, ?_⟩
  rw [he]
  exact (chosenGraph_map_iff T M X.hom vv p).mp hvp

end Models

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
