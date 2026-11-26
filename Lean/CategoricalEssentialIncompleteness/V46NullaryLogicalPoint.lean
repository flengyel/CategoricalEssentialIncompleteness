/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46NullarySyntaxInterpretation
public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import CategoricalEssentialIncompleteness.V46FirstOrderReflection

/-! # A closed logical theorem and its factorization through every theory -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NullaryLogicalPoint
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X Z : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (label : Z ⟶ X)

theorem append_nil (L : StableListAlgebra V) :
    prod.lift (terminal.from Z ≫ L.algebra.nil) (terminal.from Z ≫ L.algebra.nil) ≫
      L.append = terminal.from Z ≫ L.algebra.nil := by
  have h := L.appendParameterValue_nil (terminal.from Z ≫ L.algebra.nil)
  unfold StableListAlgebra.append
  rw [← Category.assoc, ← Category.assoc, prod.comp_lift, prod.lift_snd, prod.lift_fst]
  simpa only [StableListAlgebra.appendParameterValue, Category.assoc] using h

theorem implication_closed (a b : Z ⟶ S.algebra.a.2)
    (ha : a ≫ S.formulaOccurrences = terminal.from Z ≫ S.lists.algebra.nil)
    (hb : b ≫ S.formulaOccurrences = terminal.from Z ≫ S.lists.algebra.nil) :
    (prod.lift a b ≫ S.implicationConstructor) ≫ S.formulaOccurrences =
      terminal.from Z ≫ S.lists.algebra.nil := by
  rw [Category.assoc, S.implication_occurrences, ← Category.assoc, prod.lift_map, ha, hb]
  exact append_nil S.lists

def atom : Z ⟶ S.algebra.a.2 := label ≫ NullaryInterpretation.atomFormula S

theorem atom_closed : atom S label ≫ S.formulaOccurrences =
    terminal.from Z ≫ S.lists.algebra.nil := by
  rw [atom, Category.assoc, NullaryInterpretation.atom_occurrences, ← Category.assoc,
    terminal.comp_from]

/-- The first Hilbert scheme at one propositional atom is a sentence. -/
def formula : Z ⟶ S.algebra.a.2 := prod.lift (atom S label) (atom S label) ≫ S.hilbertOne

theorem formula_closed : formula S label ≫ S.formulaOccurrences =
    terminal.from Z ≫ S.lists.algebra.nil := by
  unfold formula CategoricalSyntax.hilbertOne
  rw [← Category.assoc, prod.comp_lift, prod.lift_fst]
  rw [← Category.assoc, prod.comp_lift, prod.lift_snd, prod.lift_fst]
  change (prod.lift (atom S label)
    (prod.lift (atom S label) (atom S label) ≫ S.implicationConstructor) ≫
      S.implicationConstructor) ≫ S.formulaOccurrences = _
  exact implication_closed S _ _ (atom_closed S label)
    (implication_closed S _ _ (atom_closed S label) (atom_closed S label))

def sentence : Z ⟶ S.sentenceObject :=
  pullback.lift (formula S label) (terminal.from Z) (formula_closed S label)

def logicalInstance : Z ⟶ S.logicalParameters :=
  prod.lift (atom S label) (atom S label) ≫
    coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl

theorem logicalInstance_formula :
    logicalInstance S label ≫ S.logicalAxioms = sentence S label ≫ S.sentenceInclusion := by
  simp only [logicalInstance, CategoricalSyntax.logicalAxioms, Category.assoc,
    coprod.inl_desc, sentence, CategoricalSyntax.sentenceInclusion, pullback.lift_fst]
  rfl

section EveryTheory
variable {L Fm Sent W : D} (logical : L ⟶ Fm) (inclusion : Sent ⟶ Fm)
variable (all : W ⨯ Fm ⟶ Fm) (imp : Fm ⨯ Fm ⟶ Fm)
variable (proofs : (A : Subobject Sent) →
  Endofunctor.Algebra (firstOrderRules logical inclusion A.arrow all imp).inference)
variable (point : Z ⟶ Sent) (instancePoint : Z ⟶ L)
variable (comm : instancePoint ≫ logical = point ≫ inclusion)

include comm in
/-- A closed logical instance factors through every closed sentence theory.
Only the proof algebra at the theory's axiom subobject is used. -/
theorem factors (U : FirstOrderReflection.Theory proofs) :
    ∃ u : Z ⟶ (U.val : D), u ≫ U.val.arrow = point := by
  let R := firstOrderRules logical inclusion U.val.arrow all imp
  let p : Z ⟶ (proofs U.val).a.left :=
    instancePoint ≫ coprod.inl ≫ R.nullaryToProof (proofs U.val)
  have hp : p ≫ (proofs U.val).a.hom = point ≫ inclusion := by
    dsimp only [p]
    rw [Category.assoc, Category.assoc, RulePresentation.nullaryToProof_conclusion]
    change instancePoint ≫ (coprod.inl ≫ coprod.desc logical (U.val.arrow ≫ inclusion)) = _
    rw [coprod.inl_desc]
    exact comm
  let q := pullback.lift p point hp
  let A := FirstOrderReflection.generated proofs U.val
  let k := q ≫ factorThruImageSubobject (FirstOrderReflection.conclusion proofs U.val)
  refine ⟨k ≫ Subobject.ofLE A U.val U.property.le, ?_⟩
  rw [Category.assoc, Subobject.ofLE_arrow]
  change (q ≫ factorThruImageSubobject _) ≫ (imageSubobject _).arrow = point
  rw [Category.assoc, imageSubobject_arrow_comp]
  exact pullback.lift_snd _ _ _
end EveryTheory
end CategoricalEssentialIncompleteness.V46.NullaryLogicalPoint
