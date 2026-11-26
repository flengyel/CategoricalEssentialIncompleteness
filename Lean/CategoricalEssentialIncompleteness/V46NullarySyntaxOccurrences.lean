/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebra
public import CategoricalEssentialIncompleteness.V46NullarySyntaxInterpretation
public import CategoricalEssentialIncompleteness.V46StableListComparison
public import CategoricalEssentialIncompleteness.V46VariableTests

/-! # Occurrence lists under interpretation of propositional atoms -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)

/-- Changing the chosen list algebra leaves the syntax polynomial and
its initial algebra unchanged. -/
def withTargetLists : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0 :=
  { S with decidableVariables := Q.decidableVariables, lists := Q.lists }

def occurrenceTarget := (withTargetLists S Q).occurrenceAlgebra

def listComparisonHom : S.occurrenceAlgebra ⟶ occurrenceTarget S Q := by
  let m := StableListAlgebra.Comparison.map S.lists Q.lists
  refine NullarySyntaxAlgebra.homOfConstructors (m, m) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [NullarySyntaxAlgebra.variableConstructor, occurrenceTarget, withTargetLists,
      CategoricalSyntax.occurrenceAlgebra, m,
      coprod.inl_desc, coprod.inr_desc,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
      StableListAlgebra.Comparison.singleton S.lists Q.lists
  · simpa [NullarySyntaxAlgebra.equalityConstructor, occurrenceTarget, withTargetLists,
      CategoricalSyntax.occurrenceAlgebra, m,
      coprod.inl_desc, coprod.inr_desc,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
      StableListAlgebra.Comparison.append S.lists Q.lists
  · simp [NullarySyntaxAlgebra.atomConstructor, occurrenceTarget, withTargetLists,
      CategoricalSyntax.occurrenceAlgebra, m,
      coprod.inl_desc, coprod.inr_desc,  StableListAlgebra.constructorOccurrences,
      StableListAlgebra.tupleAppend, Category.assoc]
    rfl
  · simp [NullarySyntaxAlgebra.negationConstructor, occurrenceTarget, withTargetLists,
      CategoricalSyntax.occurrenceAlgebra, m,
      coprod.inl_desc, coprod.inr_desc]
  · simpa [NullarySyntaxAlgebra.implicationConstructor, occurrenceTarget, withTargetLists,
      CategoricalSyntax.occurrenceAlgebra, m,
      coprod.inl_desc, coprod.inr_desc,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using
      StableListAlgebra.Comparison.append S.lists Q.lists
  · have hE := S.decidableVariables.unique Q.decidableVariables
    simpa [NullarySyntaxAlgebra.quantifierConstructor, occurrenceTarget, withTargetLists,
      CategoricalSyntax.occurrenceAlgebra, m,
      coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, hE] using
      StableListAlgebra.Comparison.deletion S.lists Q.lists Q.decidableVariables

variable (f : X ⟶ Q.sentenceObject)

theorem sentence_occurrences : Q.sentenceInclusion ≫ Q.formulaOccurrences =
    terminal.from Q.sentenceObject ≫ Q.lists.algebra.nil := by
  have h : pullback.fst Q.formulaOccurrences Q.lists.algebra.nil ≫ Q.formulaOccurrences =
      pullback.snd Q.formulaOccurrences Q.lists.algebra.nil ≫ Q.lists.algebra.nil :=
    pullback.condition
  have ht : pullback.snd Q.formulaOccurrences Q.lists.algebra.nil =
      terminal.from Q.sentenceObject := Subsingleton.elim _ _
  rw [ht] at h
  exact h

def interpretationOccurrenceHom : interpretationAlgebra Q f ⟶ occurrenceTarget S Q := by
  refine NullarySyntaxAlgebra.homOfConstructors
    (Q.termOccurrences, Q.formulaOccurrences) ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [NullarySyntaxAlgebra.variableConstructor, interpretationAlgebra,
      occurrenceTarget, withTargetLists, CategoricalSyntax.occurrenceAlgebra,
      coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc] using Q.variable_occurrences
  · simpa [NullarySyntaxAlgebra.equalityConstructor, interpretationAlgebra,
      occurrenceTarget, withTargetLists, CategoricalSyntax.occurrenceAlgebra,
      coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc] using Q.equality_occurrences
  · simp only [occurrenceTarget, CategoricalSyntax.occurrenceAlgebra, withTargetLists,
      StableListAlgebra.constructorOccurrences, SyntaxPolynomial.eval_power_zero,
      StableListAlgebra.tupleAppend, SyntaxPolynomial.eval_power_two, interpretationAlgebra,
      NullarySyntaxAlgebra.atomConstructor, coprod.inl_desc, coprod.inr_desc, Category.assoc,
      sentence_occurrences Q, terminal.comp_from_assoc]
    rw [← Category.assoc]
    congr 1
    exact Subsingleton.elim _ _
  · simpa [NullarySyntaxAlgebra.negationConstructor, interpretationAlgebra,
      occurrenceTarget, withTargetLists, CategoricalSyntax.occurrenceAlgebra,
      coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc] using Q.negation_occurrences
  · simpa [NullarySyntaxAlgebra.implicationConstructor, interpretationAlgebra,
      occurrenceTarget, withTargetLists, CategoricalSyntax.occurrenceAlgebra,
      coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc] using Q.implication_occurrences
  · simpa [NullarySyntaxAlgebra.quantifierConstructor, interpretationAlgebra,
      occurrenceTarget, withTargetLists, CategoricalSyntax.occurrenceAlgebra,
      coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
      Category.assoc] using Q.quantifier_occurrences

theorem occurrence_comparison :
    (S.termOccurrences ≫ StableListAlgebra.Comparison.map S.lists Q.lists,
      S.formulaOccurrences ≫ StableListAlgebra.Comparison.map S.lists Q.lists) =
    ((interpretation S Q f).1 ≫ Q.termOccurrences,
      (interpretation S Q f).2 ≫ Q.formulaOccurrences) := by
  have h := S.initial.hom_ext
    (S.initial.to S.occurrenceAlgebra ≫ listComparisonHom S Q)
    (S.initial.to (interpretationAlgebra Q f) ≫ interpretationOccurrenceHom S Q f)
  exact congrArg Endofunctor.Algebra.Hom.f h

theorem formula_occurrences : (interpretation S Q f).2 ≫ Q.formulaOccurrences =
    S.formulaOccurrences ≫ StableListAlgebra.Comparison.map S.lists Q.lists :=
  (congrArg Prod.snd (occurrence_comparison S Q f)).symm

theorem term_occurrences : (interpretation S Q f).1 ≫ Q.termOccurrences =
    S.termOccurrences ≫ StableListAlgebra.Comparison.map S.lists Q.lists :=
  (congrArg Prod.fst (occurrence_comparison S Q f)).symm

def sentenceInterpretation : S.sentenceObject ⟶ Q.sentenceObject :=
  pullback.lift (S.sentenceInclusion ≫ (interpretation S Q f).2)
    (terminal.from S.sentenceObject) (by
      rw [Category.assoc, formula_occurrences, ← Category.assoc, sentence_occurrences S,
        Category.assoc, StableListAlgebra.Comparison.nil])

@[reassoc (attr := simp)] theorem sentenceInterpretation_inclusion :
    sentenceInterpretation S Q f ≫ Q.sentenceInclusion =
      S.sentenceInclusion ≫ (interpretation S Q f).2 := pullback.lift_fst _ _ _

theorem sentenceInterpretation_atom : atomSentence S ≫ sentenceInterpretation S Q f = f := by
  apply (cancel_mono Q.sentenceInclusion).mp
  rw [Category.assoc, sentenceInterpretation_inclusion, ← Category.assoc,
    atomSentence_inclusion, atom]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
