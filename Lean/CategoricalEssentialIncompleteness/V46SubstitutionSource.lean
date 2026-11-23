/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainFreeForTheory
public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesPresentation

/-! # The two substitution branches on supported syntax in Proposition 6.7 -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

open ConcreteNamedSubstitution SyntacticSyntax
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

/-- The components of a raw triple are the variable, the replacement and the formula. -/
def substitutionSource (p : ℕ × ℕ × ℕ) : Prop :=
  V.val.Evalb ![p.1] ∧ (plainSyntaxCarrier V σ π d false).val.Evalb ![p.2.1] ∧
    (plainSyntaxCarrier V σ π d true).val.Evalb ![p.2.2]

private theorem supportedTag_enumerable {V Tm Fm : ℕ → Prop} {b : ℕ × ℕ × ℕ → ℕ}
    (hv : REPred V) (ht : REPred Tm) (hw : REPred Fm) (hb : Primrec b) (j : ℕ) :
    REPred (fun p : ℕ × ℕ × ℕ => (V p.1 ∧ Tm p.2.1 ∧ Fm p.2.2) ∧ b p = j) := by
  have h₁ := REPred.comp (Computable.fst (α := ℕ) (β := ℕ × ℕ)) hv
  have h₂ := REPred.comp (Computable.fst.comp (Computable.snd (α := ℕ) (β := ℕ × ℕ))) ht
  have h₃ := REPred.comp (Computable.snd.comp (Computable.snd (α := ℕ) (β := ℕ × ℕ))) hw
  exact (h₁.and (h₂.and h₃)).and ((Primrec.eq.comp hb (Primrec.const j)).computablePred.to_re)

private theorem carrier_enumerable (C : Carrier) : REPred (fun n : ℕ => C.val.Evalb ![n]) :=
  NumericalCoordinates.predicateSupport_enumerable C

/-- On ambient codes, either branch requires the source predicate as well as its tag. -/
theorem substitutionBranch_enumerable (j : ℕ) :
    REPred (fun p : ℕ × ℕ × ℕ => substitutionSource V σ π d p ∧
      substitutionFreeFor V σ π d p.1 p.2.1 p.2.2 = j) :=
  supportedTag_enumerable (carrier_enumerable V)
    (carrier_enumerable (plainSyntaxCarrier V σ π d false))
    (carrier_enumerable (plainSyntaxCarrier V σ π d true))
    (substitutionFreeFor_primrec V σ π d) j

/-- On the substitution source, the zero branch is the complement of the one branch. -/
theorem substitution_failure_iff (p : ℕ × ℕ × ℕ) (hp : substitutionSource V σ π d p) :
    substitutionFreeFor V σ π d p.1 p.2.1 p.2.2 = 0 ↔
      substitutionFreeFor V σ π d p.1 p.2.1 p.2.2 ≠ 1 := by
  have ht := (Postfix.carrier_plain_model false _ _ p.2.1).mpr hp.2.1
  have hw := (Postfix.carrier_plain_model true _ _ p.2.2).mpr hp.2.2
  rcases substitutionFreeFor_boolean V σ π d p.1 p.2.1 p.2.2 ht hw with h | h <;>
    simp [h]

section Models

open SyntacticLists
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "X" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- An arbitrary public input code is admissible precisely when it lies in the source
and the traversal on its three decoded components succeeds. -/
theorem admissible_iff_source_and_success (n : M) :
    (plainAdmissibleCarrier T V σ π d).val.Evalb ![n] ↔
      ∃ h : (Y ⨯ P : PredicateCategory T).val.Evalb ![n],
        let q : Obj T M (Y ⨯ P) := ⟨n, h⟩
        substitutionFreeFor V σ π d
          ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
          ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
          ((F T M).map prod.fst q).val = 1 := by
  constructor
  · intro ha
    have hf := (plainAdmissibleCarrier_freeFor T V σ π d M n).mp ha
    change (imageCarrier (chosenGraph T (S).admissibleInclusion).graph).val.Evalb ![n] at ha
    rw [imageCarrier_eval] at ha
    obtain ⟨a, h⟩ := ha
    have hs := ((chosenGraph T (S).admissibleInclusion).support_model M a n h).2
    exact ⟨hs, (plainFreeForPredicate_model T V σ π d M ⟨n, hs⟩).mp hf⟩
  · rintro ⟨hs, h⟩
    exact (plainAdmissibleCarrier_freeFor T V σ π d M n).mpr
      ((plainFreeForPredicate_model T V σ π d M ⟨n, hs⟩).mpr h)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
