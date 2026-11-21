/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance
public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport

/-! # Literal parser comparison under coefficient relabeling

The parser's computation graphs ignore coefficient predicates. Membership
of root labels is compared separately, with no witnesses added to a word.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Parser
variable (f : Carrier → Carrier)

theorem shapeGraph_map (p : RawPolynomial) : shapeGraph (p.mapCoefficients f) = shapeGraph p := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,shapeGraph,ip,iq]
  | sum p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,shapeGraph,ip,iq]

theorem childrenWordGraph_map (p : RawPolynomial) :
    childrenWordGraph (p.mapCoefficients f) = childrenWordGraph p := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,childrenWordGraph,ip,iq]
  | sum p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,childrenWordGraph,ip,iq]

theorem refillGraph_map (p : RawPolynomial) : refillGraph (p.mapCoefficients f) = refillGraph p := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,refillGraph,ip,iq]
  | sum p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,refillGraph,ip,iq]

theorem stepGraph_map (a b : RawPolynomial) :
    Postfix.stepGraph (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.stepGraph a b := by
  simp only [Postfix.stepGraph,refillGraph_map,childrenWordGraph_map]

theorem blueprint_map (a b : RawPolynomial) :
    Postfix.blueprint (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.blueprint a b := by
  simp only [Postfix.blueprint,stepGraph_map]

theorem prefixGraph_map (a b : RawPolynomial) :
    Postfix.prefixGraph (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.prefixGraph a b := by
  simp only [Postfix.prefixGraph,blueprint_map]

theorem runGraph_map (a b : RawPolynomial) :
    Postfix.runGraph (a.mapCoefficients f) (b.mapCoefficients f) = Postfix.runGraph a b := by
  simp only [Postfix.runGraph,prefixGraph_map]

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Changing the coefficient morphisms preserves the shape of a polynomial word. -/
theorem shape_map (p : RawPolynomial) (u : M) :
    shape (p.mapCoefficients f) u = shape p u := by
  induction p generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,shape,ip,iq]
  | sum p q ip iq =>
      simp only [SyntaxPolynomial.mapCoefficients,shape,ip,iq]
      split_ifs <;> rfl

theorem childrenWord_map (p : RawPolynomial) (u : M) :
    childrenWord (p.mapCoefficients f) u = childrenWord p u := by
  induction p generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,childrenWord,ip,iq]
  | sum p q ip iq =>
      simp only [SyntaxPolynomial.mapCoefficients,childrenWord,ip,iq]
      split_ifs <;> rfl

theorem constructor_map (p : RawPolynomial) (formula : Bool) (u : M) :
    constructor formula (p.mapCoefficients f) u = constructor formula p u := by
  simp only [constructor,shape_map,childrenWord_map]

/-- Equality of the graph formulas covers nonstandard prefix lengths. -/
theorem runPrefix_map (a b : RawPolynomial) (word n initial : M) :
    Postfix.runPrefix (a.mapCoefficients f) (b.mapCoefficients f) word n initial =
      Postfix.runPrefix a b word n initial := by
  have h := (Postfix.prefixGraph_eval a b (Postfix.runPrefix a b word n initial) n word initial).mpr rfl
  have hm : (Postfix.prefixGraph (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb
      ![Postfix.runPrefix a b word n initial,n,word,initial] := by
    simpa only [prefixGraph_map] using h
  exact ((Postfix.prefixGraph_eval _ _ _ _ _ _).mp hm).symm

theorem run_map (a b : RawPolynomial) (word initial : M) :
    Postfix.run (a.mapCoefficients f) (b.mapCoefficients f) word initial = Postfix.run a b word initial := by
  have h := (Postfix.runGraph_eval a b (Postfix.run a b word initial) word initial).mpr rfl
  have hm : (Postfix.runGraph (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb
      ![Postfix.run a b word initial,word,initial] := by
    simpa only [runGraph_map] using h
  exact ((Postfix.runGraph_eval _ _ _ _ _).mp hm).symm

variable (h : ∀ C : Carrier, ∀ u : M, (f C).val.Evalb ![u] ↔ C.val.Evalb ![u])
include h

theorem rawCarrier_map_iff (X Y : Carrier) (p : RawPolynomial) (u : M) :
    (rawCarrier X Y (p.mapCoefficients f)).val.Evalb ![u] ↔
      (rawCarrier X Y p).val.Evalb ![u] := by
  induction p generalizing u with
  | term => exact Iff.rfl
  | formula => exact Iff.rfl
  | coefficient C => exact h C u
  | unit => exact Iff.rfl
  | product p q ip iq =>
      simp only [SyntaxPolynomial.mapCoefficients,rawCarrier_product_eval,ip,iq]
  | sum p q ip iq =>
      simp only [SyntaxPolynomial.mapCoefficients,rawCarrier_sum_eval,ip,iq]

theorem recordCarrier_map_iff (a b : RawPolynomial) (r : M) :
    (recordCarrier (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb ![r] ↔
      (recordCarrier a b).val.Evalb ![r] := by
  simp [recordCarrier,rawCarrier_map_iff f h]

theorem coefficients_map_iff (a b : RawPolynomial) (word : M) :
    (coefficients (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb ![word] ↔
      (coefficients a b).val.Evalb ![word] := by
  unfold coefficients
  rw [← FiniteSigmaOne.finite_membership_model,← FiniteSigmaOne.finite_membership_model]
  simp only [FiniteSigmaOne.allEntriesCondition_eval,recordCarrier_map_iff f h]

theorem plainCarrier_map_iff (formula : Bool) (a b : RawPolynomial) (word : M) :
    (Postfix.plainCarrier formula (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb ![word] ↔
      (Postfix.plainCarrier formula a b).val.Evalb ![word] := by
  simp only [Postfix.plainCarrier_eval,coefficients_map_iff f h,run_map]

theorem storedCarrier_map_plain (formula : Bool) (a b : RawPolynomial) (word : M) :
    (Postfix.carrier formula a b).val.Evalb ![word] ↔
      (Postfix.plainCarrier formula (a.mapCoefficients f) (b.mapCoefficients f)).val.Evalb ![word] :=
  (Postfix.carrier_plain_model formula a b word).trans (plainCarrier_map_iff f h formula a b word).symm

end Models
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Parser
