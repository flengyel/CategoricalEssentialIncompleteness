/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConservation
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # The plain singleton parser and the same literal-word object -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
open Coding

/-- The displayed parser criterion: all labels are valid and one tree
of the requested sort remains. There is no stored-word equality test. -/
def plainCarrier (formula : Bool) (a b : RawPolynomial) : Carrier :=
  let R := runGraph a b
  let C := coefficients a b
  match formula with
  | false => .mkSigma “word. !C.val word ∧ ∃ o stored block stack,
      !R.val o word 1 ∧ !pairDef.val block stored 0 ∧
      !adjoinDef.val stack block 0 ∧ o = stack + 1”
  | true => .mkSigma “word. !C.val word ∧ ∃ o stored block stack,
      !R.val o word 1 ∧ !pairDef.val block stored 1 ∧
      !adjoinDef.val stack block 0 ∧ o = stack + 1”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem plainCarrier_eval (formula : Bool) (a b : RawPolynomial) (word : M) :
    (plainCarrier formula a b).val.Evalb ![word] ↔
      (coefficients a b).val.Evalb ![word] ∧ ∃ stored : M,
        run a b word 1 = adjoin ⟪stored, if formula then 1 else 0⟫ 0 + 1 := by
  cases formula <;> simp [plainCarrier]

/-- The comparison fixes every literal word, also at nonstandard model
lengths, and retains precisely the original coefficient predicate. -/
theorem carrier_plain_model (formula : Bool) (a b : RawPolynomial) (word : M) :
    (carrier formula a b).val.Evalb ![word] ↔
      (plainCarrier formula a b).val.Evalb ![word] := by
  rw [plainCarrier_eval]
  exact carrier_iff_singleton formula a b word

theorem rawCarrier_plain_model (a b q : RawPolynomial) (u : M) :
    (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u] ↔
      (rawCarrier (plainCarrier false a b) (plainCarrier true a b) q).val.Evalb ![u] := by
  induction q generalizing u with
  | term => exact carrier_plain_model false a b u
  | formula => exact carrier_plain_model true a b u
  | coefficient C => exact Iff.rfl
  | unit => exact Iff.rfl
  | product c d ic id =>
      rw [rawCarrier_product_eval, rawCarrier_product_eval]
      constructor
      · rintro ⟨x, y, rfl, hx, hy⟩
        exact ⟨x, y, rfl, (ic x).mp hx, (id y).mp hy⟩
      · rintro ⟨x, y, rfl, hx, hy⟩
        exact ⟨x, y, rfl, (ic x).mpr hx, (id y).mpr hy⟩
  | sum c d ic id =>
      rw [rawCarrier_sum_eval, rawCarrier_sum_eval]
      constructor
      · rintro (⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩)
        · exact Or.inl ⟨x, rfl, (ic x).mp hx⟩
        · exact Or.inr ⟨y, rfl, (id y).mp hy⟩
      · rintro (⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩)
        · exact Or.inl ⟨x, rfl, (ic x).mpr hx⟩
        · exact Or.inr ⟨y, rfl, (id y).mpr hy⟩

/-- Both presentations use the very same numeric postfix constructor,
with the same ordered raw children and the same coefficient labels. -/
theorem plain_constructor_comparison (formula : Bool) (a b : RawPolynomial) (u : M)
    (hu : (rawCarrier (plainCarrier false a b) (plainCarrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    (carrier formula a b).val.Evalb ![constructor formula (if formula then b else a) u] ∧
      (plainCarrier formula a b).val.Evalb ![constructor formula (if formula then b else a) u] := by
  have hs := (rawCarrier_plain_model a b (if formula then b else a) u).mpr hu
  have hc : (carrier formula a b).val.Evalb ![constructor formula (if formula then b else a) u] := by
    cases formula
    · exact term_constructor_carrier a b u hs
    · exact formula_constructor_carrier a b u hs
  exact ⟨hc, (carrier_plain_model formula a b _).mp hc⟩
end Models

def plainCarrierEquivalenceSentence (formula : Bool) (a b : RawPolynomial) : ArithmeticSentence :=
  let C := carrier formula a b
  let D := plainCarrier formula a b
  “∀ word, !C.val word ↔ !D.val word”

theorem carrier_plain_theory (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (formula : Bool) (a b : RawPolynomial) :
    T ⊢ plainCarrierEquivalenceSentence formula a b := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simpa [models_iff, plainCarrierEquivalenceSentence] using
    (fun word : M => carrier_plain_model formula a b word)

theorem carrier_plain_pa (formula : Bool) (a b : RawPolynomial) :
    𝗣𝗔 ⊢ plainCarrierEquivalenceSentence formula a b :=
  carrier_plain_theory 𝗣𝗔 formula a b

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The graph is literal numeric identity; only its source and target
predicates are compared by the proved PA parser invariant. -/
def toPlainMorphism (formula : Bool) (a b : RawPolynomial) :
    GraphMorphism T (carrier formula a b) (plainCarrier formula a b) where
  graph := GraphMorphism.identityGraph (carrier formula a b)
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro x y h
    obtain ⟨hx, hy⟩ := (GraphMorphism.identityGraph_eval _ x y).mp h
    subst y
    exact ⟨hx, (carrier_plain_model formula a b x).mp hx⟩
  total := (GraphMorphism.identity T (carrier formula a b)).total

def fromPlainMorphism (formula : Bool) (a b : RawPolynomial) :
    GraphMorphism T (plainCarrier formula a b) (carrier formula a b) where
  graph := GraphMorphism.identityGraph (plainCarrier formula a b)
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro x y h
    obtain ⟨hx, hy⟩ := (GraphMorphism.identityGraph_eval _ x y).mp h
    subst y
    exact ⟨hx, (carrier_plain_model formula a b x).mpr hx⟩
  total := (GraphMorphism.identity T (plainCarrier formula a b)).total

theorem toPlain_constructor_graph {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (formula : Bool) (a b : RawPolynomial) (u : M)
    (hu : (rawCarrier (plainCarrier false a b) (plainCarrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    (toPlainMorphism T formula a b).graph.val.Evalb
      ![constructor formula (if formula then b else a) u, constructor formula (if formula then b else a) u] :=
  (GraphMorphism.identityGraph_eval _ _ _).mpr ⟨(plain_constructor_comparison formula a b u hu).1, rfl⟩

/-- Actual inverse quotient arrows, fixing the same word on both sides. -/
def plainCarrierIso (formula : Bool) (a b : RawPolynomial) :
    @CategoryTheory.Iso (PredicateCategory T) inferInstance
      (carrier formula a b) (plainCarrier formula a b) where
  hom := classOfGraph T (toPlainMorphism T formula a b)
  inv := classOfGraph T (fromPlainMorphism T formula a b)
  hom_inv_id := by
    apply Quotient.sound
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    rw [models_iff, uniformSentence_eval]
    intro x z
    change (comp (GraphMorphism.identityGraph (plainCarrier formula a b))
      (GraphMorphism.identityGraph (carrier formula a b))).val.Evalb ![x, z] ↔
        (GraphMorphism.identityGraph (carrier formula a b)).val.Evalb ![x, z]
    rw [comp_eval]
    simp only [GraphMorphism.identityGraph_eval, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨y, ⟨hx, hy⟩, ⟨_, hz⟩⟩
      subst y
      subst z
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, hz⟩
      subst z
      exact ⟨x, ⟨hx, rfl⟩, ⟨(carrier_plain_model formula a b x).mp hx, rfl⟩⟩
  inv_hom_id := by
    apply Quotient.sound
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
    rw [models_iff, uniformSentence_eval]
    intro x z
    change (comp (GraphMorphism.identityGraph (carrier formula a b))
      (GraphMorphism.identityGraph (plainCarrier formula a b))).val.Evalb ![x, z] ↔
        (GraphMorphism.identityGraph (plainCarrier formula a b)).val.Evalb ![x, z]
    rw [comp_eval]
    simp only [GraphMorphism.identityGraph_eval, Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor
    · rintro ⟨y, ⟨hx, hy⟩, ⟨_, hz⟩⟩
      subst y
      subst z
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, hz⟩
      subst z
      exact ⟨x, ⟨hx, rfl⟩, ⟨(carrier_plain_model formula a b x).mpr hx, rfl⟩⟩

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
