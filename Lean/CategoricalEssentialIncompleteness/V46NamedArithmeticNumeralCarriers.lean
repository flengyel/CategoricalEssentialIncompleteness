/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumerals
public import CategoricalEssentialIncompleteness.V46NamedArithmeticPrimitiveInvariant
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAcceptance

/-! PA proves that its internal numeral construction is a closed,
accepted arithmetic term, including at nonstandard input indices. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
open NamedArithmeticSignature ConcreteNamedSubstitution

abbrev termCarrier : Carrier := Postfix.carrier false termPolynomial formulaPolynomial
abbrev formulaCarrier : Carrier := Postfix.carrier true termPolynomial formulaPolynomial
abbrev occurrences (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] : M → M :=
  ConcreteNamedSubstitution.freeVariables variableSymbols functionSymbols relationSymbols bound

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem nullaryInput_carrier (X Y : Carrier) (label : M) (hl : label = 0 ∨ label = 1) :
    (rawCarrier X Y termPolynomial).val.Evalb ![⟪⟪⟪⟪label,0⟫,0⟫,0⟫,1⟫] := by
  have hzero : (rawCarrier X Y (.product (.coefficient (functionSymbols 0)) .unit)).val.Evalb ![⟪label,0⟫] :=
    (rawCarrier_product_eval X Y _ _ _).mpr ⟨label,0,rfl,by simpa [rawCarrier] using hl,by simp [rawCarrier]⟩
  have hone : (rawCarrier X Y (SyntaxPolynomial.constructors functionSymbols 1)).val.Evalb ![⟪⟪label,0⟫,0⟫] :=
    (rawCarrier_sum_eval X Y _ _ _).mpr (Or.inl ⟨⟪label,0⟫,rfl,hzero⟩)
  have htwo : (rawCarrier X Y (SyntaxPolynomial.constructors functionSymbols 2)).val.Evalb ![⟪⟪⟪label,0⟫,0⟫,0⟫] :=
    (rawCarrier_sum_eval X Y _ _ _).mpr (Or.inl ⟨⟪⟪label,0⟫,0⟫,rfl,hone⟩)
  exact (rawCarrier_sum_eval X Y _ _ _).mpr (Or.inr ⟨_,rfl,htwo⟩)

theorem zeroInput_carrier (X Y : Carrier) : (rawCarrier X Y termPolynomial).val.Evalb (M := M) ![zeroInput] :=
  nullaryInput_carrier X Y 0 (Or.inl rfl)
theorem oneInput_carrier (X Y : Carrier) : (rawCarrier X Y termPolynomial).val.Evalb (M := M) ![oneInput] :=
  nullaryInput_carrier X Y 1 (Or.inr rfl)

theorem addInput_carrier (X Y : Carrier) (s t : M)
    (hs : X.val.Evalb ![s]) (ht : X.val.Evalb ![t]) :
    (rawCarrier X Y termPolynomial).val.Evalb ![addInput s t] := by
  have hchildren : (rawCarrier X Y (.product .term .term)).val.Evalb ![⟪s,t⟫] :=
    (rawCarrier_product_eval X Y _ _ _).mpr ⟨s,t,rfl,hs,ht⟩
  have hlabel : (rawCarrier X Y (.product (.coefficient (functionSymbols 2))
      (SyntaxPolynomial.power .term 2))).val.Evalb ![⟪0,⟪s,t⟫⟫] :=
    (rawCarrier_product_eval X Y _ _ _).mpr ⟨0,⟪s,t⟫,rfl,by simp [rawCarrier],hchildren⟩
  have htwo : (rawCarrier X Y (SyntaxPolynomial.constructors functionSymbols 2)).val.Evalb ![⟪⟪0,⟪s,t⟫⟫,1⟫] :=
    (rawCarrier_sum_eval X Y _ _ _).mpr (Or.inr ⟨_,rfl,hlabel⟩)
  exact (rawCarrier_sum_eval X Y _ _ _).mpr (Or.inr ⟨_,rfl,htwo⟩)

theorem zeroWord_carrier : termCarrier.val.Evalb (M := M) ![zeroWord] :=
  Postfix.term_constructor_carrier termPolynomial formulaPolynomial _ (zeroInput_carrier _ _)
theorem oneWord_carrier : termCarrier.val.Evalb (M := M) ![oneWord] :=
  Postfix.term_constructor_carrier termPolynomial formulaPolynomial _ (oneInput_carrier _ _)
theorem addWord_carrier (s t : M) (hs : termCarrier.val.Evalb ![s]) (ht : termCarrier.val.Evalb ![t]) :
    termCarrier.val.Evalb ![addWord s t] :=
  Postfix.term_constructor_carrier termPolynomial formulaPolynomial _ (addInput_carrier _ _ s t hs ht)

theorem zeroWord_occurrences : occurrences M (zeroWord : M) = 0 := by
  dsimp only [occurrences,zeroWord,termPolynomial,NamedPostfixEncoding.termPolynomial]
  rw [freeVariables_term_constructor variableSymbols functionSymbols relationSymbols bound _
    (zeroInput_carrier termCarrier formulaCarrier)]
  simp [zeroInput,
    SyntaxPolynomial.termExpression,SyntaxPolynomial.constructors,SyntaxPolynomial.power,
    freeVarsTermRoot,mapChildren,gather]

theorem oneWord_occurrences : occurrences M (oneWord : M) = 0 := by
  dsimp only [occurrences,oneWord,termPolynomial,NamedPostfixEncoding.termPolynomial]
  rw [freeVariables_term_constructor variableSymbols functionSymbols relationSymbols bound _
    (oneInput_carrier termCarrier formulaCarrier)]
  simp [oneInput,
    SyntaxPolynomial.termExpression,SyntaxPolynomial.constructors,SyntaxPolynomial.power,
    freeVarsTermRoot,mapChildren,gather]

theorem addWord_occurrences (s t : M) (hs : termCarrier.val.Evalb ![s]) (ht : termCarrier.val.Evalb ![t]) :
    occurrences M (addWord s t) = Words.append (occurrences M s) (occurrences M t) := by
  dsimp only [occurrences,addWord,termPolynomial,NamedPostfixEncoding.termPolynomial]
  rw [freeVariables_term_constructor variableSymbols functionSymbols relationSymbols bound _
    (addInput_carrier termCarrier formulaCarrier s t hs ht)]
  simp [addInput,
    SyntaxPolynomial.termExpression,SyntaxPolynomial.constructors,SyntaxPolynomial.power,
    freeVarsTermRoot,mapChildren,gather]

end Models

/-- The carrier retains only the numeral word, with its computation
and closure witnesses hidden by existential quantification. -/
def closedTermCarrier : Carrier :=
  NamedArithmeticPrimitiveRecursion.zeroFiberCarrier termCarrier
    (freeVariablesGraph variableSymbols functionSymbols relationSymbols bound)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
@[simp] theorem closedTermCarrier_eval (word : M) :
    closedTermCarrier.val.Evalb ![word] ↔ termCarrier.val.Evalb ![word] ∧ occurrences M word = 0 :=
  (NamedArithmeticPrimitiveRecursion.zeroFiberCarrier_eval _ _ word).trans
    (and_congr Iff.rfl ((freeVariablesGraph_eval variableSymbols functionSymbols relationSymbols bound 0 word).trans eq_comm))

/-- This uses arithmetic induction inside the arbitrary PA model. -/
theorem numeralCode_closed (n : M) : closedTermCarrier.val.Evalb ![numeralCode n] := by
  apply NamedArithmeticPrimitiveRecursion.scalarResult_carrier construction closedTermCarrier
  · change closedTermCarrier.val.Evalb ![zeroWord]
    exact (closedTermCarrier_eval _).mpr ⟨zeroWord_carrier,zeroWord_occurrences⟩
  · intro k previous hp
    change closedTermCarrier.val.Evalb ![addWord previous oneWord]
    obtain ⟨hc,hf⟩ := (closedTermCarrier_eval previous).mp hp
    apply (closedTermCarrier_eval _).mpr
    refine ⟨addWord_carrier _ _ hc oneWord_carrier,?_⟩
    rw [addWord_occurrences _ _ hc oneWord_carrier,hf,oneWord_occurrences,Words.append_nil]

 theorem numeralCode_carrier_closed (n : M) :
    termCarrier.val.Evalb ![numeralCode n] ∧ occurrences M (numeralCode n) = 0 :=
  (closedTermCarrier_eval _).mp (numeralCode_closed n)
end Models

end CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
