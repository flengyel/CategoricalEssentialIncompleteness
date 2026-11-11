/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticModelCoding

/-! Occurrence equations on finite external constructor charts with
arbitrary internal children. All equations use actual PA constructor
closure, and the children may be nonstandard model words. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticModelOccurrences
open ConcreteNamedSubstitution NamedPostfixEncoding NamedArithmeticStandardCodes NamedArithmeticModelCoding
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "Tm" => Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)
local notation "Fm" => Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)
local notation "FV" => ConcreteNamedSubstitution.freeVariables variableCarrier σ π d

 theorem functionInput_member (k : Fin (d+1)) (s : Symbols σ k.val) (c : Fin k.val → M)
    (hc : ∀ i,(Tm).val.Evalb ![c i]) :
    (rawCarrier Tm Fm (termPolynomial σ d)).val.Evalb
      ![⟪NamedArithmeticModelCoding.arityInput d k ⟪(s.val : M),NamedArithmeticModelCoding.childTuple k.val c⟫,1⟫] := by
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inr
  refine ⟨_,rfl,?_⟩
  apply NamedArithmeticModelCoding.arityInput_member
  exact (rawCarrier_product_eval Tm Fm _ _ _).mpr
    ⟨(s.val : M),_,rfl,carrier_natCast _ _ s.property,NamedArithmeticModelCoding.childTuple_member Tm Fm _ _ hc⟩

 theorem function_occurrences (k : Fin (d+1)) (s : Symbols σ k.val) (c : Fin k.val → M)
    (hc : ∀ i,(Tm).val.Evalb ![c i]) :
    FV (constructor false (termPolynomial σ d)
      ⟪NamedArithmeticModelCoding.arityInput d k ⟪(s.val : M),NamedArithmeticModelCoding.childTuple k.val c⟫,1⟫) =
      gatherTuple k.val (fun i => FV (c i)) := by
  erw [freeVariables_term_constructor variableCarrier σ π d _ (functionInput_member σ π d k s c hc)]
  simp [SyntaxPolynomial.termExpression,
    mapChildren,freeVarsTermRoot]

 theorem equalityInput_member (s t : M) (hs : (Tm).val.Evalb ![s]) (ht : (Tm).val.Evalb ![t]) :
    (rawCarrier Tm Fm (formulaPolynomial π d)).val.Evalb ![NamedArithmeticModelCoding.equalInput s t] := by
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  exact (rawCarrier_product_eval Tm Fm _ _ _).mpr ⟨s,t,rfl,hs,ht⟩

 theorem equality_occurrences (s t : M) (hs : (Tm).val.Evalb ![s]) (ht : (Tm).val.Evalb ![t]) :
    FV (constructor true (formulaPolynomial π d) (NamedArithmeticModelCoding.equalInput s t)) =
      Words.append (FV s) (FV t) := by
  erw [freeVariables_formula_constructor variableCarrier σ π d _ (equalityInput_member σ π d s t hs ht)]
  simp [NamedArithmeticModelCoding.equalInput,
    SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,mapChildren,
    freeVarsFormulaRoot,formulaLeft,gather]

 theorem relationInput_member (k : Fin (d+1)) (p : Symbols π k.val) (c : Fin k.val → M)
    (hc : ∀ i,(Tm).val.Evalb ![c i]) :
    (rawCarrier Tm Fm (formulaPolynomial π d)).val.Evalb
      ![NamedArithmeticModelCoding.relationInput d k (p.val : M) c] := by
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inr
  refine ⟨_,rfl,?_⟩
  apply NamedArithmeticModelCoding.arityInput_member
  exact (rawCarrier_product_eval Tm Fm _ _ _).mpr
    ⟨(p.val : M),_,rfl,carrier_natCast _ _ p.property,NamedArithmeticModelCoding.childTuple_member Tm Fm _ _ hc⟩

 theorem relation_occurrences (k : Fin (d+1)) (p : Symbols π k.val) (c : Fin k.val → M)
    (hc : ∀ i,(Tm).val.Evalb ![c i]) :
    FV (constructor true (formulaPolynomial π d) (NamedArithmeticModelCoding.relationInput d k (p.val : M) c)) =
      gatherTuple k.val (fun i => FV (c i)) := by
  erw [freeVariables_formula_constructor variableCarrier σ π d _ (relationInput_member σ π d k p c hc)]
  simp [NamedArithmeticModelCoding.relationInput,
    SyntaxPolynomial.formulaExpression,mapChildren,freeVarsFormulaRoot,formulaLeft,gather]

 theorem negationInput_member (body : M) (hb : (Fm).val.Evalb ![body]) :
    (rawCarrier Tm Fm (formulaPolynomial π d)).val.Evalb ![NamedArithmeticModelCoding.negInput body] := by
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  exact Or.inr ⟨body,rfl,hb⟩

 theorem negation_occurrences (body : M) (hb : (Fm).val.Evalb ![body]) :
    FV (constructor true (formulaPolynomial π d) (NamedArithmeticModelCoding.negInput body)) = FV body := by
  erw [freeVariables_formula_constructor variableCarrier σ π d _ (negationInput_member σ π d body hb)]
  simp [NamedArithmeticModelCoding.negInput,
    SyntaxPolynomial.formulaExpression,mapChildren,freeVarsFormulaRoot,formulaLeft,gather]

 theorem implicationInput_member (s t : M) (hs : (Fm).val.Evalb ![s]) (ht : (Fm).val.Evalb ![t]) :
    (rawCarrier Tm Fm (formulaPolynomial π d)).val.Evalb ![NamedArithmeticModelCoding.impInput s t] := by
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inl
  refine ⟨_,rfl,?_⟩
  apply (rawCarrier_sum_eval Tm Fm _ _ _).mpr
  apply Or.inr
  refine ⟨_,rfl,?_⟩
  exact (rawCarrier_product_eval Tm Fm _ _ _).mpr ⟨s,t,rfl,hs,ht⟩

 theorem implication_occurrences (s t : M) (hs : (Fm).val.Evalb ![s]) (ht : (Fm).val.Evalb ![t]) :
    FV (constructor true (formulaPolynomial π d) (NamedArithmeticModelCoding.impInput s t)) =
      Words.append (FV s) (FV t) := by
  erw [freeVariables_formula_constructor variableCarrier σ π d _ (implicationInput_member σ π d s t hs ht)]
  simp [NamedArithmeticModelCoding.impInput,
    SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,mapChildren,freeVarsFormulaRoot,formulaLeft,gather]

end CategoricalEssentialIncompleteness.V46.NamedArithmeticModelOccurrences
