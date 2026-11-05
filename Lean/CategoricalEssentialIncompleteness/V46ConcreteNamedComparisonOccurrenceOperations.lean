/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonGather
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonDeletion
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariablesRoots
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInitial

/-! # The actual occurrence-algebra operations have the numerical PA root values -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V : PredicateCategory T)
/-- Retain the ambient theory in the finite polynomial's type before
forming its actual categorical evaluation. The underlying AST is the
literal arithmetic formulaLeft template. -/
def formulaLeftPolynomial (π : ℕ → PredicateCategory T) (d : ℕ) :
    SyntaxPolynomial (PredicateCategory T) := ConcreteNamedSubstitution.formulaLeft π d

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedOccurrenceOperationsModelDecidableEq : DecidableEq M := Classical.decEq M

theorem singleton_value (x : Obj T M V) :
    ((F T M).map (lists T V).singleton x).val = adjoin x.val 0 := by
  change ((F T M).map (prod.lift (𝟙 V)
    (terminal.from V ≫ (lists T V).algebra.nil) ≫ (lists T V).algebra.cons) x).val = _
  rw [Functor.map_comp_apply]
  erw [cons_value T M V]
  erw [model_lift_fst T M,model_lift_snd T M]
  erw [Functor.map_id_apply,Functor.map_comp_apply]
  erw [nil_value T M _ V]

theorem append_term_pair_value (u : M)
    (z : Obj T M ((SyntaxPolynomial.power .term 2).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.power .term 2)).val.Evalb ![u,z.val]) :
    ((F T M).map (lists T V).append z).val =
      ConcreteNamedSubstitution.gather (SyntaxPolynomial.power .term 2) u := by
  obtain ⟨x,y,rfl,hx,hy⟩ := representation_product_points T M
    (listObject T V) (listObject T V) .term .term u z hz
  have he := (baseRepresentation_term_eval T M (listObject T V) (listObject T V)
    x ((F T M).map (prod.fst : listObject T V ⨯ listObject T V ⟶ _) z).val).mp hx
  have he' := (baseRepresentation_term_eval T M (listObject T V) (listObject T V)
    y ((F T M).map (prod.snd : listObject T V ⨯ listObject T V ⟶ _) z).val).mp hy
  erw [append_value T V M,he.2,he'.2]
  simp [SyntaxPolynomial.power,ConcreteNamedSubstitution.gather]

theorem append_formula_pair_value (u : M)
    (z : Obj T M ((SyntaxPolynomial.power .formula 2).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.power .formula 2)).val.Evalb ![u,z.val]) :
    ((F T M).map (lists T V).append z).val =
      ConcreteNamedSubstitution.gather (SyntaxPolynomial.power .formula 2) u := by
  obtain ⟨x,y,rfl,hx,hy⟩ := representation_product_points T M
    (listObject T V) (listObject T V) .formula .formula u z hz
  have he := (baseRepresentation_formula_eval T M (listObject T V) (listObject T V)
    x ((F T M).map (prod.fst : listObject T V ⨯ listObject T V ⟶ _) z).val).mp hx
  have he' := (baseRepresentation_formula_eval T M (listObject T V) (listObject T V)
    y ((F T M).map (prod.snd : listObject T V ⨯ listObject T V ⟶ _) z).val).mp hy
  erw [append_value T V M,he.2,he'.2]
  simp [SyntaxPolynomial.power,ConcreteNamedSubstitution.gather]

theorem occurrenceTerm_operation_value (σ : ℕ → PredicateCategory T) (d : ℕ) (u : M)
    (z : Obj T M ((SyntaxPolynomial.termExpression V σ d).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u,z.val]) :
    ((F T M).map (coprod.desc (lists T V).singleton
      ((lists T V).constructorOccurrences σ d)) z).val =
        ConcreteNamedSubstitution.freeVarsTermRoot σ d 0 u := by
  apply representation_coprod_desc T M (listObject T V) (listObject T V)
    (lists T V).singleton ((lists T V).constructorOccurrences σ d)
    (fun x => adjoin x 0) (ConcreteNamedSubstitution.gather (SyntaxPolynomial.constructors σ d))
    ?_ (constructorOccurrences_value T V M σ d) u z hz
  intro x q hq
  have he := (baseRepresentation_coefficient_eval T M (listObject T V) (listObject T V)
    V x q.val).mp hq
  exact (singleton_value T V M q).trans (congrArg (fun a => adjoin a 0) he.2)

/-- The four nonquantified alternatives use ordered concatenation, the
labelled constructor collection, and the identity for negation. -/
theorem occurrenceFormula_left_value (π : ℕ → PredicateCategory T) (d : ℕ) (u : M)
    (z : Obj T M ((formulaLeftPolynomial T π d).eval.obj
      (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (ConcreteNamedSubstitution.formulaLeft π d)).val.Evalb ![u,z.val]) :
    ((F T M).map (coprod.desc
      (coprod.desc (coprod.desc (lists T V).append ((lists T V).constructorOccurrences π d))
        (𝟙 (listObject T V))) (lists T V).append) z).val =
      ConcreteNamedSubstitution.gather (ConcreteNamedSubstitution.formulaLeft π d) u := by
  apply representation_coprod_desc T M (listObject T V) (listObject T V)
    (coprod.desc (coprod.desc (lists T V).append ((lists T V).constructorOccurrences π d))
      (𝟙 (listObject T V))) (lists T V).append
    (ConcreteNamedSubstitution.gather (.sum (.sum (SyntaxPolynomial.power .term 2)
      (SyntaxPolynomial.constructors π d)) .formula))
    (ConcreteNamedSubstitution.gather (SyntaxPolynomial.power .formula 2))
    ?_ (append_formula_pair_value T V M) u z hz
  intro x q hq
  apply representation_coprod_desc T M (listObject T V) (listObject T V)
    (coprod.desc (lists T V).append ((lists T V).constructorOccurrences π d))
    (𝟙 (listObject T V))
    (ConcreteNamedSubstitution.gather (.sum (SyntaxPolynomial.power .term 2)
      (SyntaxPolynomial.constructors π d))) id ?_ ?_ x q hq
  · intro y r hr
    exact representation_coprod_desc T M (listObject T V) (listObject T V)
      (lists T V).append ((lists T V).constructorOccurrences π d)
      (ConcreteNamedSubstitution.gather (SyntaxPolynomial.power .term 2))
      (ConcreteNamedSubstitution.gather (SyntaxPolynomial.constructors π d))
      (append_term_pair_value T V M) (constructorOccurrences_value T V M π d) y r hr
  · intro y r hr
    have he := (baseRepresentation_formula_eval T M (listObject T V) (listObject T V) y r.val).mp hr
    erw [Functor.map_id_apply]
    exact he.2

theorem occurrenceFormula_operation_value (π : ℕ → PredicateCategory T) (d : ℕ) (u : M)
    (z : Obj T M ((SyntaxPolynomial.formulaExpression V π d).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u,z.val]) :
    ((F T M).map (coprod.desc
      (coprod.desc
        (coprod.desc (coprod.desc (lists T V).append ((lists T V).constructorOccurrences π d))
          (𝟙 (listObject T V))) (lists T V).append)
      ((lists T V).deletion (SyntacticDecidableVariables.decidableVariables T V))) z).val =
        ConcreteNamedSubstitution.freeVarsFormulaRoot π d 0 u := by
  apply representation_coprod_desc T M (listObject T V) (listObject T V)
    (coprod.desc
      (coprod.desc (coprod.desc (lists T V).append ((lists T V).constructorOccurrences π d))
        (𝟙 (listObject T V))) (lists T V).append)
    ((lists T V).deletion (SyntacticDecidableVariables.decidableVariables T V))
    (ConcreteNamedSubstitution.gather (ConcreteNamedSubstitution.formulaLeft π d))
    (fun v => ConcreteNamedSubstitution.delete (π₁ v) (π₂ v))
    (occurrenceFormula_left_value T V M π d) ?_ u z hz
  intro v q hq
  obtain ⟨x,y,rfl,hx,hy⟩ := representation_product_points T M
    (listObject T V) (listObject T V) (.coefficient V) .formula v q hq
  have he := (baseRepresentation_coefficient_eval T M (listObject T V) (listObject T V)
    V x ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ _) q).val).mp hx
  have he' := (baseRepresentation_formula_eval T M (listObject T V) (listObject T V)
    y ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ _) q).val).mp hy
  rw [← deletionArrow_eq]
  erw [deletionArrow_value T V M,he.2,he'.2]
  simp

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
