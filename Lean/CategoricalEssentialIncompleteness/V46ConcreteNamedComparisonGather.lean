/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRepresentation
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonLists
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionGather
public import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables

/-! # Ordered categorical collection agrees with the numerical root chart -/

@[expose] public section

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

/-- This is a finite polynomial expression in the already constructed
concatenation and nil operations, not a new syntax evaluator. -/
def gatherArrow : (q : SyntaxPolynomial (PredicateCategory T)) →
    q.eval.obj (listObject T V,listObject T V) ⟶ listObject T V
  | .term => 𝟙 _
  | .formula => 𝟙 _
  | .coefficient _ => terminal.from _ ≫ (lists T V).algebra.nil
  | .unit => terminal.from _ ≫ (lists T V).algebra.nil
  | .product a b => prod.map (gatherArrow a) (gatherArrow b) ≫ (lists T V).append
  | .sum a b => coprod.desc (gatherArrow a) (gatherArrow b)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedGatherComparisonModelDecidableEq : DecidableEq M := Classical.decEq M

theorem gatherArrow_value (q : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (q.eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V) q).val.Evalb ![u,z.val]) :
    ((F T M).map (gatherArrow T V q) z).val = ConcreteNamedSubstitution.gather q u := by
  induction q generalizing u with
  | term =>
      have he := (baseRepresentation_term_eval T M (listObject T V) (listObject T V) u z.val).mp hz
      change ((F T M).map (𝟙 (listObject T V)) z).val = u
      erw [Functor.map_id_apply]
      exact he.2
  | formula =>
      have he := (baseRepresentation_formula_eval T M (listObject T V) (listObject T V) u z.val).mp hz
      change ((F T M).map (𝟙 (listObject T V)) z).val = u
      erw [Functor.map_id_apply]
      exact he.2
  | coefficient C =>
      change ((F T M).map (terminal.from C ≫ (lists T V).algebra.nil) z).val = 0
      rw [Functor.map_comp_apply]
      exact nil_value T M _ V ((F T M).map (terminal.from C) z)
  | unit =>
      change ((F T M).map (terminal.from _ ≫ (lists T V).algebra.nil) z).val = 0
      rw [Functor.map_comp_apply]
      exact nil_value T M _ V ((F T M).map (terminal.from _) z)
  | product a b ia ib =>
      obtain ⟨x,y,rfl,hx,hy⟩ := representation_product_points T M
        (listObject T V) (listObject T V) a b u z hz
      change ((F T M).map (prod.map (gatherArrow T V a) (gatherArrow T V b) ≫
        (lists T V).append) z).val = _
      rw [Functor.map_comp_apply]
      erw [append_value T V M,model_map_fst T M,model_map_snd T M,ia _ _ hx,ib _ _ hy]
      simp only [ConcreteNamedSubstitution.gather,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]
  | sum a b ia ib =>
      exact representation_coprod_desc T M (listObject T V) (listObject T V)
        (gatherArrow T V a) (gatherArrow T V b)
        (ConcreteNamedSubstitution.gather a) (ConcreteNamedSubstitution.gather b) ia ib u z hz

/-- The specified finite tuple operation has the same ordered chart,
including the nullary tuple's unit padding. -/
theorem tupleAppend_value (n : ℕ) (u : M)
    (z : Obj T M ((SyntaxPolynomial.power .term n).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.power .term n)).val.Evalb ![u,z.val]) :
    ((F T M).map ((lists T V).tupleAppend n) z).val =
      ConcreteNamedSubstitution.gather (SyntaxPolynomial.power .term n) u := by
  induction n using Nat.twoStepInduction generalizing u with
  | zero =>
      change ((F T M).map (lists T V).algebra.nil z).val = 0
      exact nil_value T M _ V z
  | one =>
      have he := (baseRepresentation_term_eval T M (listObject T V) (listObject T V) u z.val).mp hz
      change ((F T M).map (𝟙 (listObject T V)) z).val = u
      erw [Functor.map_id_apply]
      exact he.2
  | more n _ ih =>
      obtain ⟨x,y,rfl,hx,hy⟩ := representation_product_points T M
        (listObject T V) (listObject T V) (SyntaxPolynomial.power .term (n+1)) .term u z hz
      have he := (baseRepresentation_term_eval T M (listObject T V) (listObject T V)
        y ((F T M).map (prod.snd : _ ⨯ listObject T V ⟶ _) z).val).mp hy
      change ((F T M).map (prod.map ((lists T V).tupleAppend (n+1)) (𝟙 _) ≫
        (lists T V).append) z).val = _
      rw [Functor.map_comp_apply]
      erw [append_value T V M,model_map_fst T M,model_map_snd T M]
      erw [Functor.map_id_apply]
      erw [ih _ _ hx,he.2]
      simp only [SyntaxPolynomial.power,ConcreteNamedSubstitution.gather,Arithmetic.pi₁_pair,Arithmetic.pi₂_pair]

theorem coefficientTuple_value (C : PredicateCategory T) (n : ℕ) (u : M)
    (z : Obj T M ((SyntaxPolynomial.product (.coefficient C) (SyntaxPolynomial.power .term n)).eval.obj
      (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (.product (.coefficient C) (SyntaxPolynomial.power .term n))).val.Evalb ![u,z.val]) :
    ((F T M).map (prod.snd ≫ (lists T V).tupleAppend n) z).val =
      ConcreteNamedSubstitution.gather (.product (.coefficient C) (SyntaxPolynomial.power .term n)) u := by
  obtain ⟨x,y,rfl,_,hy⟩ := representation_product_points T M
    (listObject T V) (listObject T V) (.coefficient C) (SyntaxPolynomial.power .term n) u z hz
  rw [Functor.map_comp_apply]
  erw [tupleAppend_value T V M n y _ hy]
  simp [ConcreteNamedSubstitution.gather]

/-- Labels are preserved as coefficients and contribute no variable
occurrences; the ordered argument tuple contributes exactly its lists. -/
theorem constructorOccurrences_value (σ : ℕ → PredicateCategory T) (n : ℕ) (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors σ n).eval.obj (listObject T V,listObject T V)))
    (hz : (baseRepresentation T (listObject T V) (listObject T V)
      (SyntaxPolynomial.constructors σ n)).val.Evalb ![u,z.val]) :
    ((F T M).map ((lists T V).constructorOccurrences σ n) z).val =
      ConcreteNamedSubstitution.gather (SyntaxPolynomial.constructors σ n) u := by
  induction n generalizing u with
  | zero => exact coefficientTuple_value T V M (σ 0) 0 u z hz
  | succ n ih =>
      exact representation_coprod_desc T M (listObject T V) (listObject T V)
        ((lists T V).constructorOccurrences σ n) (prod.snd ≫ (lists T V).tupleAppend (n+1))
        (ConcreteNamedSubstitution.gather (SyntaxPolynomial.constructors σ n))
        (ConcreteNamedSubstitution.gather (.product (.coefficient (σ (n+1)))
          (SyntaxPolynomial.power .term (n+1)))) ih
        (coefficientTuple_value T V M (σ (n+1)) (n+1)) u z hz

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
