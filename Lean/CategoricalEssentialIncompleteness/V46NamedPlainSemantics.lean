/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels
public import CategoricalEssentialIncompleteness.V46NamedFiniteSoundness
public import CategoricalEssentialIncompleteness.V46LogicalSchemes
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels
public import CategoricalEssentialIncompleteness.V46ModelLogicalSoundness

/-! # Standard semantics of the plain categorical constructors -/

@[expose] public section

universe w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding NamedPostfixPlainComparison
open NamedPlainOperationsModels ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "G" => F 𝗣𝗔 ℕ

def decodeTerm (t : Obj 𝗣𝗔 ℕ X) : NamedFiniteSyntax.Term (Symbols σ) d :=
  (plainTermModelEquiv σ π d).symm t
def decodeFormula (φ : Obj 𝗣𝗔 ℕ Y) : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d :=
  (plainFormulaModelEquiv σ π d).symm φ

@[simp] theorem decodeTerm_code (t : Obj 𝗣𝗔 ℕ X) :
    termCode (decodeTerm σ π d t) = t.val := by
  calc
    _ = (plainTermModelEquiv σ π d (decodeTerm σ π d t)).val :=
      (plainTermModelEquiv_val _).symm
    _ = _ := congrArg Subtype.val ((plainTermModelEquiv σ π d).apply_symm_apply t)

@[simp] theorem decodeFormula_code (φ : Obj 𝗣𝗔 ℕ Y) :
    formulaCode (decodeFormula σ π d φ) = φ.val := by
  calc
    _ = (plainFormulaModelEquiv σ π d (decodeFormula σ π d φ)).val :=
      (plainFormulaModelEquiv_val _).symm
    _ = _ := congrArg Subtype.val ((plainFormulaModelEquiv σ π d).apply_symm_apply φ)

private theorem decodeTerm_of_val (t : Obj 𝗣𝗔 ℕ X)
    (r : NamedFiniteSyntax.Term (Symbols σ) d) (h : t.val = termCode r) :
    decodeTerm σ π d t = r := by
  apply NamedPostfixEncoding.termCode_injective
  exact (decodeTerm_code σ π d t).trans h

private theorem decodeFormula_of_val (φ : Obj 𝗣𝗔 ℕ Y)
    (ψ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) (h : φ.val = formulaCode ψ) :
    decodeFormula σ π d φ = ψ := by
  apply NamedPostfixEncoding.formulaCode_injective
  exact (decodeFormula_code σ π d φ).trans h

@[simp] theorem decode_variable (x : Obj 𝗣𝗔 ℕ variableCarrier) :
    decodeTerm σ π d ((G).map (S).variableConstructor x) = .var x.val := by
  apply decodeTerm_of_val
  exact variable_value 𝗣𝗔 ℕ variableCarrier σ π d x

@[simp] theorem decode_equality (z : Obj 𝗣𝗔 ℕ (X ⨯ X)) :
    decodeFormula σ π d ((G).map (S).equalityConstructor z) =
      .equal (decodeTerm σ π d ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := X)) z))
        (decodeTerm σ π d ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := X)) z)) := by
  apply decodeFormula_of_val
  simp only [formulaPolynomial,formulaCode,equalInput,decodeTerm_code]
  erw [equality_value 𝗣𝗔 ℕ variableCarrier σ π d z]
  rfl

@[simp] theorem decode_negation (φ : Obj 𝗣𝗔 ℕ Y) :
    decodeFormula σ π d ((G).map (S).negationConstructor φ) =
      .neg (decodeFormula σ π d φ) := by
  apply decodeFormula_of_val
  simpa only [formulaPolynomial,formulaCode,negInput,decodeFormula_code] using
    negation_value 𝗣𝗔 ℕ variableCarrier σ π d φ

@[simp] theorem decode_implication (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y)) :
    decodeFormula σ π d ((G).map (S).implicationConstructor z) =
      .imp (decodeFormula σ π d ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z))
        (decodeFormula σ π d ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z)) := by
  apply decodeFormula_of_val
  simp only [formulaPolynomial,formulaCode,impInput,decodeFormula_code]
  erw [implication_value 𝗣𝗔 ℕ variableCarrier σ π d z]
  rfl

@[simp] theorem decode_quantifier (z : Obj 𝗣𝗔 ℕ (variableCarrier ⨯ Y)) :
    decodeFormula σ π d ((G).map (S).quantifierConstructor z) =
      .all ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := variableCarrier) («Y» := Y)) z).val
        (decodeFormula σ π d ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableCarrier) («Y» := Y)) z)) := by
  apply decodeFormula_of_val
  simp only [formulaPolynomial,formulaCode,allInput,decodeFormula_code]
  erw [quantifier_value 𝗣𝗔 ℕ variableCarrier σ π d z]
  rfl

variable {K : Type w} (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

def evaluate (t : Obj 𝗣𝗔 ℕ X) (ρ : ℕ → K) : K :=
  (decodeTerm σ π d t).evaluate functions ρ
def Holds (φ : Obj 𝗣𝗔 ℕ Y) (ρ : ℕ → K) : Prop :=
  (decodeFormula σ π d φ).Holds functions relations ρ
def Valid (φ : Obj 𝗣𝗔 ℕ Y) : Prop := ∀ ρ : ℕ → K, Holds σ π d functions relations φ ρ

@[simp] theorem holds_equality (z : Obj 𝗣𝗔 ℕ (X ⨯ X)) (ρ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).equalityConstructor z) ρ ↔
      evaluate σ π d functions ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := X)) z) ρ =
        evaluate σ π d functions ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := X) («Y» := X)) z) ρ := by
  simp only [Holds,decode_equality,NamedFiniteSyntax.Formula.Holds,evaluate]

@[simp] theorem holds_negation (φ : Obj 𝗣𝗔 ℕ Y) (ρ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).negationConstructor φ) ρ ↔
      ¬ Holds σ π d functions relations φ ρ := by
  simp only [Holds,decode_negation,NamedFiniteSyntax.Formula.Holds]

@[simp] theorem holds_implication (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y)) (ρ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).implicationConstructor z) ρ ↔
      (Holds σ π d functions relations ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z) ρ →
        Holds σ π d functions relations ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z) ρ) := by
  simp only [Holds,decode_implication,NamedFiniteSyntax.Formula.Holds]

@[simp] theorem holds_quantifier (z : Obj 𝗣𝗔 ℕ (variableCarrier ⨯ Y)) (ρ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).quantifierConstructor z) ρ ↔
      ∀ a : K, Holds σ π d functions relations ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableCarrier) («Y» := Y)) z)
        (Function.update ρ ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := variableCarrier) («Y» := Y)) z).val a) := by
  simp only [Holds,decode_quantifier,NamedFiniteSyntax.Formula.Holds]

theorem valid_hilbertOne (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y)) :
    Valid σ π d functions relations ((G).map (S).hilbertOne z) := by
  intro ρ
  exact ModelLogicalSoundness.valid_one (G) (S).implicationConstructor
    (fun φ => Holds σ π d functions relations φ ρ)
    (fun q => holds_implication σ π d functions relations q ρ) z

theorem valid_hilbertTwo (z : Obj 𝗣𝗔 ℕ ((Y ⨯ Y) ⨯ Y)) :
    Valid σ π d functions relations ((G).map (S).hilbertTwo z) := by
  intro ρ
  exact ModelLogicalSoundness.valid_two (G) (S).implicationConstructor
    (fun φ => Holds σ π d functions relations φ ρ)
    (fun q => holds_implication σ π d functions relations q ρ) z

theorem valid_hilbertThree (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y)) :
    Valid σ π d functions relations ((G).map (S).hilbertThree z) := by
  intro ρ
  exact ModelLogicalSoundness.valid_three (G) (S).implicationConstructor
    (fun φ => Holds σ π d functions relations φ ρ)
    (fun q => holds_implication σ π d functions relations q ρ)
    (S).negationConstructor (fun φ => holds_negation σ π d functions relations φ ρ) z

theorem valid_hilbertReflexivity (t : Obj 𝗣𝗔 ℕ X) :
    Valid σ π d functions relations ((G).map (S).hilbertReflexivity t) := by
  intro ρ
  simp only [CategoricalSyntax.hilbertReflexivity,Functor.map_comp_apply,holds_equality]
  erw [model_lift_fst 𝗣𝗔 ℕ,model_lift_snd 𝗣𝗔 ℕ]

theorem valid_generalization (z : Obj 𝗣𝗔 ℕ (variableCarrier ⨯ Y))
    (h : Valid σ π d functions relations ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := variableCarrier) («Y» := Y)) z)) :
    Valid σ π d functions relations ((G).map (S).quantifierConstructor z) := by
  intro ρ
  rw [holds_quantifier]
  exact fun a => h _

theorem valid_modusPonens (z : Obj 𝗣𝗔 ℕ (Y ⨯ Y))
    (hφ : Valid σ π d functions relations ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z))
    (himp : Valid σ π d functions relations ((G).map (S).implicationConstructor z)) :
    Valid σ π d functions relations ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔) («X» := Y) («Y» := Y)) z) := by
  intro ρ
  exact (holds_implication σ π d functions relations z ρ).mp (himp ρ) (hφ ρ)

theorem valid_negation_disjoint [Nonempty K] (φ : Obj 𝗣𝗔 ℕ Y)
    (hφ : Valid σ π d functions relations φ)
    (hnot : Valid σ π d functions relations ((G).map (S).negationConstructor φ)) : False := by
  classical
  let ρ : ℕ → K := fun _ => Classical.choice (inferInstance : Nonempty K)
  exact (holds_negation σ π d functions relations φ ρ).mp (hnot ρ) (hφ ρ)

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
