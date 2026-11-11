/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbert
public import CategoricalEssentialIncompleteness.V46NamedPlainSemantics
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainAdmissibleValues
public import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution

/-! # Genuine model points for literal named derivation instances -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open NamedFiniteSyntax NamedPostfixEncoding NamedPostfixPlainComparison NamedPlainSemantics
open ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "G" => F 𝗣𝗔 ℕ

def termPoint (t : Tm) : Obj 𝗣𝗔 ℕ X := plainTermModelEquiv σ π d t

def formulaPoint (φ : Fm) : Obj 𝗣𝗔 ℕ Y := plainFormulaModelEquiv σ π d φ

def namePoint (x : ℕ) : Obj 𝗣𝗔 ℕ variableCarrier := ⟨x,by simp [variableCarrier]⟩

@[simp] theorem termPoint_value (t : Tm) : (termPoint σ π d t).val = termCode t :=
  @plainTermModelEquiv_val σ π d t

@[simp] theorem formulaPoint_value (φ : Fm) : (formulaPoint σ π d φ).val = formulaCode φ :=
  @plainFormulaModelEquiv_val σ π d φ

@[simp] theorem decode_termPoint (t : Tm) : decodeTerm σ π d (termPoint σ π d t) = t :=
  (plainTermModelEquiv σ π d).symm_apply_apply t

@[simp] theorem decode_formulaPoint (φ : Fm) : decodeFormula σ π d (formulaPoint σ π d φ) = φ :=
  (plainFormulaModelEquiv σ π d).symm_apply_apply φ

theorem formulaPoint_of_decode (p : Obj 𝗣𝗔 ℕ Y) (φ : Fm) (h : decodeFormula σ π d p = φ) :
    p = formulaPoint σ π d φ := by
  have he : formulaPoint σ π d (decodeFormula σ π d p) = p :=
    (plainFormulaModelEquiv σ π d).apply_symm_apply p
  exact he.symm.trans (congrArg (formulaPoint σ π d) h)

theorem negation_point (φ : Fm) :
    (G).map (S).negationConstructor (formulaPoint σ π d φ) = formulaPoint σ π d (.neg φ) := by
  apply formulaPoint_of_decode σ π d
  erw [decode_negation,decode_formulaPoint]

theorem implication_point (φ ψ : Fm) :
    (G).map (S).implicationConstructor
      (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) =
        formulaPoint σ π d (.imp φ ψ) := by
  apply formulaPoint_of_decode σ π d
  have hd := decode_implication σ π d
    (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
  exact hd.trans (congrArg₂ NamedFiniteSyntax.Formula.imp
    ((congrArg (decodeFormula σ π d) (pairPoint_fst 𝗣𝗔 ℕ _ _)).trans
      (decode_formulaPoint σ π d φ))
    ((congrArg (decodeFormula σ π d) (pairPoint_snd 𝗣𝗔 ℕ _ _)).trans
      (decode_formulaPoint σ π d ψ)))

theorem equality_point (u t : Tm) :
    (G).map (S).equalityConstructor
      (pairPoint 𝗣𝗔 ℕ (termPoint σ π d u) (termPoint σ π d t)) =
        formulaPoint σ π d (.equal u t) := by
  apply formulaPoint_of_decode σ π d
  have hd := decode_equality σ π d
    (pairPoint 𝗣𝗔 ℕ (termPoint σ π d u) (termPoint σ π d t))
  exact hd.trans (congrArg₂ NamedFiniteSyntax.Formula.equal
    ((congrArg (decodeTerm σ π d) (pairPoint_fst 𝗣𝗔 ℕ _ _)).trans
      (decode_termPoint σ π d u))
    ((congrArg (decodeTerm σ π d) (pairPoint_snd 𝗣𝗔 ℕ _ _)).trans
      (decode_termPoint σ π d t)))

theorem quantifier_point (x : ℕ) (φ : Fm) :
    (G).map (S).quantifierConstructor
      (pairPoint 𝗣𝗔 ℕ (namePoint x) (formulaPoint σ π d φ)) =
        formulaPoint σ π d (.all x φ) := by
  apply formulaPoint_of_decode σ π d
  erw [decode_quantifier,pairPoint_fst,pairPoint_snd,decode_formulaPoint]
  rfl

/-- The public source is word-first, with its genuine nested chosen
product point. No underlying product code is identified with a pair. -/
def substitutionPoint (x : ℕ) (φ : Fm) (t : Tm) :
    Obj 𝗣𝗔 ℕ (Y ⨯ (S).substitutionParameters) :=
  pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ)
    (pairPoint 𝗣𝗔 ℕ (namePoint x) (termPoint σ π d t))

/-- Scalar functions read only the actual three product projections. -/
theorem substitutionInput_scalar (k : ℕ → ℕ → ℕ → ℕ) (x : ℕ) (φ : Fm) (t : Tm) :
    k ((G).map (prod.fst : (S).substitutionParameters ⟶ variableCarrier)
        ((G).map prod.snd (substitutionPoint σ π d x φ t))).val
      ((G).map (prod.snd : (S).substitutionParameters ⟶ X)
        ((G).map prod.snd (substitutionPoint σ π d x φ t))).val
      ((G).map prod.fst (substitutionPoint σ π d x φ t)).val =
        k x (termCode t) (formulaCode φ) := by
  simp only [substitutionPoint,pairPoint_fst,pairPoint_snd,
    termPoint_value,formulaPoint_value,namePoint]

/-- The separately defined named free-for condition constructs an
actual point of the categorical success pullback. -/
theorem admissiblePoint_exists (x : ℕ) (φ : Fm) (t : Tm) (h : φ.FreeFor x t) :
    ∃ a : Obj 𝗣𝗔 ℕ (S).admissibleSubstitution,
      (G).map (S).admissibleInclusion a = substitutionPoint σ π d x φ t := by
  apply (plain_admissible_model_iff 𝗣𝗔 variableCarrier σ π d ℕ
    (substitutionPoint σ π d x φ t)).mpr
  have hf := (@substitutionFreeFor_formulaCode σ π d φ t x).mpr h
  simpa only [substitutionPoint,pairPoint_fst,pairPoint_snd,
    termPoint_value,formulaPoint_value,namePoint] using hf

/-- An actual admissibility point with the specified public coordinates
has exactly the successful literal named output. -/
theorem substitution_point (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (a : Obj 𝗣𝗔 ℕ (S).admissibleSubstitution)
    (ha : (G).map (S).admissibleInclusion a = substitutionPoint σ π d x φ t)
    (hs : φ.substitute x t = some ψ) :
    (G).map (S).formulaSubstitution a = formulaPoint σ π d ψ := by
  let raw : Obj 𝗣𝗔 ℕ (Y ⨯ (S).substitutionParameters) → ℕ := fun q =>
    ConcreteNamedSubstitution.substitutionResult variableCarrier σ π d
      ((G).map (prod.fst : (S).substitutionParameters ⟶ variableCarrier)
        ((G).map prod.snd q)).val
      ((G).map (prod.snd : (S).substitutionParameters ⟶ X)
        ((G).map prod.snd q)).val ((G).map prod.fst q).val
  have hr : raw ((G).map (S).admissibleInclusion a) =
      ConcreteNamedSubstitution.ok ((G).map (S).formulaSubstitution a).val :=
    plain_formulaSubstitution_result 𝗣𝗔 variableCarrier σ π d ℕ a
  have hc : raw (substitutionPoint σ π d x φ t) =
      ConcreteNamedSubstitution.substitutionResult variableCarrier σ π d x (termCode t) (formulaCode φ) :=
    substitutionInput_scalar σ π d
      (ConcreteNamedSubstitution.substitutionResult variableCarrier σ π d) x φ t
  have he := hc.symm.trans ((congrArg raw ha).symm.trans hr)
  rw [@substitutionResult_formulaCode σ π d φ t x,hs] at he
  apply Subtype.ext
  have hv := congrArg (fun n : ℕ => π₁ n) he
  have hp : formulaCode ψ = ((G).map (S).formulaSubstitution a).val := by
    simpa only [NamedPostfixEncoding.optionCode,ConcreteNamedSubstitution.ok,pi₁_pair] using hv
  exact hp.symm.trans (formulaPoint_value σ π d ψ).symm

/-- Every intended successful instance is lifted through the real
admissibility object, with both its inclusion and its result preserved. -/
theorem substitution_instance (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    ∃ a : Obj 𝗣𝗔 ℕ (S).admissibleSubstitution,
      (G).map (S).admissibleInclusion a = substitutionPoint σ π d x φ t ∧
        (G).map (S).formulaSubstitution a = formulaPoint σ π d ψ := by
  obtain ⟨a,ha⟩ := admissiblePoint_exists σ π d x φ t hff
  exact ⟨a,ha,substitution_point σ π d x φ t ψ a ha hs⟩

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
