import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertOperations

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.OperationsChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example {A B C : PredicateCategory T} (f : A ⟶ C) (g : B ⟶ C)
    (a : Obj T M A) (b : Obj T M B)
    (h : (F T M).map f a = (F T M).map g b) :
    ∃ z : Obj T M (pullback f g),
      (F T M).map (pullback.fst f g) z = a ∧
      (F T M).map (pullback.snd f g) z = b :=
  pullback_point_exists T M f g a b h
example {A : PredicateCategory T} (f : A ⟶ Two (PredicateCategory T))
    (b : Bool) (a : Obj T M A)
    (h : (F T M).map f a = (F T M).map (Two.constant A b) a) :
    ∃ z : Obj T M (Two.Fiber f b), (F T M).map (Two.fiberι f b) z = a :=
  booleanFiber_point_exists T M f b a h

open SyntacticSyntax NamedFiniteSyntax NamedPostfixEncoding
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example {A : PredicateCategory 𝗣𝗔} (f g : A ⟶ Y) (a : Obj 𝗣𝗔 ℕ A)
    (φ ψ : Fm) (hf : (F 𝗣𝗔 ℕ).map f a = formulaPoint σ π d φ)
    (hg : (F 𝗣𝗔 ℕ).map g a = formulaPoint σ π d ψ) :
    (F 𝗣𝗔 ℕ).map (prod.lift f g ≫ (S).implicationConstructor) a =
      formulaPoint σ π d (.imp φ ψ) := implication_at σ π d f g a φ ψ hf hg

example {A : PredicateCategory 𝗣𝗔} (f : A ⟶ Y) (a : Obj 𝗣𝗔 ℕ A)
    (φ : Fm) (hf : (F 𝗣𝗔 ℕ).map f a = formulaPoint σ π d φ) :
    (F 𝗣𝗔 ℕ).map (f ≫ (S).negationConstructor) a =
      formulaPoint σ π d (.neg φ) := negation_at σ π d f a φ hf

example {A : PredicateCategory 𝗣𝗔} (f g : A ⟶ X) (a : Obj 𝗣𝗔 ℕ A)
    (u t : Tm) (hf : (F 𝗣𝗔 ℕ).map f a = termPoint σ π d u)
    (hg : (F 𝗣𝗔 ℕ).map g a = termPoint σ π d t) :
    (F 𝗣𝗔 ℕ).map (prod.lift f g ≫ (S).equalityConstructor) a =
      formulaPoint σ π d (.equal u t) := equality_at σ π d f g a u t hf hg

example {A : PredicateCategory 𝗣𝗔} (f : A ⟶ variableCarrier) (g : A ⟶ Y)
    (a : Obj 𝗣𝗔 ℕ A) (x : ℕ) (φ : Fm)
    (hf : (F 𝗣𝗔 ℕ).map f a = namePoint x)
    (hg : (F 𝗣𝗔 ℕ).map g a = formulaPoint σ π d φ) :
    (F 𝗣𝗔 ℕ).map (prod.lift f g ≫ (S).quantifierConstructor) a =
      formulaPoint σ π d (.all x φ) := quantifier_at σ π d f g a x φ hf hg

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.OperationsChecks
