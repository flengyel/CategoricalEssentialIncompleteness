/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearch
public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateCoordinates
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! # The printed primitive-recursive Neg extension and actual Γ refutation

The primitive-recursion, PA-totality and constructor-graph proofs are first
given for an arbitrary raw polynomial and arbitrary typed model point.
The arithmetic fixed-formula instance then uses its proved sentence range.
No chosen sentence-point code is used in this comparison.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

namespace NegationCoding

def graph (q : RawPolynomial) : 𝚺₁.Semisentence 2 :=
  let G := Coding.constructorGraph true q
  .mkSigma “out word. ∃ a b c, !pairDef.val a word 1 ∧ !pairDef.val b a 0 ∧
    !pairDef.val c b 0 ∧ !G.val out c”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def word (q : RawPolynomial) (w : M) : M :=
  Coding.constructor true q (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair w 1) 0) 0)

@[simp] theorem graph_eval (q : RawPolynomial) (out w : M) :
    (graph q).val.Evalb ![out,w] ↔ out = word q w := by
  simp [graph,word]

end Models

theorem word_primrec (q : RawPolynomial) : Primrec (word q : ℕ → ℕ) :=
  (NatVectors.constructor_primrec true q).comp
    (NatVectors.pair_primrec.comp
      (NatVectors.pair_primrec.comp
        (NatVectors.pair_primrec.comp Primrec.id (Primrec.const 1)) (Primrec.const 0))
      (Primrec.const 0))

def totalitySentence (q : RawPolynomial) : ArithmeticSentence :=
  let G := graph q
  “∀ word, ∃ out, !G.val out word ∧ ∀ other, !G.val other word → other = out”

theorem totality_PA (q : RawPolynomial) : 𝗣𝗔 ⊢ totalitySentence q := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff,totalitySentence]

section Constructors
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "Y" => (Postfix.plainCarrier true (SyntaxPolynomial.termExpression V σ d)
  (SyntaxPolynomial.formulaExpression V π d) : PredicateCategory T)

/-- An arbitrary typed formula point, including a nonstandard one, has
the literal constructor word as the output of the actual negation graph. -/
theorem constructor_graph (x : SyntacticLists.Obj T M Y) (y : M) :
    (chosenGraph T (S).negationConstructor).graph.val.Evalb ![x.val,y] ↔
      y = word (SyntaxPolynomial.formulaExpression V π d) x.val := by
  have hv := NamedPlainOperationsModels.negation_value T M V σ π d x
  constructor
  · intro h
    have he := (ConcreteNamedComparison.chosenGraph_value_iff T M (S).negationConstructor x y).mp h
    exact he.symm.trans hv
  · intro h
    apply (ConcreteNamedComparison.chosenGraph_value_iff T M (S).negationConstructor x y).mpr
    exact hv.trans h.symm

theorem constructor_graph_of_member (x y : M) (hx : (Y).val.Evalb ![x]) :
    (chosenGraph T (S).negationConstructor).graph.val.Evalb ![x,y] ↔
      y = word (SyntaxPolynomial.formulaExpression V π d) x :=
  constructor_graph T M V σ π d ⟨x,hx⟩ y

end Constructors
end NegationCoding

open NamedArithmeticSignature

def negationWord (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (w : M) : M :=
  NegationCoding.word formulaPolynomial w

def negationWordGraph : 𝚺₁.Semisentence 2 := NegationCoding.graph formulaPolynomial

theorem negationWord_primrec : Primrec (negationWord ℕ : ℕ → ℕ) :=
  NegationCoding.word_primrec formulaPolynomial

theorem negationWord_formulaCode (φ : Formula) :
    negationWord ℕ (NamedArithmeticSignature.formulaCode φ) =
      NamedArithmeticSignature.formulaCode (.neg φ) := rfl

def negationWordTotalitySentence : ArithmeticSentence :=
  NegationCoding.totalitySentence formulaPolynomial

theorem negationWord_total_PA : 𝗣𝗔 ⊢ negationWordTotalitySentence :=
  NegationCoding.totality_PA formulaPolynomial

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem negationWordGraph_eval (out w : M) :
    negationWordGraph.val.Evalb ![out,w] ↔ out = negationWord M w :=
  NegationCoding.graph_eval formulaPolynomial out w

/-- This is exactly the printed C'(n)=ProvΓ(Neg(Θ(n))) equation. The
sentence-range premise is proved by the fixed-formula construction. -/
theorem negative_eval_word (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    (negative Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![negationWord M (NamedArithmeticFixedSubstitution.value φ n)] := by
  have hs := NamedArithmeticFixedSubstitution.value_sentence (M := M) φ hφ n
  have hx := ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M _).mp hs).1
  have hg : ∀ y : M,
      (chosenGraph 𝗣𝗔
        (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).negationConstructor).graph.val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n,y] ↔
        y = negationWord M (NamedArithmeticFixedSubstitution.value φ n) := by
    intro y
    exact NegationCoding.constructor_graph_of_member 𝗣𝗔 M
      variableSymbols functionSymbols relationSymbols bound _ y hx
  rw [negative_eval M Γ φ n]
  simp only [hg,exists_eq_left]

end Models
end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
