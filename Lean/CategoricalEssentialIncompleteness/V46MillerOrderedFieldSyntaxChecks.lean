import CategoricalEssentialIncompleteness.V46MillerOrderedFieldSyntax

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSyntax

example : bound=2 := rfl
example : PrimrecPred (fun x : ℕ × ℕ => (functionSymbols x.1).val.Evalb ![x.2]) :=
  functionSymbols_primrec
example : PrimrecPred (fun x : ℕ × ℕ => (relationSymbols x.1).val.Evalb ![x.2]) :=
  relationSymbols_primrec
example (n j : ℕ) : formulaCode (belowSentence n j)=belowWord n j := formulaCode_belowSentence n j
example (n j : ℕ) : formulaCode (aboveSentence n j)=aboveWord n j := formulaCode_aboveSentence n j
example : Primrec₂ belowWord := belowWord_primrec
example : Primrec₂ aboveWord := aboveWord_primrec
example : Primrec theta := theta_primrec
example (n : ℕ) : theta n=formulaCode (lt (mul (natural 2) (c n)) one) := rfl
example (n : ℕ) : belowSentence n halfIndex=lt one (mul (natural 2) (c n)) := below_half_shape n
example (n : ℕ) : aboveSentence n halfIndex=lt (mul (natural 2) (c n)) one := above_half_shape n
example (n j : ℕ) : sentencePredicate.val.Evalb ![belowWord n j] := belowWord_sentence n j
example (n j : ℕ) : sentencePredicate.val.Evalb ![aboveWord n j] := aboveWord_sentence n j
example (n : ℕ) : sentencePredicate.val.Evalb ![theta n] := theta_sentence n
example (φ : Formula) : formulaCode (negation φ)=
    SyntacticSyntax.Coding.constructor true formulaPolynomial
      (NamedPostfixEncoding.negInput (formulaCode φ)) := formulaCode_negation φ
example : sentencePredicate.val.Evalb ![formulaCode orderAsymmetry] := orderAsymmetry_sentence
example (a : Point) : Uniform.Enumerable (Uniform.Family.ofPoint a) (fun word =>
    (∃ n j,(Rationals.q j : ℝ)<(a n : ℝ) ∧ belowWord n j=word) ∨
    (∃ n j,(a n : ℝ)<(Rationals.q j : ℝ) ∧ aboveWord n j=word)) := cutAxioms_enumerable a
example (a : Point) (word : ℕ) (h : word∈cutAxioms a) :
    sentencePredicate.val.Evalb ![word] := cutAxioms_sentences a word h
example (a : Point) (n : ℕ) (h : (a n : ℝ)<1/2) : theta n∈cutAxioms a := lower_cut_axiom a n h
example (a : Point) (n : ℕ) (h : 1/2<(a n : ℝ)) :
    formulaCode (lt one (mul (natural 2) (c n)))∈cutAxioms a := upper_cut_axiom a n h

end CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSyntax
