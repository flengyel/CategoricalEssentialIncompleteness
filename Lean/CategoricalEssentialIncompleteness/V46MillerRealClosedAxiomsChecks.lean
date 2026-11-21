/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedAxioms


/-! # Recognition of the ordered-field and real-closure axiom words -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms
open OrderedFieldSyntax

example : ∀ φ∈finiteSentences,φ.freeVariables=[] := finiteSentences_closed
example (n : ℕ) : (oddSentence n).freeVariables=[] := oddSentence_closed n
example (n : ℕ) : formulaCode (oddSentence n)=oddWord n := formulaCode_oddSentence n
example : Primrec oddWord := oddWord_primrec
example : Primrec allSuffix := allSuffix_primrec
example (n : ℕ) : allSuffix (oddWord n)=2*n+2 := oddWord_suffix n
example (word : ℕ) :
    (2≤allSuffix word ∧ allSuffix word%2=0 ∧ word=oddWord ((allSuffix word-2)/2)) ↔
      ∃ n,word=oddWord n := odd_generator_iff word
example : PrimrecPred (fun word => word∈RCFAxiomWords) := rcfAxiomWords_primrec
example (word : ℕ) : word∈RCFAxiomWords ↔
    (∃ φ∈finiteSentences,formulaCode φ=word) ∨ ∃ n,word=oddWord n := rcf_generator_iff word
example : asymmetryWord∈RCFAxiomWords := asymmetry_mem
example : formulaCode positiveSquare∈RCFAxiomWords := positiveSquare_mem
example (n : ℕ) : formulaCode (oddSentence n)∈RCFAxiomWords := oddSentence_mem n
example (word : ℕ) (h : word∈RCFAxiomWords) : sentencePredicate.val.Evalb ![word] :=
  rcfAxiomWords_sentences word h
example (a : Point) : Uniform.Enumerable (Uniform.Family.ofPoint a)
    (fun word => word∈RCFAxiomWords ∨ word∈cutAxioms a) := theoryAxioms_enumerable a
example (a : Point) (word : ℕ) (h : word∈RCFAxiomWords ∨ word∈cutAxioms a) :
    sentencePredicate.val.Evalb ![word] := theoryAxioms_sentences a word h
example (a : Point) : asymmetryWord∈theoryAxioms a := theory_asymmetry_mem a
example (a : Point) (n : ℕ) (h : (a n : ℝ)<1/2) : theta n∈theoryAxioms a :=
  theory_lower_cut_axiom a n h
example (a : Point) (n : ℕ) (h : 1/2<(a n : ℝ)) :
    formulaCode (lt one (mul (natural 2) (c n)))∈theoryAxioms a := theory_upper_cut_axiom a n h

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms
