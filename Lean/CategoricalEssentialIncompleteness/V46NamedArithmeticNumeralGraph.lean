/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumeralCarriers

/-! The numeral words define an actual PA-total morphism into the closed
term predicate. Its standard values are the unchanged literal named
postfix encodings. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
open NamedArithmeticSignature

def numeralMorphismGraph : 𝚺₁.Semisentence 2 := .mkSigma “n word. !variableSymbols.val n ∧ !numeralGraph.val word n”

def numeralMorphism : GraphMorphism 𝗣𝗔 variableSymbols closedTermCarrier where
  graph := numeralMorphismGraph
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ hM
    rw [models_iff,supportSentence_eval]
    intro n word h
    have hn : variableSymbols.val.Evalb ![n] ∧ word = numeralCode n := by
      simpa [numeralMorphismGraph] using h
    exact ⟨hn.1,hn.2.symm ▸ numeralCode_closed n⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ hM
    rw [models_iff,totalSentence_eval]
    intro n hn
    refine ⟨numeralCode n,?_,?_⟩
    · simp [numeralMorphismGraph]
    · intro word hw
      simpa [numeralMorphismGraph] using hw

theorem zeroWord_standard : (zeroWord : ℕ) = termCode zero := by
  rfl

theorem oneWord_standard : (oneWord : ℕ) = termCode one := by
  rfl

theorem addWord_standard (s t : Term) :
    addWord (termCode s) (termCode t) = termCode (add s t) := by
  rfl

/-- This equality is about the standard arithmetic code model. The
internal carrier theorem above independently covers nonstandard n. -/
theorem numeralCode_standard (n : ℕ) : numeralCode n = termCode (numeral n) := by
  induction n with
  | zero => simpa using zeroWord_standard
  | succ n ih => rw [numeralCode_succ,ih,oneWord_standard,addWord_standard]; rfl

end CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
