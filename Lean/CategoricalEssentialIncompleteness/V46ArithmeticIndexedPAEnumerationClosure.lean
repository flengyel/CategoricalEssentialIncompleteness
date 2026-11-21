/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedPAEnumerationWords
public import CategoricalEssentialIncompleteness.V46NamedPostfixComparison

/-! # Positive finite records for named universal closure

The record peels the outer quantifiers. Its standard interpretation is proved
equivalent to the named UniversalClosure relation. The accepted inner formula is an
existential witness rather than an additional label.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

abbrev formulaCarrier : Carrier :=
  SyntacticSyntax.Postfix.carrier true termPolynomial formulaPolynomial

def allGraph : 𝚺₁.Semisentence 3 :=
  let C := SyntacticSyntax.Coding.constructorGraph true formulaPolynomial
  .mkSigma “outer name inner. ∃ a u, !pairDef.val a name inner ∧
    !pairDef.val u a 1 ∧ !C.val outer u”

def closureStep : SyntacticDerivation.Records.Transition :=
  let F := formulaCarrier
  .mkSigma “outer name inner. !F.val inner ∧ !allGraph.val outer name inner”

def closureRelation : 𝚺₁.Semisentence 2 :=
  let R := SyntacticDerivation.Records.run closureStep
  .mkSigma “outer inner. ∃ names, !R.val names outer inner”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem allGraph_eval (outer name inner : M) :
    allGraph.val.Evalb ![outer,name,inner] ↔
      outer = SyntacticSyntax.Coding.constructor true formulaPolynomial
        (Arithmetic.pair (Arithmetic.pair name inner) 1) := by
  simp [allGraph]

@[simp] theorem closureStep_eval (outer name inner : M) :
    closureStep.val.Evalb ![outer,name,inner] ↔
      formulaCarrier.val.Evalb ![inner] ∧
        outer = SyntacticSyntax.Coding.constructor true formulaPolynomial
          (Arithmetic.pair (Arithmetic.pair name inner) 1) := by
  simp [closureStep]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem closureRelation_eval (outer inner : M) :
    closureRelation.val.Evalb ![outer,inner] ↔
      ∃ names : M, (SyntacticDerivation.Records.run closureStep).val.Evalb
        ![names,outer,inner] := by
  simp [closureRelation]

end Models

theorem allGraph_formulaCode (name : ℕ) (φ : Formula) :
    allGraph.val.Evalb ![formulaCode (.all name φ),name,formulaCode φ] := by
  apply (allGraph_eval _ _ _).mpr
  rfl

/-- Each standard finite record is a finite sequence of named quantifier constructors; no
nonstandard Set initiality is asserted. -/
theorem closure_run_codes (φ ψ : Formula) (names : ℕ)
    (hr : (SyntacticDerivation.Records.run closureStep).val.Evalb
      ![names,formulaCode ψ,formulaCode φ]) : UniversalClosure φ ψ := by
  have aux : ∀ n (word : ℕ), len word = n → ∀ χ : Formula,
      (SyntacticDerivation.Records.run closureStep).val.Evalb
        ![word,formulaCode χ,formulaCode φ] → UniversalClosure φ χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro word hn χ hrun
        rcases nil_or_adjoin word with rfl | ⟨name,tail,rfl⟩
        · have he := (SyntacticDerivation.Records.run_nil closureStep
            (formulaCode χ) (formulaCode φ)).mp hrun
          have hφχ : φ = χ := NamedPostfixEncoding.formulaCode_injective he
          subst χ
          exact .refl
        · obtain ⟨inner,hs,ht⟩ := (SyntacticDerivation.Records.run_adjoin closureStep
            name tail (formulaCode χ) (formulaCode φ)).mp hrun
          obtain ⟨hi,he⟩ := (closureStep_eval _ _ _).mp hs
          obtain ⟨body,hbody⟩ := (NamedPostfixEncoding.standard_codes_surjective
            functionSymbols relationSymbols bound).2 inner hi
          change formulaCode body = inner at hbody
          have hcode : formulaCode (.all name body) = formulaCode χ := by
            change SyntacticSyntax.Coding.constructor true formulaPolynomial
              (Arithmetic.pair (Arithmetic.pair name (formulaCode body)) 1) = _
            rw [hbody]
            exact he.symm
          have hχ : χ = .all name body := NamedPostfixEncoding.formulaCode_injective hcode.symm
          subst χ
          have hsmall : len tail < n := by
            rw [← hn,len_adjoin]
            exact Nat.lt_succ_self _
          have htail : (SyntacticDerivation.Records.run closureStep).val.Evalb
              ![tail,formulaCode body,formulaCode φ] := by
            simpa only [hbody] using ht
          exact .all name (ih (len tail) hsmall tail rfl body htail)
  exact aux (len names) names rfl ψ hr

theorem closure_record {φ ψ : Formula} (h : UniversalClosure φ ψ) :
    ∃ names : ℕ, (SyntacticDerivation.Records.run closureStep).val.Evalb
      ![names,formulaCode ψ,formulaCode φ] := by
  induction h with
  | refl =>
      exact ⟨0,(SyntacticDerivation.Records.run_nil closureStep _ _).mpr rfl⟩
  | @all name body h ih =>
      obtain ⟨names,hr⟩ := ih
      refine ⟨adjoin name names,
        (SyntacticDerivation.Records.run_adjoin closureStep _ _ _ _).mpr
          ⟨formulaCode body,?_,hr⟩⟩
      exact (closureStep_eval _ _ _).mpr
        ⟨NamedPostfixEncoding.formulaCode_member body,((allGraph_eval _ _ _).mp
          (allGraph_formulaCode name body))⟩

theorem closureRelation_codes (φ ψ : Formula) :
    closureRelation.val.Evalb ![formulaCode ψ,formulaCode φ] ↔ UniversalClosure φ ψ := by
  rw [closureRelation_eval]
  exact ⟨fun ⟨names,hr⟩ => closure_run_codes φ ψ names hr,closure_record⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedPAEnumeration
