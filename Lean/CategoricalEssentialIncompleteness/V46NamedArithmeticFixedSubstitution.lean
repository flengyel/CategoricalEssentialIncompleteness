/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumeralGraph
public import CategoricalEssentialIncompleteness.V46NamedArithmeticSubstitutionOccurrences
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences

/-! Numeral substitution for a generic finite named arithmetic formula.
The complete PA range proof precedes every arithmetic-formula or chosen
index specialization. No source numeral is evaluated during that proof. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticFixedSubstitution
open NamedArithmeticSignature NamedArithmeticNumerals ConcreteNamedSubstitution
open NamedArithmeticStandardCodes NamedArithmeticModelCoding NamedArithmeticModelSubstitution
open NamedArithmeticSubstitutionOccurrences

def sourceWord (φ : Formula) : ℕ := NamedArithmeticSignature.formulaCode φ

def graph (φ : Formula) : 𝚺₁.Semisentence 2 :=
  let N := numeralGraph
  let S := substitutionResultGraph variableSymbols functionSymbols relationSymbols bound
  .mkSigma “out index. ∃ term res, !N.val term index ∧
    !S.val res 0 term !!(FiniteSigmaOne.numeralTerm (sourceWord φ)) ∧ !pi₁Def.val out res”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def value (φ : Formula) (n : M) : M :=
  π₁ (substitutionResult variableSymbols functionSymbols relationSymbols bound
    0 (numeralCode (M := M) n) (sourceWord φ : M))

@[simp] theorem graph_eval (φ : Formula) (out n : M) :
    (graph φ).val.Evalb ![out,n] ↔ out = value φ n := by
  simp [graph,value,FiniteSigmaOne.numeralTerm,numeral_eq_natCast]

instance value_defined (φ : Formula) :
    𝚺₁-Function₁ (value φ : M → M) via graph φ := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using graph_eval (M := M) φ (v 0) (v 1)
instance value_definable (φ : Formula) : 𝚺₁-Function₁ (value φ : M → M) :=
  (value_defined (M := M) φ).to_definable

 theorem sourceWord_eq_model (φ : Formula) :
    (sourceWord φ : M) = formulaWord (M := M) (σ := functionSymbols) (π := relationSymbols) (d := bound) φ :=
  formulaWord_natCast (M := M) (σ := functionSymbols) (π := relationSymbols) (d := bound) φ

 theorem sourceWord_freeVariables (φ : Formula) :
    freeVariables variableSymbols functionSymbols relationSymbols bound (sourceWord φ : M) =
      ((NatVectors.pack φ.freeVariables : ℕ) : M) := by
  have hc := freeVariables_natCast (M := M) variableSymbols functionSymbols relationSymbols bound (sourceWord φ)
  have hN : (freeVariables variableSymbols functionSymbols relationSymbols bound (sourceWord φ) : ℕ) =
      NatVectors.pack φ.freeVariables := NamedPostfixEncoding.freeVariables_formulaCode φ
  exact hc.symm.trans (congrArg (fun k : ℕ => (k : M)) hN)

 theorem sourceWord_members (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (name : M)
    (h : member name (freeVariables variableSymbols functionSymbols relationSymbols bound (sourceWord φ : M)) = 1) :
    name = 0 := by
  rw [sourceWord_freeVariables (M := M) φ,member_pack_natCast (M := M)] at h
  obtain ⟨y,hy,he⟩ := h
  simpa only [hφ y hy,Nat.cast_zero] using he.symm

 theorem value_eq_output (φ : Formula) (n : M) :
    value φ n = formulaOutput (M := M) (σ := functionSymbols) (π := relationSymbols) (d := bound)
      0 (numeralCode n) φ := by
  unfold value
  rw [sourceWord_eq_model (M := M) φ]
  rw [formulaResult_eq (M := M) (σ := functionSymbols) (π := relationSymbols) (d := bound)
    0 (numeralCode n) (numeralCode_carrier_closed (M := M) n).1 (numeralCode_carrier_closed (M := M) n).2,
    ok,pi₁_pair]

 theorem value_carrier (φ : Formula) (n : M) :
    formulaCarrier.val.Evalb ![value φ n] := by
  rw [value_eq_output (M := M) φ n]
  exact formulaOutput_member (M := M) (σ := functionSymbols) (π := relationSymbols) (d := bound)
    0 (numeralCode n) (numeralCode_carrier_closed (M := M) n).1 (numeralCode_carrier_closed (M := M) n).2 φ

 theorem value_closed (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    freeVariables variableSymbols functionSymbols relationSymbols bound (value φ n) = 0 := by
  rw [value_eq_output (M := M) φ n]
  apply result_sentence (M := M) functionSymbols relationSymbols bound 0 (numeralCode n)
    (numeralCode_carrier_closed (M := M) n).1 (numeralCode_carrier_closed (M := M) n).2 φ
  intro name hn
  apply sourceWord_members (M := M) φ hφ name
  rw [sourceWord_eq_model (M := M) φ]
  exact hn

 theorem value_sentence (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).val.Evalb
      ![value φ n] := by
  apply (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound M _).mpr
  exact ⟨(Postfix.carrier_plain_model (M := M) true NamedArithmeticSignature.termPolynomial
    NamedArithmeticSignature.formulaPolynomial (value φ n)).mp (value_carrier (M := M) φ n),value_closed (M := M) φ hφ n⟩

 theorem value_admissible (φ : Formula) (n : M) :
    substitutionFreeFor variableSymbols functionSymbols relationSymbols bound
      0 (numeralCode n) (sourceWord φ : M) = 1 :=
  NamedArithmeticClosedSubstitution.substitutionFreeFor_closed (M := M) variableSymbols functionSymbols relationSymbols bound
    0 (numeralCode n) (sourceWord φ : M) (numeralCode_carrier_closed (M := M) n).1 (numeralCode_carrier_closed (M := M) n).2
    (carrier_natCast (M := M) _ _ (NamedPostfixEncoding.formulaCode_member φ))

 theorem value_success (φ : Formula) (n : M) :
    substitutionResult variableSymbols functionSymbols relationSymbols bound
      0 (numeralCode n) (sourceWord φ : M) = ok (value φ n) := by
  rw [sourceWord_eq_model (M := M) φ,value_eq_output (M := M) φ n]
  exact formulaResult_eq (M := M) (σ := functionSymbols) (π := relationSymbols) (d := bound)
    0 (numeralCode n) (numeralCode_carrier_closed (M := M) n).1 (numeralCode_carrier_closed (M := M) n).2 φ

end Models

open SyntacticSyntax.NatVectors
private theorem fixedReplacement_primrec {f : ℕ × ℕ × ℕ → ℕ} (hf : Primrec f)
    {g : ℕ → ℕ} (hg : Primrec g) (word : ℕ) :
    Primrec (fun n : ℕ => π₁ (f (0,g n,word))) :=
  pi1_primrec.comp (hf.comp
    (Primrec.pair (Primrec.const 0) (Primrec.pair hg (Primrec.const word))))

 theorem value_primrec (φ : Formula) : Primrec (value φ : ℕ → ℕ) := by
  exact Primrec.of_eq
    (fixedReplacement_primrec
      (substitutionResult_primrec variableSymbols functionSymbols relationSymbols bound)
      numeralCode_primrec (sourceWord φ)) (fun _ => by simp only [value,natCast_nat])

/-- The only source condition is its explicit external free-name bound;
PA range and totality are proved from the actual constructor algorithm. -/
def morphism (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) : GraphMorphism 𝗣𝗔 variableSymbols
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound) where
  graph :=
    let H := graph φ
    .mkSigma “n word. !variableSymbols.val n ∧ !H.val word n”
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ hM
    rw [models_iff,supportSentence_eval]
    intro n word h
    have hn : variableSymbols.val.Evalb ![n] ∧ word = value φ n := by simpa using h
    exact ⟨hn.1,hn.2.symm ▸ value_sentence (M := M) φ hφ n⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ hM
    rw [models_iff,totalSentence_eval]
    intro n hn
    refine ⟨value φ n,?_,?_⟩
    · simp
    · intro word hw
      simpa using hw

@[simp] theorem morphism_graph_eval (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n word : M) :
    (morphism φ hφ).graph.val.Evalb ![n,word] ↔ word = value φ n := by
  simp [morphism]

end CategoricalEssentialIncompleteness.V46.NamedArithmeticFixedSubstitution
