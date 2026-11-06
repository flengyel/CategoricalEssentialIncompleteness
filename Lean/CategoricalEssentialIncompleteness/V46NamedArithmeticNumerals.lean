import CategoricalEssentialIncompleteness.V46NamedArithmeticSignature
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser
import CategoricalEssentialIncompleteness.V46NamedArithmeticPrimitiveRecursion
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariables

/-! Internal arithmetic numerals are literal zero/add/one postfix words.
The recursion has a PA-total graph in every PA model and an independent
standard primitive-recursion certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
open NamedArithmeticSignature

/-- The three finite-sum tags are the actual left-associated arity chart. -/
def zeroGraph : 𝚺₁.Semisentence 1 :=
  let C := constructorGraph false termPolynomial
  .mkSigma “out. ∃ a b c u, !pairDef.val a 0 0 ∧ !pairDef.val b a 0 ∧
    !pairDef.val c b 0 ∧ !pairDef.val u c 1 ∧ !C.val out u”
def oneGraph : 𝚺₁.Semisentence 1 :=
  let C := constructorGraph false termPolynomial
  .mkSigma “out. ∃ a b c u, !pairDef.val a 1 0 ∧ !pairDef.val b a 0 ∧
    !pairDef.val c b 0 ∧ !pairDef.val u c 1 ∧ !C.val out u”
def addGraph : 𝚺₁.Semisentence 3 :=
  let C := constructorGraph false termPolynomial
  .mkSigma “out left right. ∃ a b c u, !pairDef.val a left right ∧ !pairDef.val b 0 a ∧
    !pairDef.val c b 1 ∧ !pairDef.val u c 1 ∧ !C.val out u”

def blueprint : PR.Blueprint 0 where
  zero := zeroGraph
  succ := .mkSigma “out previous index. ∃ one, !oneGraph.val one ∧ !addGraph.val out previous one”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def zeroInput : M := ⟪⟪⟪⟪0,0⟫,0⟫,0⟫,1⟫
def oneInput : M := ⟪⟪⟪⟪1,0⟫,0⟫,0⟫,1⟫
def addInput (left right : M) : M := ⟪⟪⟪0,⟪left,right⟫⟫,1⟫,1⟫
def zeroWord : M := constructor false termPolynomial zeroInput
def oneWord : M := constructor false termPolynomial oneInput
def addWord (left right : M) : M := constructor false termPolynomial (addInput left right)

@[simp] theorem zeroGraph_eval (out : M) : zeroGraph.val.Evalb ![out] ↔ out = zeroWord := by
  simp [zeroGraph,zeroWord,zeroInput]
@[simp] theorem oneGraph_eval (out : M) : oneGraph.val.Evalb ![out] ↔ out = oneWord := by
  simp [oneGraph,oneWord,oneInput]
@[simp] theorem addGraph_eval (out left right : M) :
    addGraph.val.Evalb ![out,left,right] ↔ out = addWord left right := by
  simp [addGraph,addWord,addInput]

def construction : PR.Construction M blueprint where
  zero _ := zeroWord
  succ _ _ previous := addWord previous oneWord
  zero_defined := .mk fun v => by
    change zeroGraph.val.Evalb v ↔ v 0 = zeroWord
    have hv : ![v 0] = v := by funext i; fin_cases i; rfl
    simpa only [hv] using zeroGraph_eval (v 0)
  succ_defined := .mk fun v => by simp [blueprint]

def numeralCode (n : M) : M := NamedArithmeticPrimitiveRecursion.scalarResult construction n

private theorem construction_zero (p : Fin 0 → M) : (construction (M := M)).zero p = zeroWord := rfl
private theorem construction_succ (p : Fin 0 → M) (n previous : M) :
    (construction (M := M)).succ p n previous = addWord previous oneWord := rfl

@[simp] theorem numeralCode_zero : numeralCode (0 : M) = zeroWord := by
  change construction.result ![] 0 = zeroWord
  exact (construction.result_zero ![]).trans (construction_zero ![])
@[simp] theorem numeralCode_succ (n : M) : numeralCode (n+1) = addWord (numeralCode n) oneWord := by
  change construction.result ![] (n+1) = addWord (construction.result ![] n) oneWord
  exact (construction.result_succ ![] n).trans (construction_succ ![] n _)

end Models

def numeralGraph : 𝚺₁.Semisentence 2 := blueprint.resultDef

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem numeralGraph_eval (out n : M) :
    numeralGraph.val.Evalb ![out,n] ↔ out = numeralCode n :=
  NamedArithmeticPrimitiveRecursion.scalarResult_eval construction out n

instance numeralCode_defined : 𝚺₁-Function₁ (numeralCode : M → M) via numeralGraph :=
  NamedArithmeticPrimitiveRecursion.scalarResult_defined construction
instance numeralCode_definable : 𝚺₁-Function₁ (numeralCode : M → M) :=
  NamedArithmeticPrimitiveRecursion.scalarResult_definable construction
instance numeralCode_definable' (Γ m) : Γ-[m+1]-Function₁ (numeralCode : M → M) :=
  NamedArithmeticPrimitiveRecursion.scalarResult_definable' construction Γ m
end Models

open SyntacticSyntax.NatVectors

theorem addInput_primrec : Primrec₂ (addInput : ℕ → ℕ → ℕ) :=
  pair_primrec.comp
    (pair_primrec.comp (pair_primrec.comp (Primrec.const 0) (pair_primrec.comp Primrec.fst Primrec.snd))
      (Primrec.const 1)) (Primrec.const 1)

theorem addWord_primrec : Primrec₂ (addWord : ℕ → ℕ → ℕ) :=
  (constructor_primrec false termPolynomial).comp addInput_primrec

theorem numeralCode_primrec : Primrec (numeralCode : ℕ → ℕ) := by
  have hz : Primrec (fun _ : Unit => (construction (M := ℕ)).zero ![]) := Primrec.const _
  have hs : Primrec₂ (fun (_ : Unit) (v : ℕ × ℕ) => (construction (M := ℕ)).succ ![] v.1 v.2) := by
    exact addWord_primrec.comp (Primrec.snd.comp Primrec.snd) (Primrec.const oneWord)
  exact NamedArithmeticPrimitiveRecursion.scalarResult_primrec construction hz hs

end CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
