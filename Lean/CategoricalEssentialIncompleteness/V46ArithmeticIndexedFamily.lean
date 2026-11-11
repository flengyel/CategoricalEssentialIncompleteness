/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedAxioms

/-! # One actual arithmetic derivation object for the indexed axiom family

The logical schemes and inference constructors are the realized named
ones. The full initial algebra is constructed by arbitrary-rule initiality;
its numeral fibers require the separate extensive algebra decomposition.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFamily
open NamedArithmeticSignature

abbrev syntaxData := ArithmeticLiteralModel.sentenceSyntax
abbrev parameter := ArithmeticIndexedAxioms.parameter
abbrev sentence := ArithmeticIndexedAxioms.sentence
abbrev formula := (realization 𝗣𝗔).obj syntaxData.algebra.a.2
abbrev variableObject := (realization 𝗣𝗔).obj variableSymbols
abbrev logicalParameters := (realization 𝗣𝗔).obj syntaxData.logicalParameters

def logical : logicalParameters ⟶ formula := (realization 𝗣𝗔).map syntaxData.logicalAxioms

def sentenceInclusion : sentence ⟶ formula :=
  (realization 𝗣𝗔).map (ArithmeticLiteralModel.sentenceChart.hom ≫ syntaxData.sentenceInclusion)

def generalization : variableObject ⨯ formula ⟶ formula :=
  inv (prodComparison (realization 𝗣𝗔) variableSymbols syntaxData.algebra.a.2) ≫
    (realization 𝗣𝗔).map syntaxData.quantifierConstructor

def implication : formula ⨯ formula ⟶ formula :=
  inv (prodComparison (realization 𝗣𝗔) syntaxData.algebra.a.2 syntaxData.algebra.a.2) ≫
    (realization 𝗣𝗔).map syntaxData.implicationConstructor

def rules (AxPA : Carrier) : RulePresentation (parameter ⨯ formula) 2 :=
  ArithmeticIndexedRules.rules parameter logical sentenceInclusion
    (ArithmeticIndexedAxioms.axioms AxPA) generalization implication

def algebra (AxPA : Carrier) : Endofunctor.Algebra (rules AxPA).inference :=
  SyntacticDerivation.totalDerivationAlgebra 𝗣𝗔 (rules AxPA)

def initial (AxPA : Carrier) : IsInitial (algebra AxPA) :=
  SyntacticDerivation.totalDerivationInitial 𝗣𝗔 (rules AxPA)

def conclusion (AxPA : Carrier) : (algebra AxPA).a.left ⟶ parameter ⨯ formula :=
  (algebra AxPA).a.hom

def sentenceProof (AxPA : Carrier) : TotalSplit 𝗣𝗔 :=
  pullback (conclusion AxPA) (prod.map (𝟙 parameter) sentenceInclusion)

def sentenceConclusion (AxPA : Carrier) : sentenceProof AxPA ⟶ parameter ⨯ sentence :=
  pullback.snd (conclusion AxPA) (prod.map (𝟙 parameter) sentenceInclusion)

def formulaTheory (AxPA : Carrier) : Subobject (parameter ⨯ formula) :=
  imageSubobject (conclusion AxPA)

def sentenceTheory (AxPA : Carrier) : Subobject (parameter ⨯ sentence) :=
  imageSubobject (sentenceConclusion AxPA)

theorem sentenceTheory_pullback (AxPA : Carrier) :
    sentenceTheory AxPA =
      (Subobject.pullback (prod.map (𝟙 parameter) sentenceInclusion)).obj
        (formulaTheory AxPA) :=
  sentenceImage_subobject (conclusion AxPA) (prod.map (𝟙 parameter) sentenceInclusion)

theorem formulaTheory_least (AxPA : Carrier) :
    ClosedUnder (rules AxPA).inference (image.ι (conclusion AxPA)) ∧
      ∀ {U : TotalSplit 𝗣𝗔} (m : U ⟶ parameter ⨯ formula) [Mono m],
        ClosedUnder (rules AxPA).inference m →
          ∃ w : image (conclusion AxPA) ⟶ U, w ≫ m = image.ι (conclusion AxPA) :=
  (rules AxPA).least_theorem_subobject (algebra AxPA) (initial AxPA)

def axiomIntroduction (AxPA : Carrier) :
    ArithmeticIndexedAxioms.axiomObject AxPA ⟶ (algebra AxPA).a.left :=
  coprod.inr ≫ SyntacticDerivation.totalNullaryDerivation 𝗣𝗔 (rules AxPA)

@[reassoc] theorem axiomIntroduction_conclusion (AxPA : Carrier) :
    axiomIntroduction AxPA ≫ conclusion AxPA =
      ArithmeticIndexedAxioms.axioms AxPA ≫ prod.map (𝟙 parameter) sentenceInclusion := by
  have h := congrArg
    (fun k => (coprod.inr : ArithmeticIndexedAxioms.axiomObject AxPA ⟶
      (rules AxPA).instances 0) ≫ k)
    (SyntacticDerivation.totalNullaryDerivation_conclusion 𝗣𝗔 (rules AxPA))
  exact (Category.assoc _ _ _).trans (h.trans
    (ArithmeticIndexedRules.nullary_axiom_conclusion parameter logical sentenceInclusion
      (ArithmeticIndexedAxioms.axioms AxPA) generalization implication))

def fold (AxPA : Carrier) (B : Endofunctor.Algebra (rules AxPA).inference) :
    algebra AxPA ⟶ B := (initial AxPA).to B

theorem fold_unique (AxPA : Carrier) (B : Endofunctor.Algebra (rules AxPA).inference)
    (f : algebra AxPA ⟶ B) : f = fold AxPA B :=
  (initial AxPA).hom_ext f _

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFamily
