/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTotal
public import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # The parameter-preserving inference signature of the arithmetic family

The parameter belongs to every premise and the conclusion. Children keep
their individual formula coordinates. Nullary nonlogical rules are the
given family axiom object, rather than a constant family.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedRules

section Signature
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable (E : D) {V F L S A : D}

/-- The displayed arity-0, arity-1 and arity-2 data of §7.2,
with its common external E-coordinate. -/
def rules (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ E ⨯ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) : RulePresentation (E ⨯ F) 2 where
  instances := ![(E ⨯ L) ⨿ A, E ⨯ (V ⨯ F), E ⨯ (F ⨯ F)]
  premises := Fin.cases (terminal.from _) (Fin.cases
    (prod.lift prod.fst (prod.snd ≫ prod.snd))
    (Fin.cases
      (prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
        (prod.lift prod.fst (prod.snd ≫ imp)))
      (fun i => Fin.elim0 i)))
  conclusion := Fin.cases
    (coprod.desc (prod.map (𝟙 E) logical) (axioms ≫ prod.map (𝟙 E) sentence))
    (Fin.cases (prod.map (𝟙 E) all)
      (Fin.cases (prod.map (𝟙 E) prod.snd) (fun i => Fin.elim0 i)))

variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ E ⨯ S)
  (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

theorem unary_parameter :
    (rules E logical sentence axioms all imp).premises 1 ≫ prod.fst =
      (rules E logical sentence axioms all imp).conclusion 1 ≫ prod.fst := by
  change prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ prod.fst =
    prod.map (𝟙 E) all ≫ prod.fst
  simp

theorem binary_first_parameter :
    (rules E logical sentence axioms all imp).premises 2 ≫ prod.fst ≫ prod.fst =
      (rules E logical sentence axioms all imp).conclusion 2 ≫ prod.fst := by
  change prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.lift prod.fst (prod.snd ≫ imp)) ≫ prod.fst ≫ prod.fst =
      prod.map (𝟙 E) prod.snd ≫ prod.fst
  simp

theorem binary_second_parameter :
    (rules E logical sentence axioms all imp).premises 2 ≫ prod.snd ≫ prod.fst =
      (rules E logical sentence axioms all imp).conclusion 2 ≫ prod.fst := by
  change prod.lift (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.lift prod.fst (prod.snd ≫ imp)) ≫ prod.snd ≫ prod.fst =
      prod.map (𝟙 E) prod.snd ≫ prod.fst
  simp

theorem nullary_logical_conclusion :
    coprod.inl ≫ (rules E logical sentence axioms all imp).conclusion 0 =
      prod.map (𝟙 E) logical := by
  simp [rules]

theorem nullary_axiom_conclusion :
    coprod.inr ≫ (rules E logical sentence axioms all imp).conclusion 0 =
      axioms ≫ prod.map (𝟙 E) sentence := by
  simp [rules]

end Signature

section Total
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (E : TotalSplit T) {V F L S A : TotalSplit T}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ E ⨯ S)
  (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

def algebra : Endofunctor.Algebra (rules E logical sentence axioms all imp).inference :=
  SyntacticDerivation.totalDerivationAlgebra T (rules E logical sentence axioms all imp)

/-- The full family's universal property is constructed from arbitrary-rule
initiality, with no initiality premise on the family signature. -/
def initial : IsInitial (algebra T E logical sentence axioms all imp) :=
  SyntacticDerivation.totalDerivationInitial T (rules E logical sentence axioms all imp)

def conclusion : (algebra T E logical sentence axioms all imp).a.left ⟶ E ⨯ F :=
  (algebra T E logical sentence axioms all imp).a.hom

def sentenceProof : TotalSplit T :=
  pullback (conclusion T E logical sentence axioms all imp) (prod.map (𝟙 E) sentence)

def sentenceConclusion : sentenceProof T E logical sentence axioms all imp ⟶ E ⨯ S :=
  pullback.snd (conclusion T E logical sentence axioms all imp) (prod.map (𝟙 E) sentence)

def formulaTheory : Subobject (E ⨯ F) :=
  imageSubobject (conclusion T E logical sentence axioms all imp)

def sentenceTheory : Subobject (E ⨯ S) :=
  imageSubobject (sentenceConclusion T E logical sentence axioms all imp)

theorem sentenceTheory_pullback :
    sentenceTheory T E logical sentence axioms all imp =
      (Subobject.pullback (prod.map (𝟙 E) sentence)).obj
        (formulaTheory T E logical sentence axioms all imp) :=
  sentenceImage_subobject (conclusion T E logical sentence axioms all imp)
    (prod.map (𝟙 E) sentence)

theorem formulaTheory_least :
    ClosedUnder (rules E logical sentence axioms all imp).inference
        (image.ι (conclusion T E logical sentence axioms all imp)) ∧
      ∀ {U : TotalSplit T} (m : U ⟶ E ⨯ F) [Mono m],
        ClosedUnder (rules E logical sentence axioms all imp).inference m →
          ∃ w : image (conclusion T E logical sentence axioms all imp) ⟶ U,
            w ≫ m = image.ι (conclusion T E logical sentence axioms all imp) :=
  (rules E logical sentence axioms all imp).least_theorem_subobject
    (algebra T E logical sentence axioms all imp)
    (initial T E logical sentence axioms all imp)

end Total
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedRules
