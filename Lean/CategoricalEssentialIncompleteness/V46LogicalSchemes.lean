/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution
public import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # The seven named-variable first-order logical axiom schemes -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

/-- `φ ⇒ (ψ ⇒ φ)`. -/
def hilbertOne : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 :=
  prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ S.implicationConstructor) ≫
    S.implicationConstructor

/-- `(φ ⇒ (ψ ⇒ χ)) ⇒ ((φ ⇒ ψ) ⇒ (φ ⇒ χ))`. -/
def hilbertTwo : (S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 :=
  prod.lift
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ S.implicationConstructor) ≫
        S.implicationConstructor)
    (prod.lift (prod.fst ≫ S.implicationConstructor)
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ S.implicationConstructor) ≫
        S.implicationConstructor) ≫ S.implicationConstructor

/-- `(¬ψ ⇒ ¬φ) ⇒ (φ ⇒ ψ)`. -/
def hilbertThree : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2 :=
  prod.lift
    (prod.lift (prod.snd ≫ S.negationConstructor) (prod.fst ≫ S.negationConstructor) ≫
      S.implicationConstructor)
    S.implicationConstructor ≫ S.implicationConstructor

/-- Coordinates `(x,φ,t)` are permuted into the source of formula substitution. -/
def instantiationInput : V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.1) ⟶
    S.algebra.a.2 ⨯ S.substitutionParameters :=
  prod.lift (prod.snd ≫ prod.fst) (prod.lift prod.fst (prod.snd ≫ prod.snd))

def instantiationParameters : D :=
  pullback S.instantiationInput S.admissibleInclusion

def instantiationInclusion : S.instantiationParameters ⟶
    V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.1) := pullback.fst _ _

instance instantiationInclusion_mono : Mono S.instantiationInclusion := by
  dsimp [instantiationInclusion, instantiationParameters]
  infer_instance

def instantiationAdmissible : S.instantiationParameters ⟶ S.admissibleSubstitution :=
  pullback.snd _ _

theorem instantiation_admissible :
    S.instantiationInclusion ≫ S.instantiationInput =
      S.instantiationAdmissible ≫ S.admissibleInclusion := pullback.condition

/-- `(∀x φ) ⇒ φ[x:=t]`, with its admissibility parameter object. -/
def hilbertInstantiation : S.instantiationParameters ⟶ S.algebra.a.2 :=
  prod.lift
    (prod.lift (S.instantiationInclusion ≫ prod.fst)
      (S.instantiationInclusion ≫ prod.snd ≫ prod.fst) ≫ S.quantifierConstructor)
    (S.instantiationAdmissible ≫ S.formulaSubstitution) ≫ S.implicationConstructor

def distributionAbsence : V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.2) ⟶ Two D :=
  prod.lift prod.fst (prod.snd ≫ prod.fst ≫ S.formulaOccurrences) ≫
    S.lists.membership S.decidableVariables

def distributionParameters : D := Two.Fiber S.distributionAbsence false

def distributionInclusion : S.distributionParameters ⟶
    V ⨯ (S.algebra.a.2 ⨯ S.algebra.a.2) := Two.fiberι _ _

instance distributionInclusion_mono : Mono S.distributionInclusion := by
  dsimp [distributionInclusion]
  infer_instance

theorem distribution_absence :
    S.distributionInclusion ≫ S.distributionAbsence =
      Two.constant S.distributionParameters false := Two.fiberι_comp _ _

/-- `∀x(φ⇒ψ) ⇒ (φ⇒∀x ψ)`, on the fiber where `x` is absent from `φ`. -/
def hilbertDistribution : S.distributionParameters ⟶ S.algebra.a.2 :=
  S.distributionInclusion ≫ prod.lift
    (prod.lift prod.fst (prod.snd ≫ S.implicationConstructor) ≫ S.quantifierConstructor)
    (prod.lift (prod.snd ≫ prod.fst)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ S.quantifierConstructor) ≫
        S.implicationConstructor) ≫ S.implicationConstructor

/-- Equality reflexivity, with an arbitrary term as parameter. -/
def hilbertReflexivity : S.algebra.a.1 ⟶ S.algebra.a.2 :=
  prod.lift (𝟙 _) (𝟙 _) ≫ S.equalityConstructor

def equalitySchemeBase : D := (V ⨯ S.algebra.a.2) ⨯ (S.algebra.a.1 ⨯ S.algebra.a.1)

def equalityFirstInput : S.equalitySchemeBase ⟶ S.algebra.a.2 ⨯ S.substitutionParameters :=
  prod.lift (prod.fst ≫ prod.snd)
    (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.fst))

def equalitySecondInput : S.equalitySchemeBase ⟶ S.algebra.a.2 ⨯ S.substitutionParameters :=
  prod.lift (prod.fst ≫ prod.snd)
    (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.snd))

/-- Intersection of the two success pullbacks on the shared coordinates `(x,φ,u,t)`. -/
def equalitySchemeParameters : D :=
  pullback (pullback.fst S.equalityFirstInput S.admissibleInclusion)
    (pullback.fst S.equalitySecondInput S.admissibleInclusion)

def equalitySchemeInclusion : S.equalitySchemeParameters ⟶ S.equalitySchemeBase :=
  pullback.fst _ _ ≫ pullback.fst S.equalityFirstInput S.admissibleInclusion

instance equalitySchemeInclusion_mono : Mono S.equalitySchemeInclusion := by
  dsimp [equalitySchemeInclusion]
  infer_instance

def equalityFirstAdmissible : S.equalitySchemeParameters ⟶ S.admissibleSubstitution :=
  pullback.fst _ _ ≫ pullback.snd S.equalityFirstInput S.admissibleInclusion

def equalitySecondAdmissible : S.equalitySchemeParameters ⟶ S.admissibleSubstitution :=
  pullback.snd _ _ ≫ pullback.snd S.equalitySecondInput S.admissibleInclusion

theorem equality_first_admissible :
    S.equalitySchemeInclusion ≫ S.equalityFirstInput =
      S.equalityFirstAdmissible ≫ S.admissibleInclusion := by
  dsimp only [equalitySchemeInclusion, equalityFirstAdmissible, equalitySchemeParameters]
  calc
    _ = pullback.fst _ _ ≫
        (pullback.fst S.equalityFirstInput S.admissibleInclusion ≫ S.equalityFirstInput) :=
      Category.assoc _ _ _
    _ = pullback.fst _ _ ≫
        (pullback.snd S.equalityFirstInput S.admissibleInclusion ≫ S.admissibleInclusion) :=
      congrArg (fun k => pullback.fst _ _ ≫ k) pullback.condition
    _ = _ := (Category.assoc _ _ _).symm

theorem equality_second_admissible :
    S.equalitySchemeInclusion ≫ S.equalitySecondInput =
      S.equalitySecondAdmissible ≫ S.admissibleInclusion := by
  dsimp only [equalitySchemeInclusion, equalitySecondAdmissible, equalitySchemeParameters]
  calc
    _ = (pullback.snd _ _ ≫
        pullback.fst S.equalitySecondInput S.admissibleInclusion) ≫ S.equalitySecondInput :=
      congrArg (fun k => k ≫ S.equalitySecondInput) pullback.condition
    _ = pullback.snd _ _ ≫
        (pullback.fst S.equalitySecondInput S.admissibleInclusion ≫ S.equalitySecondInput) :=
      Category.assoc _ _ _
    _ = pullback.snd _ _ ≫
        (pullback.snd S.equalitySecondInput S.admissibleInclusion ≫ S.admissibleInclusion) :=
      congrArg (fun k => pullback.snd _ _ ≫ k) pullback.condition
    _ = _ := (Category.assoc _ _ _).symm

/-- `(u=t) ⇒ (φ[x:=u] ⇒ φ[x:=t])`, with both substitutions admissible. -/
def hilbertEquality : S.equalitySchemeParameters ⟶ S.algebra.a.2 :=
  prod.lift (S.equalitySchemeInclusion ≫ prod.snd ≫ S.equalityConstructor)
    (prod.lift (S.equalityFirstAdmissible ≫ S.formulaSubstitution)
      (S.equalitySecondAdmissible ≫ S.formulaSubstitution) ≫ S.implicationConstructor) ≫
        S.implicationConstructor

/-- The finite coproduct of the seven scheme parameter objects. -/
def logicalParameters : D :=
  ((((((S.algebra.a.2 ⨯ S.algebra.a.2) ⨿
    ((S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2)) ⨿
      (S.algebra.a.2 ⨯ S.algebra.a.2)) ⨿ S.instantiationParameters) ⨿
        S.distributionParameters) ⨿ S.algebra.a.1) ⨿ S.equalitySchemeParameters

def logicalAxioms : S.logicalParameters ⟶ S.algebra.a.2 :=
  coprod.desc (coprod.desc (coprod.desc (coprod.desc
    (coprod.desc (coprod.desc S.hilbertOne S.hilbertTwo) S.hilbertThree)
      S.hilbertInstantiation) S.hilbertDistribution) S.hilbertReflexivity) S.hilbertEquality

/-- The Appendix A.6 presentation, now with its logical scheme map constructed. -/
def logicalRules {A : D} (axioms : A ⟶ S.sentenceObject) :
    RulePresentation S.algebra.a.2 2 :=
  firstOrderRules S.logicalAxioms S.sentenceInclusion axioms
    S.quantifierConstructor S.implicationConstructor

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
