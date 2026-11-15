/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RuleRelabelling
public import CategoricalEssentialIncompleteness.V46SignedDerivationLeafCodes
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial
public import CategoricalEssentialIncompleteness.V46FirstOrderTheory

/-! # Literal signed rule labels and the canonical first-order calculus -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def sumIso (A B : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T) (PredicateInterpretation.sumCarrier A B)
      (Limits.coprod (C := PredicateCategory T) A B) := by
  let e := IsColimit.coconePointUniqueUpToIso (coprodIsCoprod A B)
    (PredicateInterpretation.sumIsColimit T A B)
  exact e.symm

def axiomIso (L A B : PredicateCategory T) :
    CategoryTheory.Iso (C := PredicateCategory T) (axiomCarrier L A B)
      (Limits.coprod (C := PredicateCategory T) L (Limits.coprod (C := PredicateCategory T) A B)) :=
  sumIso T L (PredicateInterpretation.sumCarrier A B) ≪≫
    coprod.mapIso (Iso.refl L) (sumIso T A B)

variable {L A B V S F : PredicateCategory T}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⨿ B ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
local notation "R" => firstOrderRules logical sentence axioms all imp

def labelObjects : Fin 3 → PredicateCategory T :=
  ![axiomCarrier L A B, Limits.prod (C := PredicateCategory T) V F,
    Limits.prod (C := PredicateCategory T) F F]

def labelIso : ∀ i : Fin 3, labelObjects (T := T) (L := L) (A := A) (B := B)
    (V := V) (F := F) i ≅ (R).instances i := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · exact axiomIso T L A B
  · exact Iso.refl _
  · exact Iso.refl _

def literalRules : RulePresentation F 2 :=
  RuleRelabelling.rules R (labelObjects (T := T) (L := L) (A := A) (B := B) (V := V) (F := F))
    (labelIso T logical sentence axioms all imp)

theorem literal_rule_polynomial :
    SyntaxPolynomial.constructors (SyntacticDerivation.PolynomialComparison.coefficients
        (D := PredicateCategory T) (literalRules T logical sentence axioms all imp)) 2 =
      rulePolynomial L A B (Limits.prod (C := PredicateCategory T) V F)
        (Limits.prod (C := PredicateCategory T) F F) := by
  simp [SyntaxPolynomial.constructors, SyntacticDerivation.PolynomialComparison.coefficients,
    literalRules, RuleRelabelling.rules, labelObjects, rulePolynomial, ruleCoefficients]

theorem literal_conclusion_image :
    imageSubobject (SyntacticDerivation.derivationAlgebra T
        (literalRules T logical sentence axioms all imp)).a.hom =
      imageSubobject (SyntacticDerivation.derivationAlgebra T R).a.hom :=
  RuleRelabelling.conclusion_image_eq R _ (labelIso T logical sentence axioms all imp)
    (SyntacticDerivation.derivationAlgebra T (literalRules T logical sentence axioms all imp))
    (SyntacticDerivation.derivationInitial T (literalRules T logical sentence axioms all imp))
    (SyntacticDerivation.derivationAlgebra T R) (SyntacticDerivation.derivationInitial T R)

theorem literal_sentence_image :
    imageSubobject (pullback.snd (SyntacticDerivation.derivationAlgebra T
        (literalRules T logical sentence axioms all imp)).a.hom sentence) =
      imageSubobject (pullback.snd (SyntacticDerivation.derivationAlgebra T R).a.hom sentence) :=
  RuleRelabelling.sentence_image_eq R _ (labelIso T logical sentence axioms all imp) sentence
    (SyntacticDerivation.derivationAlgebra T (literalRules T logical sentence axioms all imp))
    (SyntacticDerivation.derivationInitial T (literalRules T logical sentence axioms all imp))
    (SyntacticDerivation.derivationAlgebra T R) (SyntacticDerivation.derivationInitial T R)

end CategoricalEssentialIncompleteness.V46.SignedDerivation
