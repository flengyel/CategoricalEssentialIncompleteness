/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationCoordinates


/-! # The fork formula, axiom and rule objects -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation
open EffectiveFork (Total)

example (X Y : Total) : codedProduct X Y = ⟨EffectiveFork.product X.obj Y.obj⟩ := rfl
example (X Y : Total) : X ⨯ Y ≅ codedProduct X Y := productComparison X Y
example (X Y : Total) : (productComparison X Y).hom ≫ codedFst X Y = prod.fst :=
  productComparison_fst X Y
example (X Y : Total) : (productComparison X Y).hom ≫ codedSnd X Y = prod.snd :=
  productComparison_snd X Y
example (X Y : Total) : (productComparison X Y).inv ≫ prod.fst = codedFst X Y :=
  productComparison_inv_fst X Y
example (X Y : Total) : (productComparison X Y).inv ≫ prod.snd = codedSnd X Y :=
  productComparison_inv_snd X Y
example (X Y : Total) : (productComparison X Y).hom =
    codedPair (prod.fst : X ⨯ Y ⟶ X) prod.snd := productComparison_hom X Y
example (X Y : Total) : (productComparison X Y).inv =
    prod.lift (codedFst X Y) (codedSnd X Y) := productComparison_inv X Y
example {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ (productComparison X Y).hom = codedPair f g := productComparison_pair f g

example : sentenceObject.obj = ForkSyntax.S := rfl
example : variableObject.obj = EffectiveFork.V := rfl
example : atom.hom = ForkSyntax.theta := rfl
example : negation.hom = ForkSyntax.nu := rfl
example : implication = (productComparison sentenceObject sentenceObject).hom ≫
    ⟨ForkSyntax.implication,ForkSyntax.implication_total⟩ := rfl
example : H1 = prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ implication) ≫ implication := rfl
example : H2 = prod.lift
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ implication) ≫ implication)
    (prod.lift
      (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) ≫ implication)
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ implication) ≫ implication) ≫ implication := rfl
example : H3 = prod.lift
    (prod.lift (prod.snd ≫ negation) (prod.fst ≫ negation) ≫ implication)
    (prod.lift prod.fst prod.snd ≫ implication) ≫ implication := rfl

example (a b : Idem EffectiveFork.V) : axiomCoefficients a b =
    ![sentenceObject ⨯ sentenceObject,(sentenceObject ⨯ sentenceObject) ⨯ sentenceObject,
      sentenceObject ⨯ sentenceObject,axiomDomain a,axiomDomain b] := rfl
example (a b : Idem EffectiveFork.V) : Sigma.ι (axiomCoefficients a b) 0 ≫ lambda a b = H1 :=
  lambda_logical1 a b
example (a b : Idem EffectiveFork.V) : Sigma.ι (axiomCoefficients a b) 1 ≫ lambda a b = H2 :=
  lambda_logical2 a b
example (a b : Idem EffectiveFork.V) : Sigma.ι (axiomCoefficients a b) 2 ≫ lambda a b = H3 :=
  lambda_logical3 a b
example (a b : Idem EffectiveFork.V) : Sigma.ι (axiomCoefficients a b) 3 ≫ lambda a b =
    axiomInclusion a ≫ atom := lambda_positive a b
example (a b : Idem EffectiveFork.V) : Sigma.ι (axiomCoefficients a b) 4 ≫ lambda a b =
    axiomInclusion b ≫ atom ≫ negation := lambda_negative a b

example (a b : Idem EffectiveFork.V) : (rules a b).instances 0 = axiomObject a b := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).instances 1 = ⊥_ Total := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).instances 2 = (sentenceObject ⨯ sentenceObject) := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).premises 2 = prod.lift prod.fst implication := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).conclusion 0 = lambda a b := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).conclusion 2 = prod.snd := rfl
example (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) :
    ((printedH a b).obj Q).left = (axiomObject a b ⨿
      pullback (prod.lift prod.fst implication) (prod.map Q.hom Q.hom)) := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).inference ≅ printedH a b := inferenceIso a b

example (a b : Idem EffectiveFork.V) : (proofObject a b).obj = ForkSyntax.Prf a b := rfl
example (a b : Idem EffectiveFork.V) : (conclusion a b).hom = ForkSyntax.conclusion a b := rfl
end CategoricalEssentialIncompleteness.V46.ForkDerivation
