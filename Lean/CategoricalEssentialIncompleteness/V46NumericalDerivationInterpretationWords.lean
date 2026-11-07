/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationRules
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationParser
import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial
import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport

/-! # Original PA ordinary-tree words and literal numerical tree words

Both directions use the identical word number. The stored-word parser
check is retained on the PA side and compared by the proved conservation
law; coefficient labels are the actual unary arithmetic images.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation

def labelMap (C : PredicateCategory 𝗣𝗔) : PredicateCategory 𝗧𝗔 := NumericalSyntaxTreeChart.E.inverse.obj (K.obj C)

theorem labelMap_eval (C : Carrier) (n : ℕ) :
    (labelMap C).val.Evalb (M := ℕ) ![n] ↔ C.val.Evalb (M := ℕ) ![n] :=
  coefficient_labels C n

/-- Predicate-coordinate identity is constructed with opaque predicates;
its support proof is supplied by the explicitly stated equivalence. -/
def carrierIdentityIso (C : PredicateCategory 𝗣𝗔) (D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb (M := ℕ) ![n] ↔ D.val.Evalb (M := ℕ) ![n]) :
    K.obj C ≅ NumericalCoordinates.predicateObject D where
  hom :=
    { toFun := fun x => ⟨x.val,(h x.val).mp x.property⟩
      represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩ }
  inv :=
    { toFun := fun x => ⟨x.val,(h x.val).mpr x.property⟩
      represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩ }
  hom_inv_id := by
    apply NumericalTuples.Map.ext
    funext x
    rfl
  inv_hom_id := by
    apply NumericalTuples.Map.ext
    funext x
    rfl

/-- A source stored word and its literal coded-coefficient plain word
have the identical scalar code, for both recursive sorts. -/
def rawWordIso (b : Bool) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    K.obj (Postfix.carrier b p q) ≅ NumericalCoordinates.predicateObject
      (Postfix.plainCarrier b (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)) :=
  carrierIdentityIso _ _ (Parser.storedCarrier_map_plain labelMap labelMap_eval b p q)

/-- An entire represented-word coordinate equation is proved while the
source and target predicate objects remain arbitrary. -/
def CarrierScalarIdentity (C : PredicateCategory 𝗣𝗔) (D : PredicateCategory 𝗧𝗔)
    (j : K.obj C ≅ NumericalSyntaxTreeChart.E.functor.obj D) : Prop :=
  ∀ x : NumericalTuples.Point (K.obj C),
    ((NumericalSyntaxTreeChart.wordPresentationIso D).hom.toFun (j.hom.toFun x)).val = x.val

def realizeCarrierIdentityIso (C : PredicateCategory 𝗣𝗔) (D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb (M := ℕ) ![n] ↔ D.val.Evalb (M := ℕ) ![n]) :
    K.obj C ≅ NumericalSyntaxTreeChart.E.functor.obj D :=
  carrierIdentityIso C D h ≪≫ (NumericalSyntaxTreeChart.wordPresentationIso D).symm

theorem realizeCarrierIdentityIso_value (C : PredicateCategory 𝗣𝗔) (D : PredicateCategory 𝗧𝗔)
    (h : ∀ n : ℕ, C.val.Evalb (M := ℕ) ![n] ↔ D.val.Evalb (M := ℕ) ![n]) :
    CarrierScalarIdentity C D (realizeCarrierIdentityIso C D h) := by
  intro x
  have he : (realizeCarrierIdentityIso C D h).hom ≫
      (NumericalSyntaxTreeChart.wordPresentationIso D).hom = (carrierIdentityIso C D h).hom := by
    simp only [realizeCarrierIdentityIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
      Iso.inv_hom_id,Category.comp_id]
  exact congrArg (fun f => (f.toFun x).val) he

/-- The target is the actual literal equivalence image of the plain word
predicate; its chosen object is compared through the proved word chart. -/
def realizedWordIso (b : Bool) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    K.obj (Postfix.carrier b p q) ≅ NumericalSyntaxTreeChart.E.functor.obj
      (Postfix.plainCarrier b (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)) :=
  realizeCarrierIdentityIso _ _ (Parser.storedCarrier_map_plain labelMap labelMap_eval b p q)

abbrev realizedWordIso_value (b : Bool) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :=
  realizeCarrierIdentityIso_value _ _ (Parser.storedCarrier_map_plain labelMap labelMap_eval b p q)

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
