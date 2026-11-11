/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFamily
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedAxioms
public import CategoricalEssentialIncompleteness.V46NamedGammaEvidenceSoundness

/-! # A uniform provability formula from the constructed family conclusion -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
open NamedArithmeticSignature

/-- The predicate presentation of the actual family sentence-proof object.
Its graph coordinates are transported through the proved equivalence. -/
def proofCarrier (AxPA : Carrier) : PredicateCategory 𝗣𝗔 :=
  (predicateEquivalence 𝗣𝗔).inverse.obj (ArithmeticIndexedFamily.sentenceProof AxPA)

def rawConclusion (AxPA : Carrier) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (proofCarrier AxPA)
      ArithmeticIndexedAxioms.productPredicate :=
  (predicateEquivalence 𝗣𝗔).inverse.map
      (ArithmeticIndexedFamily.sentenceConclusion AxPA ≫ ArithmeticIndexedAxioms.productIso.inv) ≫
    (predicateEquivalence 𝗣𝗔).unitIso.inv.app ArithmeticIndexedAxioms.productPredicate

/-- Joint image coordinates are established for an opaque graph first. -/
def jointImage (C : Graph) : 𝚺₁.Semisentence 2 :=
  .mkSigma “e z. ∃ p w, !natPairFormula.val w e z ∧ !C.val p w”

/-- This is an existential image of the actual conclusion graph. The
parameter remains an input; no per-theory proof object or index is chosen. -/
def provability (AxPA : Carrier) : 𝚺₁.Semisentence 2 :=
  jointImage (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).graph

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem jointImage_eval (C : Graph) (e z : M) :
    (jointImage C).val.Evalb ![e,z] ↔
      (imageCarrier C).val.Evalb ![⟪e,z⟫] := by
  simp [jointImage,imageCarrier]

@[simp] theorem provability_image (AxPA : Carrier) (e z : M) :
    (provability AxPA).val.Evalb ![e,z] ↔
      (imageCarrier (chosenGraph 𝗣𝗔 (rawConclusion AxPA)).graph).val.Evalb ![⟪e,z⟫] :=
  jointImage_eval M _ e z

/-- Uniform membership is witnessed by a point of the constructed family
proof presentation, for arbitrary internal parameters and sentence words. -/
theorem provability_eval (AxPA : Carrier) (e z : M) :
    (provability AxPA).val.Evalb ![e,z] ↔
      ∃ p : Obj 𝗣𝗔 M (proofCarrier AxPA),
        ((F 𝗣𝗔 M).map (rawConclusion AxPA) p).val = ⟪e,z⟫ :=
  (provability_image M AxPA e z).trans
    (SyntacticGeneratedAxioms.imageCarrier_points 𝗣𝗔 M (rawConclusion AxPA) ⟪e,z⟫)

end Models
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability
