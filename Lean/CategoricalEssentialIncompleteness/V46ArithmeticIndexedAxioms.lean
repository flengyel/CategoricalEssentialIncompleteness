/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticLiteralModel
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedRules
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import CategoricalEssentialIncompleteness.V46UniformTrace

/-! # The Σ₁ indexed axiom subobject of E × Sent

AxPA is the chosen Σ₁ sentence-axiom predicate in the manuscript. The
construction and its categorical universal properties do not require a
soundness or initiality assumption on this coefficient predicate.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxioms
open NamedArithmeticSignature

abbrev sentencePredicate : PredicateCategory 𝗣𝗔 := NamedArithmeticLiteralTotal.literalPredicate
abbrev parameter : TotalSplit 𝗣𝗔 := ArithmeticOmegaComparison.identityOmega 𝗣𝗔
abbrev sentence : TotalSplit 𝗣𝗔 := NamedArithmeticLiteralTotal.literalSentence

def axiomGraph (AxPA : Carrier) : 𝚺₁.Semisentence 2 :=
  let Sent := sentencePredicate
  let G := UniformTrace.graph
  .mkSigma “e z. !Sent.val z ∧ (!AxPA.val z ∨ ∃ y, !G.val e z y)”

def fiberAxioms (AxPA : Carrier) (e : ℕ) : Carrier :=
  let Ax := axiomGraph AxPA
  .mkSigma “z. !Ax.val !!(e) z”

/-- The sole label is the pair word. Sentence and computation witnesses
are existential; they are not added to the encoded syntax. -/
def carrier (AxPA : Carrier) : Carrier :=
  let Ax := axiomGraph AxPA
  .mkSigma “w. ∃ e z, !natPairFormula.val w e z ∧ !Ax.val e z”

abbrev productPredicate : PredicateCategory 𝗣𝗔 := productCarrier variableSymbols sentencePredicate

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem axiomGraph_eval (AxPA : Carrier) (e z : M) :
    (axiomGraph AxPA).val.Evalb ![e,z] ↔
      sentencePredicate.val.Evalb ![z] ∧
        (AxPA.val.Evalb ![z] ∨ ∃ y : M, UniformTrace.graph.val.Evalb ![e,z,y]) := by
  simp [axiomGraph]

@[simp] theorem fiberAxioms_eval (AxPA : Carrier) (e : ℕ) (z : M) :
    (fiberAxioms AxPA e).val.Evalb ![z] ↔
      sentencePredicate.val.Evalb ![z] ∧
        (AxPA.val.Evalb ![z] ∨ ∃ y : M, UniformTrace.graph.val.Evalb ![(e : M),z,y]) := by
  simp [fiberAxioms,numeral_eq_natCast_app]

@[simp] theorem carrier_eval (AxPA : Carrier) (w : M) :
    (carrier AxPA).val.Evalb ![w] ↔
      ∃ e z : M, w = ⟪e,z⟫ ∧ sentencePredicate.val.Evalb ![z] ∧
        (AxPA.val.Evalb ![z] ∨ ∃ y : M, UniformTrace.graph.val.Evalb ![e,z,y]) := by
  simp [carrier]

theorem carrier_pair (AxPA : Carrier) (e z : M) :
    (carrier AxPA).val.Evalb ![⟪e,z⟫] ↔ (axiomGraph AxPA).val.Evalb ![e,z] := by
  rw [carrier_eval,axiomGraph_eval]
  constructor
  · rintro ⟨e',z',he,hs,hΓ⟩
    obtain ⟨rfl,rfl⟩ := (pair_eq_pair_iff e z e' z').mp he
    exact ⟨hs,hΓ⟩
  · rintro ⟨hs,hΓ⟩
    exact ⟨e,z,rfl,hs,hΓ⟩

theorem carrier_numeral (AxPA : Carrier) (e : ℕ) (z : M) :
    (carrier AxPA).val.Evalb ![⟪(e : M),z⟫] ↔
      (fiberAxioms AxPA e).val.Evalb ![z] :=
  (carrier_pair M AxPA (e : M) z).trans
    ((axiomGraph_eval M AxPA (e : M) z).trans (fiberAxioms_eval M AxPA e z).symm)

end Models

theorem inclusionProof (AxPA : Carrier) :
    𝗣𝗔 ⊢ inclusionSentence (carrier AxPA) productPredicate := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro w hw
  obtain ⟨e,z,he,hs,_⟩ := (carrier_eval M AxPA w).mp hw
  exact (productCarrier_eval variableSymbols sentencePredicate w).mpr
    ⟨e,z,he,NamedArithmeticSignature.variables_eval e,hs⟩

def predicateInclusion (AxPA : Carrier) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (carrier AxPA) productPredicate :=
  representedArrow 𝗣𝗔 (GraphMorphism.inclusion (inclusionProof AxPA))

instance predicateInclusion_mono (AxPA : Carrier) : Mono (predicateInclusion AxPA) := by
  unfold predicateInclusion
  infer_instance

def rawProductIso : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    productPredicate (variableSymbols ⨯ sentencePredicate) where
  hom := SyntacticLists.fromRawProduct 𝗣𝗔 variableSymbols sentencePredicate
  inv := SyntacticLists.toRawProduct 𝗣𝗔 variableSymbols sentencePredicate
  hom_inv_id := SyntacticLists.fromRaw_toRaw 𝗣𝗔 variableSymbols sentencePredicate
  inv_hom_id := SyntacticLists.toRaw_fromRaw 𝗣𝗔 variableSymbols sentencePredicate

/-- This is the proved v : J(D) ≅ E × S of the indexed axiom construction, including the
identity-Ω comparison rather than a carrier change. -/
def productIso : (realization 𝗣𝗔).obj productPredicate ≅ parameter ⨯ sentence :=
  (realization 𝗣𝗔).mapIso rawProductIso ≪≫
    asIso (prodComparison (realization 𝗣𝗔) variableSymbols sentencePredicate) ≪≫
      prod.mapIso (ArithmeticOmegaComparison.omegaIso 𝗣𝗔).symm (Iso.refl _)

def axiomObject (AxPA : Carrier) : TotalSplit 𝗣𝗔 := (realization 𝗣𝗔).obj (carrier AxPA)

def axioms (AxPA : Carrier) : axiomObject AxPA ⟶ parameter ⨯ sentence :=
  (realization 𝗣𝗔).map (predicateInclusion AxPA) ≫ productIso.hom

instance axioms_mono (AxPA : Carrier) : Mono (axioms AxPA) := by
  unfold axioms
  infer_instance

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxioms
