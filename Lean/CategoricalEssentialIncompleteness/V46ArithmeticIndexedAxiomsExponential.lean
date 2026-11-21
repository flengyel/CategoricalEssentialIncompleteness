/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityExponential

/-! # The indexed axiom coefficient in the exponential product chart -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxioms.Exponential
open NamedArithmeticSignature

/-- Membership and computation witnesses remain existential; the label
is precisely the exponential code of the parameter and sentence word. -/
def printedCarrier (AxPA : Carrier) : Carrier :=
  let E := ExponentialPairing.graph
  let A := ArithmeticIndexedAxioms.axiomGraph AxPA
  .mkSigma “w. ∃ e z, !E.val w e z ∧ !A.val e z”

def encodeGraph (AxPA : Carrier) : Graph :=
  let A := ArithmeticIndexedAxioms.carrier AxPA
  let E := ExponentialProducts.encodeGraph variableSymbols ArithmeticIndexedAxioms.sentencePredicate
  .mkSigma “source target. !A.val source ∧ !E.val source target”

def decodeGraph (AxPA : Carrier) : Graph :=
  let A := printedCarrier AxPA
  let D := ExponentialProducts.decodeGraph variableSymbols ArithmeticIndexedAxioms.sentencePredicate
  .mkSigma “source target. !A.val source ∧ !D.val source target”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem rawCarrier_data (AxPA : Carrier) (w : M) :
    (ArithmeticIndexedAxioms.carrier AxPA).val.Evalb ![w] ↔
      ∃ e z : M, w = Arithmetic.pair e z ∧
        (ArithmeticIndexedAxioms.axiomGraph AxPA).val.Evalb ![e,z] := by
  simp [ArithmeticIndexedAxioms.carrier]

@[simp] theorem printedCarrier_eval (AxPA : Carrier) (w : M) :
    (printedCarrier AxPA).val.Evalb ![w] ↔
      ∃ e z : M, w = ExponentialPairing.code e z ∧
        (ArithmeticIndexedAxioms.axiomGraph AxPA).val.Evalb ![e,z] := by
  simp [printedCarrier]

theorem printedCarrier_code (AxPA : Carrier) (e z : M) :
    (printedCarrier AxPA).val.Evalb ![ExponentialPairing.code e z] ↔
      (ArithmeticIndexedAxioms.axiomGraph AxPA).val.Evalb ![e,z] := by
  rw [printedCarrier_eval]
  constructor
  · rintro ⟨a,b,he,ha⟩
    obtain ⟨rfl,rfl⟩ := ExponentialPairing.code_injective he
    exact ha
  · intro h
    exact ⟨e,z,rfl,h⟩

theorem printedCarrier_numeral (AxPA : Carrier) (e : ℕ) (z : M) :
    (printedCarrier AxPA).val.Evalb ![ExponentialPairing.code (e : M) z] ↔
      (ArithmeticIndexedAxioms.fiberAxioms AxPA e).val.Evalb ![z] :=
  (printedCarrier_code M AxPA (e : M) z).trans
    ((ArithmeticIndexedAxioms.axiomGraph_eval M AxPA (e : M) z).trans
      (ArithmeticIndexedAxioms.fiberAxioms_eval M AxPA e z).symm)

@[simp] theorem encodeGraph_eval (AxPA : Carrier) (source target : M) :
    (encodeGraph AxPA).val.Evalb ![source,target] ↔
      (ArithmeticIndexedAxioms.carrier AxPA).val.Evalb ![source] ∧
        (ExponentialProducts.encodeGraph variableSymbols ArithmeticIndexedAxioms.sentencePredicate).val.Evalb
          ![source,target] := by
  simp [encodeGraph]

@[simp] theorem decodeGraph_eval (AxPA : Carrier) (source target : M) :
    (decodeGraph AxPA).val.Evalb ![source,target] ↔
      (printedCarrier AxPA).val.Evalb ![source] ∧
        (ExponentialProducts.decodeGraph variableSymbols ArithmeticIndexedAxioms.sentencePredicate).val.Evalb
          ![source,target] := by
  simp [decodeGraph]

theorem encodeGraph_pair (AxPA : Carrier) (e z target : M) :
    (encodeGraph AxPA).val.Evalb ![Arithmetic.pair e z,target] ↔
      (ArithmeticIndexedAxioms.axiomGraph AxPA).val.Evalb ![e,z] ∧
        target = ExponentialPairing.code e z := by
  rw [encodeGraph_eval,ArithmeticIndexedAxioms.carrier_pair,ExponentialProducts.encodeGraph_pair]
  constructor
  · intro h
    exact ⟨h.1,h.2.2.2⟩
  · rintro ⟨ha,he⟩
    exact ⟨ha,NamedArithmeticSignature.variables_eval e,
      ((ArithmeticIndexedAxioms.axiomGraph_eval M AxPA e z).mp ha).1,he⟩

theorem decodeGraph_code (AxPA : Carrier) (e z target : M) :
    (decodeGraph AxPA).val.Evalb ![ExponentialPairing.code e z,target] ↔
      (ArithmeticIndexedAxioms.axiomGraph AxPA).val.Evalb ![e,z] ∧
        target = Arithmetic.pair e z := by
  rw [decodeGraph_eval,printedCarrier_code]
  constructor
  · rintro ⟨ha,hd⟩
    obtain ⟨a,b,he,ht,_,_⟩ := (ExponentialProducts.decodeGraph_eval variableSymbols
      ArithmeticIndexedAxioms.sentencePredicate (ExponentialPairing.code e z) target).mp hd
    obtain ⟨rfl,rfl⟩ := ExponentialPairing.code_injective he
    exact ⟨ha,ht⟩
  · rintro ⟨ha,ht⟩
    exact ⟨ha,(ExponentialProducts.decodeGraph_eval variableSymbols
      ArithmeticIndexedAxioms.sentencePredicate _ _).mpr ⟨e,z,rfl,ht,
        NamedArithmeticSignature.variables_eval e,
        ((ArithmeticIndexedAxioms.axiomGraph_eval M AxPA e z).mp ha).1⟩⟩

end Models

def encode (AxPA : Carrier) :
    GraphMorphism 𝗣𝗔 (ArithmeticIndexedAxioms.carrier AxPA) (printedCarrier AxPA) where
  graph := encodeGraph AxPA
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro source target h
    have hs := ((encodeGraph_eval M AxPA source target).mp h).1
    obtain ⟨e,z,rfl,ha⟩ := (rawCarrier_data M AxPA source).mp hs
    have ht := ((encodeGraph_pair M AxPA e z target).mp h).2
    exact ⟨hs,(printedCarrier_eval M AxPA target).mpr ⟨e,z,ht,ha⟩⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,totalSentence_eval]
    intro source hs
    obtain ⟨e,z,rfl,ha⟩ := (rawCarrier_data M AxPA source).mp hs
    refine ⟨ExponentialPairing.code e z,(encodeGraph_pair M AxPA e z _).mpr ⟨ha,rfl⟩,?_⟩
    intro target ht
    exact ((encodeGraph_pair M AxPA e z target).mp ht).2

def decode (AxPA : Carrier) :
    GraphMorphism 𝗣𝗔 (printedCarrier AxPA) (ArithmeticIndexedAxioms.carrier AxPA) where
  graph := decodeGraph AxPA
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro source target h
    have hs := ((decodeGraph_eval M AxPA source target).mp h).1
    obtain ⟨e,z,rfl,ha⟩ := (printedCarrier_eval M AxPA source).mp hs
    have ht := ((decodeGraph_code M AxPA e z target).mp h).2
    exact ⟨hs,(rawCarrier_data M AxPA target).mpr ⟨e,z,ht,ha⟩⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,totalSentence_eval]
    intro source hs
    obtain ⟨e,z,rfl,ha⟩ := (printedCarrier_eval M AxPA source).mp hs
    refine ⟨Arithmetic.pair e z,(decodeGraph_code M AxPA e z _).mpr ⟨ha,rfl⟩,?_⟩
    intro target ht
    exact ((decodeGraph_code M AxPA e z target).mp ht).2

/-- The original coefficient labels and the exponential coefficient labels are related
by the proved code translations, with the same parameter and sentence. -/
def carrierIso (AxPA : Carrier) : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (ArithmeticIndexedAxioms.carrier AxPA) (printedCarrier AxPA) where
  hom := representedArrow 𝗣𝗔 (encode AxPA)
  inv := representedArrow 𝗣𝗔 (decode AxPA)
  hom_inv_id := by
    apply hom_ext 𝗣𝗔
    intro M _ _ source target
    simp only [relation_comp,relation_class,relation_id]
    change (∃ mid : M, (encodeGraph AxPA).val.Evalb ![source,mid] ∧
      (decodeGraph AxPA).val.Evalb ![mid,target]) ↔
        (ArithmeticIndexedAxioms.carrier AxPA).val.Evalb ![source] ∧ target = source
    constructor
    · rintro ⟨mid,he,hd⟩
      have hs := ((encodeGraph_eval M AxPA source mid).mp he).1
      obtain ⟨e,z,rfl,ha⟩ := (rawCarrier_data M AxPA source).mp hs
      have hm := ((encodeGraph_pair M AxPA e z mid).mp he).2
      subst mid
      exact ⟨hs,((decodeGraph_code M AxPA e z target).mp hd).2⟩
    · rintro ⟨hs,htarget⟩
      subst target
      obtain ⟨e,z,rfl,ha⟩ := (rawCarrier_data M AxPA source).mp hs
      exact ⟨ExponentialPairing.code e z,(encodeGraph_pair M AxPA e z _).mpr ⟨ha,rfl⟩,
        (decodeGraph_code M AxPA e z _).mpr ⟨ha,rfl⟩⟩
  inv_hom_id := by
    apply hom_ext 𝗣𝗔
    intro M _ _ source target
    simp only [relation_comp,relation_class,relation_id]
    change (∃ mid : M, (decodeGraph AxPA).val.Evalb ![source,mid] ∧
      (encodeGraph AxPA).val.Evalb ![mid,target]) ↔
        (printedCarrier AxPA).val.Evalb ![source] ∧ target = source
    constructor
    · rintro ⟨mid,hd,he⟩
      have hs := ((decodeGraph_eval M AxPA source mid).mp hd).1
      obtain ⟨e,z,rfl,ha⟩ := (printedCarrier_eval M AxPA source).mp hs
      have hm := ((decodeGraph_code M AxPA e z mid).mp hd).2
      subst mid
      exact ⟨hs,((encodeGraph_pair M AxPA e z target).mp he).2⟩
    · rintro ⟨hs,htarget⟩
      subst target
      obtain ⟨e,z,rfl,ha⟩ := (printedCarrier_eval M AxPA source).mp hs
      exact ⟨Arithmetic.pair e z,(decodeGraph_code M AxPA e z _).mpr ⟨ha,rfl⟩,
        (encodeGraph_pair M AxPA e z _).mpr ⟨ha,rfl⟩⟩

theorem inclusionProof (AxPA : Carrier) :
    𝗣𝗔 ⊢ inclusionSentence (printedCarrier AxPA) ArithmeticIndexedProvability.printedProductPredicate := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro w hw
  obtain ⟨e,z,he,ha⟩ := (printedCarrier_eval M AxPA w).mp hw
  exact (ExponentialProducts.carrier_eval variableSymbols ArithmeticIndexedAxioms.sentencePredicate w).mpr
    ⟨e,z,he,NamedArithmeticSignature.variables_eval e,
      ((ArithmeticIndexedAxioms.axiomGraph_eval M AxPA e z).mp ha).1⟩

def printedInclusion (AxPA : Carrier) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (printedCarrier AxPA)
      ArithmeticIndexedProvability.printedProductPredicate :=
  representedArrow 𝗣𝗔 (GraphMorphism.inclusion (inclusionProof AxPA))

instance printedInclusion_mono (AxPA : Carrier) : Mono (printedInclusion AxPA) := by
  unfold printedInclusion
  infer_instance

private theorem encoded_inclusion (AxPA : Carrier) :
    representedArrow 𝗣𝗔 (encode AxPA) ≫
      representedArrow 𝗣𝗔 (GraphMorphism.inclusion (inclusionProof AxPA)) =
    representedArrow 𝗣𝗔 (GraphMorphism.inclusion (ArithmeticIndexedAxioms.inclusionProof AxPA)) ≫
      representedArrow 𝗣𝗔 (ExponentialProducts.encode 𝗣𝗔 variableSymbols
        ArithmeticIndexedAxioms.sentencePredicate) := by
  apply hom_ext 𝗣𝗔
  intro M _ _ source target
  simp only [relation_comp,relation_class]
  change (∃ mid : M, (encodeGraph AxPA).val.Evalb ![source,mid] ∧
      (GraphMorphism.identityGraph (printedCarrier AxPA)).val.Evalb ![mid,target]) ↔
    (∃ mid : M, (GraphMorphism.identityGraph (ArithmeticIndexedAxioms.carrier AxPA)).val.Evalb
      ![source,mid] ∧
      (ExponentialProducts.encodeGraph variableSymbols ArithmeticIndexedAxioms.sentencePredicate).val.Evalb
        ![mid,target])
  constructor
  · rintro ⟨mid,he,hi⟩
    obtain ⟨_,htarget⟩ := (GraphMorphism.identityGraph_eval (printedCarrier AxPA) mid target).mp hi
    subst target
    have hp := (encodeGraph_eval M AxPA source mid).mp he
    exact ⟨source,(GraphMorphism.identityGraph_eval _ source source).mpr ⟨hp.1,rfl⟩,hp.2⟩
  · rintro ⟨mid,hi,he⟩
    obtain ⟨ha,hmid⟩ := (GraphMorphism.identityGraph_eval (ArithmeticIndexedAxioms.carrier AxPA) source mid).mp hi
    subst mid
    have hp := (encodeGraph_eval M AxPA source target).mpr ⟨ha,he⟩
    exact ⟨target,hp,(GraphMorphism.identityGraph_eval _ target target).mpr
      ⟨((encode AxPA).support_model M source target hp).2,rfl⟩⟩

/-- The subobject square commutes in the PA-provable graph category. -/
theorem mono_square (AxPA : Carrier) :
    (carrierIso AxPA).hom ≫ printedInclusion AxPA =
      ArithmeticIndexedAxioms.predicateInclusion AxPA ≫
        (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate).hom :=
  encoded_inclusion AxPA

def printedObject (AxPA : Carrier) : TotalSplit 𝗣𝗔 :=
  (realization 𝗣𝗔).obj (printedCarrier AxPA)

def printedAxioms (AxPA : Carrier) :
    printedObject AxPA ⟶ ArithmeticIndexedAxioms.parameter ⨯ ArithmeticIndexedAxioms.sentence :=
  (realization 𝗣𝗔).map (printedInclusion AxPA) ≫ ArithmeticIndexedProvability.printedProductIso.hom

instance printedAxioms_mono (AxPA : Carrier) : Mono (printedAxioms AxPA) := by
  unfold printedAxioms
  infer_instance

private theorem product_chart :
    (realization 𝗣𝗔).map (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
      ArithmeticIndexedAxioms.sentencePredicate).hom ≫
        ArithmeticIndexedProvability.printedProductIso.hom = ArithmeticIndexedAxioms.productIso.hom := by
  simpa only [ArithmeticIndexedProvability.printedProductIso,Iso.trans_hom,Iso.symm_hom,
    Functor.mapIso_hom] using
    (Iso.hom_inv_id_assoc ((realization 𝗣𝗔).mapIso
      (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate))
      ArithmeticIndexedAxioms.productIso.hom)

/-- The same coefficient morphism over E×Sent is obtained in the chart. This is the
nullary-rule coefficient comparison for the family. -/
theorem realized_square (AxPA : Carrier) :
    (realization 𝗣𝗔).map (carrierIso AxPA).hom ≫ printedAxioms AxPA =
      ArithmeticIndexedAxioms.axioms AxPA := by
  calc
    _ = (realization 𝗣𝗔).map ((carrierIso AxPA).hom ≫ printedInclusion AxPA) ≫
        ArithmeticIndexedProvability.printedProductIso.hom := by
      dsimp only [printedAxioms]
      rw [Functor.map_comp,Category.assoc]
    _ = (realization 𝗣𝗔).map (ArithmeticIndexedAxioms.predicateInclusion AxPA ≫
        (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
          ArithmeticIndexedAxioms.sentencePredicate).hom) ≫
          ArithmeticIndexedProvability.printedProductIso.hom :=
      congrArg (fun f => (realization 𝗣𝗔).map f ≫ ArithmeticIndexedProvability.printedProductIso.hom)
        (mono_square AxPA)
    _ = (realization 𝗣𝗔).map (ArithmeticIndexedAxioms.predicateInclusion AxPA) ≫
        ((realization 𝗣𝗔).map (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols
          ArithmeticIndexedAxioms.sentencePredicate).hom ≫
            ArithmeticIndexedProvability.printedProductIso.hom) := by
      rw [Functor.map_comp,Category.assoc]
    _ = (realization 𝗣𝗔).map (ArithmeticIndexedAxioms.predicateInclusion AxPA) ≫
        ArithmeticIndexedAxioms.productIso.hom :=
      congrArg (fun f => (realization 𝗣𝗔).map (ArithmeticIndexedAxioms.predicateInclusion AxPA) ≫ f)
        product_chart
    _ = _ := rfl

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedAxioms.Exponential
