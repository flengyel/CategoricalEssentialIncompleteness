/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersNumeralsPredicate
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionPullbacks

/-! # The actual numeral pullback of the indexed axiom predicate

The square is first proved for the literal pair presentation in every PA
model. Its labels remain formula words and parameter/formula pairs.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
open NamedArithmeticSignature

def predicateTerminalFrom (B : PredicateCategory 𝗣𝗔) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance B terminalCarrier :=
  (SyntacticPredicates.terminalIsTerminal 𝗣𝗔).from B


/-- The constant numeral is paired with the original input word. -/
def rawNumeralGraph (B : Carrier) (e : ℕ) : 𝚺₁.Semisentence 2 :=
  .mkSigma “x w. !B.val x ∧ !natPairFormula.val w !!(e) x”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
@[simp] theorem rawNumeralGraph_eval (B : Carrier) (e : ℕ) (x w : M) :
    (rawNumeralGraph B e).val.Evalb ![x,w] ↔ B.val.Evalb ![x] ∧ w = ⟪(e : M),x⟫ := by
  simp [rawNumeralGraph,numeral_eq_natCast_app]
end Models

def rawNumeralRepresentation (B : Carrier) (e : ℕ) :
    GraphMorphism 𝗣𝗔 B (productCarrier variableSymbols B) where
  graph := rawNumeralGraph B e
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro x w h
    obtain ⟨hx,rfl⟩ := (rawNumeralGraph_eval M B e x w).mp h
    exact ⟨hx,(productCarrier_eval variableSymbols B _).mpr
      ⟨(e : M),x,rfl,variables_eval _,hx⟩⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,totalSentence_eval]
    intro x hx
    refine ⟨⟪(e : M),x⟫,(rawNumeralGraph_eval M B e x _).mpr ⟨hx,rfl⟩,?_⟩
    intro y hy
    exact ((rawNumeralGraph_eval M B e x y).mp hy).2

def rawNumeralPair (B : PredicateCategory 𝗣𝗔) (e : ℕ) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance B (productCarrier variableSymbols B) :=
  representedArrow 𝗣𝗔 (rawNumeralRepresentation B e)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
@[simp] theorem rawNumeralPair_value (B : PredicateCategory 𝗣𝗔) (e : ℕ)
    (x : Obj 𝗣𝗔 M B) :
    ((F 𝗣𝗔 M).map (rawNumeralPair B e) x).val = ⟪(e : M),x.val⟫ :=
  ((rawNumeralGraph_eval M B e x.val _).mp
    (PredicateInterpretation.value_graph 𝗣𝗔 M (rawNumeralRepresentation B e) x)).2

/-- The raw graph agrees with the already proved product coding. -/
theorem rawNumeralPair_point (B : PredicateCategory 𝗣𝗔) (e : ℕ)
    (x : Obj 𝗣𝗔 M B) :
    (F 𝗣𝗔 M).map (rawNumeralPair B e) x =
      PredicateInterpretation.productCoding 𝗣𝗔 M variableSymbols B
        (⟨(e : M),variables_eval _⟩,x) := by
  exact Subtype.ext (rawNumeralPair_value M B e x)
end Models

/-- Fiber membership already includes sentencehood; it is not an extra
label or assumption in the numeral fiber. -/
theorem fiberSentenceProof (AxPA : Carrier) (e : ℕ) :
    𝗣𝗔 ⊢ inclusionSentence (ArithmeticIndexedAxioms.fiberAxioms AxPA e)
      ArithmeticIndexedAxioms.sentencePredicate := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro z hz
  exact ((ArithmeticIndexedAxioms.fiberAxioms_eval M AxPA e z).mp hz).1

def fiberSentencePredicate (AxPA : Carrier) (e : ℕ) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (ArithmeticIndexedAxioms.fiberAxioms AxPA e) ArithmeticIndexedAxioms.sentencePredicate :=
  representedArrow 𝗣𝗔 (GraphMorphism.inclusion (fiberSentenceProof AxPA e))

instance fiberSentencePredicate_mono (AxPA : Carrier) (e : ℕ) :
    Mono (fiberSentencePredicate AxPA e) := by
  unfold fiberSentencePredicate
  infer_instance

def fiberToFamilyRepresentation (AxPA : Carrier) (e : ℕ) : GraphMorphism 𝗣𝗔
    (ArithmeticIndexedAxioms.fiberAxioms AxPA e) (ArithmeticIndexedAxioms.carrier AxPA) where
  graph := rawNumeralGraph (ArithmeticIndexedAxioms.fiberAxioms AxPA e) e
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro x w h
    obtain ⟨hx,rfl⟩ := (rawNumeralGraph_eval M (ArithmeticIndexedAxioms.fiberAxioms AxPA e) e x w).mp h
    exact ⟨hx,(ArithmeticIndexedAxioms.carrier_numeral M AxPA e x).mpr hx⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,totalSentence_eval]
    intro x hx
    refine ⟨⟪(e : M),x⟫,(rawNumeralGraph_eval M (ArithmeticIndexedAxioms.fiberAxioms AxPA e) e x _).mpr ⟨hx,rfl⟩,?_⟩
    intro y hy
    exact ((rawNumeralGraph_eval M (ArithmeticIndexedAxioms.fiberAxioms AxPA e) e x y).mp hy).2

def fiberToFamilyPredicate (AxPA : Carrier) (e : ℕ) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (ArithmeticIndexedAxioms.fiberAxioms AxPA e) (ArithmeticIndexedAxioms.carrier AxPA) :=
  representedArrow 𝗣𝗔 (fiberToFamilyRepresentation AxPA e)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
@[simp] theorem fiberToFamily_value (AxPA : Carrier) (e : ℕ)
    (x : Obj 𝗣𝗔 M (ArithmeticIndexedAxioms.fiberAxioms AxPA e)) :
    ((F 𝗣𝗔 M).map (fiberToFamilyPredicate AxPA e) x).val = ⟪(e : M),x.val⟫ :=
  ((rawNumeralGraph_eval M (ArithmeticIndexedAxioms.fiberAxioms AxPA e) e x.val _).mp
    (PredicateInterpretation.value_graph 𝗣𝗔 M (fiberToFamilyRepresentation AxPA e) x)).2
@[simp] theorem fiberSentence_value (AxPA : Carrier) (e : ℕ)
    (x : Obj 𝗣𝗔 M (ArithmeticIndexedAxioms.fiberAxioms AxPA e)) :
    ((F 𝗣𝗔 M).map (fiberSentencePredicate AxPA e) x).val = x.val :=
  PredicateInterpretation.map_inclusion_val 𝗣𝗔 M (fiberSentenceProof AxPA e) x
@[simp] theorem familyInclusion_value (AxPA : Carrier)
    (x : Obj 𝗣𝗔 M (ArithmeticIndexedAxioms.carrier AxPA)) :
    ((F 𝗣𝗔 M).map (ArithmeticIndexedAxioms.predicateInclusion AxPA) x).val = x.val :=
  PredicateInterpretation.map_inclusion_val 𝗣𝗔 M (ArithmeticIndexedAxioms.inclusionProof AxPA) x
end Models

@[reassoc] theorem predicateAxiom_square (AxPA : Carrier) (e : ℕ) :
    fiberToFamilyPredicate AxPA e ≫ ArithmeticIndexedAxioms.predicateInclusion AxPA =
      fiberSentencePredicate AxPA e ≫ rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e := by
  apply PredicateInterpretation.jointly_faithful 𝗣𝗔
  intro M _ _
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  simp only [Functor.map_comp_apply,familyInclusion_value,fiberToFamily_value,
    rawNumeralPair_value,fiberSentence_value]

/-- The square is cartesian universally in PA, including nonstandard
formula words and witnesses for the indexed enumeration. -/
theorem predicateAxiom_pullback (AxPA : Carrier) (e : ℕ) :
    IsPullback (fiberToFamilyPredicate AxPA e) (fiberSentencePredicate AxPA e)
      (ArithmeticIndexedAxioms.predicateInclusion AxPA)
      (rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e) := by
  apply SyntacticDerivation.OptionPullbacks.predicate_of_models 𝗣𝗔
    (predicateAxiom_square AxPA e)
  intro M _ _
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_,?_,?_⟩
  · simpa only [Functor.map_comp] using congrArg (F 𝗣𝗔 M).map (predicateAxiom_square AxPA e)
  · intro x y h
    apply Subtype.ext
    exact (fiberSentence_value M AxPA e x).symm.trans
      ((congrArg Subtype.val h.2).trans (fiberSentence_value M AxPA e y))
  · intro a z h
    have hv : a.val = ⟪(e : M),z.val⟫ := by
      simpa only [familyInclusion_value,rawNumeralPair_value] using congrArg Subtype.val h
    have hz : (ArithmeticIndexedAxioms.fiberAxioms AxPA e).val.Evalb ![z.val] :=
      (ArithmeticIndexedAxioms.carrier_numeral M AxPA e z.val).mp (hv ▸ a.property)
    let x : Obj 𝗣𝗔 M (ArithmeticIndexedAxioms.fiberAxioms AxPA e) := ⟨z.val,hz⟩
    refine ⟨x,Subtype.ext ?_,Subtype.ext ?_⟩
    · exact (fiberToFamily_value M AxPA e x).trans hv.symm
    · exact fiberSentence_value M AxPA e x

/-- The named product comparison retains exactly the constant numeral
and the original word, before transport to the total splitting. -/
@[reassoc] theorem rawNumeralPair_product (B : PredicateCategory 𝗣𝗔) (e : ℕ) :
    rawNumeralPair B e ≫ fromRawProduct 𝗣𝗔 variableSymbols B =
      prod.lift (predicateTerminalFrom B ≫ numeralPredicate e) (𝟙 B) := by
  apply prod.hom_ext
  · apply PredicateInterpretation.jointly_faithful 𝗣𝗔
    intro M _ _
    apply ConcreteCategory.hom_ext
    intro x
    have hp : (F 𝗣𝗔 M).map (rawNumeralPair B e ≫
        fromRawProduct 𝗣𝗔 variableSymbols B) x =
        pairPoint 𝗣𝗔 M ⟨(e : M),variables_eval _⟩ x := by
      simp only [Functor.map_comp_apply,rawNumeralPair_point,pairPoint]
    have hp' : (F 𝗣𝗔 M).map (fromRawProduct 𝗣𝗔 variableSymbols B)
        ((F 𝗣𝗔 M).map (rawNumeralPair B e) x) =
        pairPoint 𝗣𝗔 M ⟨(e : M),variables_eval _⟩ x := by
      simpa only [Functor.map_comp_apply] using hp
    simp only [Functor.map_comp_apply,prod.lift_fst]
    rw [hp',pairPoint_fst]
    apply Subtype.ext
    exact ((numeralGraph_eval M e _ _).mp
      (PredicateInterpretation.value_graph 𝗣𝗔 M (numeralRepresentation e)
        ((F 𝗣𝗔 M).map (predicateTerminalFrom B) x))).2.symm
  · apply PredicateInterpretation.jointly_faithful 𝗣𝗔
    intro M _ _
    apply ConcreteCategory.hom_ext
    intro x
    simp only [Functor.map_comp_apply,prod.lift_snd,Functor.map_id_apply]
    rw [rawNumeralPair_point]
    exact pairPoint_snd 𝗣𝗔 M ⟨(e : M),variables_eval _⟩ x

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
