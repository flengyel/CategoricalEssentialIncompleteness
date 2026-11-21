/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes
public import CategoricalEssentialIncompleteness.V46SyntacticParityComparison
public import CategoricalEssentialIncompleteness.V46SyntacticPredicates
public import CategoricalEssentialIncompleteness.V46PrintedObjectCodingModels
public import CategoricalEssentialIncompleteness.V46SyntacticComparison

/-! # The diagonal source morphism and its two restriction domains -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes

/-- The universal program receives the exponential product code, via the constructed
object isomorphism. -/
def sourceTau :
    PCategoryStruct.nearProd (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) ⟶ omegaObject 𝗣𝗔 :=
  (PrintedObjectCoding.omegaProductIso 𝗣𝗔).hom ≫
    arrowOfIndex 𝗣𝗔 .omega .omega UniformTrace.universalIndex

def sourceDiagonal : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  PCategoryStruct.diag (omegaObject 𝗣𝗔) ≫ sourceTau

def diagonalArrow : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  arrowOfIndex 𝗣𝗔 .omega .omega diagonalIndex

def sourceParityDiagonal :
    omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) :=
  PCategoryStruct.diag (omegaObject 𝗣𝗔) ≫ sourceTau ≫ (omegaCoprodIso 𝗣𝗔).inv

theorem sourceParityDiagonal_eq :
    sourceParityDiagonal = sourceDiagonal ≫ (omegaCoprodIso 𝗣𝗔).inv :=
  (Category.assoc _ _ _).symm

def a0 : Idem (omegaObject 𝗣𝗔) :=
  diagonal0 sourceTau (omegaCoprodIso 𝗣𝗔).symm

def a1 : Idem (omegaObject 𝗣𝗔) :=
  diagonal1 sourceTau (omegaCoprodIso 𝗣𝗔).symm

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Relate numerical graphs to the interpreted morphism before instantiating any large
closed program expression. -/
theorem mem_model_relation {Q R : CodedProgramCategory 𝗣𝗔} (f : Q ⟶ R)
    (x : SyntacticModel.interpretedType M (objectCode Q))
    (y : SyntacticModel.interpretedType M (objectCode R)) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map f x ↔
      SyntacticModel.programRelation 𝗣𝗔 M f.val
        (SyntacticModel.codingEquiv 𝗣𝗔 M (objectCode Q) x).val
        (SyntacticModel.codingEquiv 𝗣𝗔 M (objectCode R) y).val :=
  (SyntacticModel.mem_model 𝗣𝗔 M f x y).trans (SyntacticModel.mem_arrow 𝗣𝗔 M f _ _)

theorem universal_arrow_relation (input output : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      (arrowOfIndex 𝗣𝗔 .omega .omega UniformTrace.universalIndex).val input output ↔
      UniformTrace.graph.val.Evalb ![(UniformTrace.universalIndex : M),input,output] := by
  rw [arrowOfIndex_val,SyntacticModel.programRelation_class,eventualGraph_normalizeIndex_eval]
  simp only [CodedObjectMembership.memberFormula_omega_eval,true_and,and_true]
  have h := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) UniformTrace.universalIndex input output
  simp only [numeral_eq_natCast_app] at h
  exact h.symm

/-- The categorical source map is the program u in the manuscript's exponential input
coordinates. -/
theorem sourceTau_relation (a b y : M) :
    SyntacticModel.programRelation 𝗣𝗔 M sourceTau.val (pair a b) y ↔
      UniformTrace.graph.val.Evalb ![a,b,y] := by
  rw [sourceTau,comp_val,SyntacticModel.programRelation_mul]
  constructor
  · rintro ⟨z,hz,hy⟩
    rw [PrintedObjectCoding.omegaProduct_value,PrintedObjectCoding.encodeProgram_model] at hz
    obtain ⟨c,d,he,hz⟩ := hz
    obtain ⟨hc,hd⟩ := (CodedObjectMembership.pair_eq_pair_iff _ _ _ _).mp he
    subst c
    subst d
    subst z
    exact (UniformTrace.universal_eval a b y).mp ((universal_arrow_relation M _ _).mp hy)
  · intro hy
    refine ⟨ExponentialPairing.code a b,?_,?_⟩
    · rw [PrintedObjectCoding.omegaProduct_value,PrintedObjectCoding.encodeProgram_model]
      exact ⟨a,b,rfl,rfl⟩
    · exact (universal_arrow_relation M _ _).mpr ((UniformTrace.universal_eval a b y).mpr hy)

theorem mem_sourceTau (a b y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceTau (a,b) ↔
      UniformTrace.graph.val.Evalb ![a,b,y] := by
  rw [mem_model_relation]
  exact sourceTau_relation M a b y

theorem mem_source_diagonal (x : M) (p : M × M) :
    p ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map
      (PCategoryStruct.diag (omegaObject 𝗣𝗔)) x ↔ p = (x,x) := by
  change p ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map
    (arrowOfIndex 𝗣𝗔 .omega (.product .omega .omega)
      TypedNearProduct.diagonalIndex) x ↔ _
  rw [SyntacticModel.mem_model_index,TypedNearProduct.eventualGraph_diagonalIndex_eval]
  change pair p.1 p.2 = pair x x ↔ p = (x,x)
  rw [CodedObjectMembership.pair_eq_pair_iff]
  exact ⟨fun h => Prod.ext h.1 h.2,fun h =>
    ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

theorem mem_sourceDiagonal (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceDiagonal x ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] := by
  rw [sourceDiagonal,(SyntacticModel.modelFunctor 𝗣𝗔 M).map_comp,mem_comp,
    diagonal_graph]
  constructor
  · rintro ⟨p,hp,hy⟩
    have he := (mem_source_diagonal M x p).mp hp
    subst p
    exact (mem_sourceTau M x x y).mp hy
  · intro hy
    exact ⟨(x,x),(mem_source_diagonal M x (x,x)).mpr rfl,
      (mem_sourceTau M x x y).mpr hy⟩

theorem mem_diagonalArrow (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map diagonalArrow x ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] := by
  rw [diagonalArrow,SyntacticModel.mem_model_index]
  have hs := canonicalPartrecGraphFormula_eval_iff_eventualGraph
    (M := M) diagonalIndex x y
  simp only [numeral_eq_natCast_app] at hs
  exact hs.symm

theorem mem_sourceParityDiagonal_inl (x m : M) :
    Sum.inl m ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceParityDiagonal x ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m] := by
  rw [sourceParityDiagonal_eq,(SyntacticModel.modelFunctor 𝗣𝗔 M).map_comp,mem_comp]
  change (∃ y : M,
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceDiagonal x ∧
    Sum.inl m ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).inv y) ↔ _
  simp only [mem_sourceDiagonal,PartialSearchLift.mem_parity_decode_inl]
  exact ⟨fun ⟨_,hy,he⟩ => he ▸ hy,fun h => ⟨_,h,rfl⟩⟩

theorem mem_sourceParityDiagonal_inr (x m : M) :
    Sum.inr m ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceParityDiagonal x ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m + 1] := by
  rw [sourceParityDiagonal_eq,(SyntacticModel.modelFunctor 𝗣𝗔 M).map_comp,mem_comp]
  change (∃ y : M,
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceDiagonal x ∧
    Sum.inr m ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).inv y) ↔ _
  simp only [mem_sourceDiagonal,PartialSearchLift.mem_parity_decode_inr]
  exact ⟨fun ⟨_,hy,he⟩ => he ▸ hy,fun h => ⟨_,h,rfl⟩⟩

theorem model_summand0 :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (summand0 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)) =
        summand0 (PartialFun.of M) (PartialFun.of M) := by
  let F := SyntacticModel.modelRangeFunctor 𝗣𝗔 M
  have hc : (F.comparison (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom = 𝟙 _ :=
    SyntacticModel.model_comparison_eq_id 𝗣𝗔 M _ _
  have h := F.comparison_sum (𝟙 (omegaObject 𝗣𝗔))
    (0 : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔)
  simp only [hc,Category.id_comp,Category.comp_id,F.toFunctor.map_id,F.map_zero] at h
  exact Idem.ext h

theorem model_summand1 :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      (summand1 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)) =
        summand1 (PartialFun.of M) (PartialFun.of M) := by
  let F := SyntacticModel.modelRangeFunctor 𝗣𝗔 M
  have hc : (F.comparison (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)).hom = 𝟙 _ :=
    SyntacticModel.model_comparison_eq_id 𝗣𝗔 M _ _
  have h := F.comparison_sum (0 : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔)
    (𝟙 (omegaObject 𝗣𝗔))
  simp only [hc,Category.id_comp,Category.comp_id,F.toFunctor.map_id,F.map_zero] at h
  exact Idem.ext h

/-- The first restriction is the partial identity on the alpha truth set, including its
nonstandard members. -/
theorem model_a0 :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      a0 = setIdem {x : M | alpha.val.Evalb ![x]} := by
  change (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
    (Idem.pull sourceParityDiagonal (summand0 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔))) = _
  rw [RangeFunctor.map_pull,model_summand0]
  change Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceParityDiagonal)
    (summand0 (PartialFun.of M) (PartialFun.of M)) = setIdem {x : M | alpha.val.Evalb ![x]}
  apply support_injective
  ext x
  rw [support_pull,support_setIdem]
  change (∃ z : M ⊕ M,
    z ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceParityDiagonal x ∧
    z ∈ support (summand0 (PartialFun.of M) (PartialFun.of M))) ↔ alpha.val.Evalb (M := M) ![x]
  rw [alpha_eval]
  simp only [PartialSearchLift.mem_support_summand0]
  constructor
  · rintro ⟨_,hz,m,rfl⟩
    exact ⟨m,(mem_sourceParityDiagonal_inl M x m).mp hz⟩
  · rintro ⟨m,hm⟩
    exact ⟨Sum.inl m,(mem_sourceParityDiagonal_inl M x m).mpr hm,m,rfl⟩

theorem model_a1 :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
      a1 = setIdem {x : M | beta.val.Evalb ![x]} := by
  change (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
    (Idem.pull sourceParityDiagonal (summand1 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔))) = _
  rw [RangeFunctor.map_pull,model_summand1]
  change Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceParityDiagonal)
    (summand1 (PartialFun.of M) (PartialFun.of M)) = setIdem {x : M | beta.val.Evalb ![x]}
  apply support_injective
  ext x
  rw [support_pull,support_setIdem]
  change (∃ z : M ⊕ M,
    z ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map sourceParityDiagonal x ∧
    z ∈ support (summand1 (PartialFun.of M) (PartialFun.of M))) ↔ beta.val.Evalb (M := M) ![x]
  rw [beta_eval]
  simp only [PartialSearchLift.mem_support_summand1]
  constructor
  · rintro ⟨_,hz,m,rfl⟩
    exact ⟨m,(mem_sourceParityDiagonal_inr M x m).mp hz⟩
  · rintro ⟨m,hm⟩
    exact ⟨Sum.inr m,(mem_sourceParityDiagonal_inr M x m).mpr hm,m,rfl⟩

end Models

/-- Equality holds in the uniform source category, rather than only after the standard
interpretation. -/
theorem diagonalIndex_represents : diagonalArrow = sourceDiagonal := by
  apply CodedHom.ext
  apply SyntacticPredicates.programClass_ext 𝗣𝗔
  intro M _ _ x y
  have h := (mem_diagonalArrow M x y).trans (mem_sourceDiagonal M x y).symm
  rw [mem_model_relation,mem_model_relation] at h
  exact h

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes
