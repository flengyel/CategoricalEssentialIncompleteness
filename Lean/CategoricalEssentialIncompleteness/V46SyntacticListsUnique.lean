/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticListsFold

/-! # Uniqueness of the actual categorical fold -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {P V : PredicateCategory T} (B : ListAlgebra (D := Over P) (constantFamily P V))
variable (m : constantFamily P (listObject T V) ⟶ B.carrier)

def candidateMorphism : GraphMorphism T (productCarrier P (listObject T V)) B.carrier.left :=
  chosenGraph T (fromRawProduct T P (listObject T V) ≫ m.left)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem candidate_eval (p : Obj T M P) (a : Obj T M (listObject T V))
    (y : Obj T M B.carrier.left) :
    (SyntacticListEvaluation.SliceAlgebra.unpackedGraph (candidateMorphism T B m).graph).val.Evalb
      ![p.val, a.val, y.val] ↔
        (F T M).map m.left (pairPoint T M p a) = y := by
  rw [SyntacticListEvaluation.SliceAlgebra.unpackedGraph_eval]
  change (chosenGraph T (fromRawProduct T P (listObject T V) ≫ m.left)).graph.val.Evalb
    ![(PredicateInterpretation.productCoding T M P (listObject T V) (p, a)).val, y.val] ↔ _
  rw [chosenGraph_map_iff]
  rw [Functor.map_comp]
  rfl

/-- The canonical nil point over an arbitrary parameter is obtained by
interpreting the actual terminal object of the slice. -/
theorem parameter_nil_point (p : Obj T M P) :
    (F T M).map ((algebra T V).withParameters P).nil.left
      ((F T M).map (terminalOverIso T P).inv p) =
        pairPoint T M p ⟨0, listCarrier_nil V⟩ := by
  let t := (F T M).map (terminalOverIso T P).inv p
  have hi : (F T M).map (⊤_ (Over P)).hom t = p := by
    have h := congrArg (F T M).map (terminalOverIso T P).inv_hom_id
    rw [terminalOverIso_hom, Functor.map_comp, (F T M).map_id P] at h
    exact ConcreteCategory.congr_hom h p
  apply modelProduct_ext T M
  · exact (parameter_nil_fst T (P := P) (V := V) M t).trans
      (hi.trans (pairPoint_fst T M p ⟨0, listCarrier_nil V⟩).symm)
  · apply Subtype.ext
    exact (parameter_nil_snd T (P := P) (V := V) M t).trans
      (congrArg Subtype.val (pairPoint_snd T M p
        (⟨0, listCarrier_nil V⟩ : Obj T M (listObject T V)))).symm

theorem candidate_nil_typed
    (hn : ((algebra T V).withParameters P).nil ≫ m = B.nil)
    (p : Obj T M P) (y : Obj T M B.carrier.left) :
    (SyntacticListEvaluation.SliceAlgebra.unpackedGraph (candidateMorphism T B m).graph).val.Evalb
      ![p.val, 0, y.val] ↔ (decode T B).nilOp.graph.val.Evalb ![p.val, y.val] := by
  change (SyntacticListEvaluation.SliceAlgebra.unpackedGraph
    (candidateMorphism T B m).graph).val.Evalb ![p.val, 0, y.val] ↔
      (chosenGraph T (nilMap T B)).graph.val.Evalb ![p.val, y.val]
  rw [candidate_eval T B m M p ⟨0, listCarrier_nil V⟩ y,
    chosenGraph_map_iff T M (nilMap T B) p y]
  have he : (F T M).map m.left (pairPoint T M p ⟨0, listCarrier_nil V⟩) =
      (F T M).map (nilMap T B) p := by
    rw [← parameter_nil_point T M p]
    have hm := congrArg (F T M).map (congrArg Over.Hom.left hn)
    change (F T M).map (((algebra T V).withParameters P).nil.left ≫ m.left) =
      (F T M).map B.nil.left at hm
    rw [Functor.map_comp] at hm
    have hh := ConcreteCategory.congr_hom hm ((F T M).map (terminalOverIso T P).inv p)
    have hnmap : (F T M).map (nilMap T B) p = (F T M).map B.nil.left
        ((F T M).map (terminalOverIso T P).inv p) := by
      change (F T M).map ((terminalOverIso T P).inv ≫ B.nil.left) p = _
      rw [Functor.map_comp]
      rfl
    exact hh.trans hnmap.symm
  rw [he]

theorem candidate_cons_typed
    (hc : ((algebra T V).withParameters P).cons ≫ m =
      prod.map (𝟙 (constantFamily P V)) m ≫ B.cons)
    (p : Obj T M P) (v : Obj T M V) (a : Obj T M (listObject T V))
    (y : Obj T M B.carrier.left) :
    (SyntacticListEvaluation.SliceAlgebra.unpackedGraph (candidateMorphism T B m).graph).val.Evalb
      ![p.val, adjoin v.val a.val, y.val] ↔
      ∃ x : Obj T M B.carrier.left,
        (SyntacticListEvaluation.SliceAlgebra.unpackedGraph
          (candidateMorphism T B m).graph).val.Evalb
          ![p.val, a.val, x.val] ∧ (decodedCons T B).val.Evalb ![p.val, v.val, x.val, y.val] := by
  let va : Obj T M (listObject T V) :=
    ⟨adjoin v.val a.val, (listCarrier_cons V v.val a.val).mpr ⟨v.property, a.property⟩⟩
  let u := pairPoint T M p v
  let w := pairPoint T M p a
  let x := (F T M).map m.left w
  obtain ⟨q, hq₁, hq₂⟩ := modelOverProduct_exists T M
    (constantFamily P V) (constantFamily P (listObject T V)) u w
    ((pairPoint_fst T M p v).trans (pairPoint_fst T M p a).symm)
  let r := (F T M).map (prod.map (𝟙 (constantFamily P V)) m).left q
  have hr₁ : (F T M).map (consFirst T B) r = u := by
    have h := modelOverProduct_map_fst T M (𝟙 (constantFamily P V)) m q
    have hi : (F T M).map (Over.Hom.left (𝟙 (constantFamily P V)))
        ((F T M).map (prod.fst : constantFamily P V ⨯
          constantFamily P (listObject T V) ⟶ constantFamily P V).left q) =
        (F T M).map (prod.fst : constantFamily P V ⨯
          constantFamily P (listObject T V) ⟶ constantFamily P V).left q :=
      ConcreteCategory.congr_hom ((F T M).map_id (P ⨯ V)) _
    exact h.trans (hi.trans hq₁)
  have hr₂ : (F T M).map (consSecond T B) r = x :=
    (modelOverProduct_map_snd T M (𝟙 (constantFamily P V)) m q).trans
      (congrArg ((F T M).map m.left) hq₂)
  have hhead : (F T M).map ((algebra T V).withParameters P).cons.left q =
      pairPoint T M p va := by
    apply modelProduct_ext T M
    · exact (parameter_cons_fst T (P := P) (V := V) M q).trans
        ((over_value T M (prod.fst : constantFamily P V ⨯
          constantFamily P (listObject T V) ⟶ constantFamily P V) q).symm.trans
            (((congrArg ((F T M).map (prod.fst : P ⨯ V ⟶ P)) hq₁).trans
              (pairPoint_fst T M p v)).trans (pairPoint_fst T M p va).symm))
    · apply Subtype.ext
      have hv := (congrArg ((F T M).map (prod.snd : P ⨯ V ⟶ V)) hq₁).trans
        (pairPoint_snd T M p v)
      have ha := (congrArg ((F T M).map
        (prod.snd : P ⨯ listObject T V ⟶ listObject T V)) hq₂).trans
          (pairPoint_snd T M p a)
      exact (parameter_cons_snd T (P := P) (V := V) M q).trans
        ((congrArg₂ adjoin (congrArg Subtype.val hv) (congrArg Subtype.val ha)).trans
          (congrArg Subtype.val (pairPoint_snd T M p va)).symm)
  have he : (F T M).map m.left (pairPoint T M p va) = (F T M).map B.cons.left r := by
    rw [← hhead]
    have hm := congrArg (F T M).map (congrArg Over.Hom.left hc)
    change (F T M).map (((algebra T V).withParameters P).cons.left ≫ m.left) =
      (F T M).map ((prod.map (𝟙 (constantFamily P V)) m).left ≫ B.cons.left) at hm
    rw [Functor.map_comp, Functor.map_comp] at hm
    exact ConcreteCategory.congr_hom hm q
  rw [candidate_eval T B m M p va y]
  constructor
  · intro hy
    refine ⟨x, (candidate_eval T B m M p a x).mpr rfl, ?_⟩
    exact (decodedCons_model T B M p v x y).mpr
      ⟨r, (congrArg ((F T M).map (prod.fst : P ⨯ V ⟶ P)) hr₁).trans
        (pairPoint_fst T M p v),
        (congrArg ((F T M).map (prod.snd : P ⨯ V ⟶ V)) hr₁).trans
        (pairPoint_snd T M p v), hr₂, he.symm.trans hy⟩
  · rintro ⟨x', hx', hy'⟩
    have hxx : x = x' := (candidate_eval T B m M p a x').mp hx'
    obtain ⟨r', hp', hv', hx'', hy''⟩ := (decodedCons_model T B M p v x' y).mp hy'
    have hu' : (F T M).map (consFirst T B) r' = u :=
      modelProduct_ext T M (hp'.trans (pairPoint_fst T M p v).symm)
        (hv'.trans (pairPoint_snd T M p v).symm)
    have hr' : r' = r := modelOverProduct_ext T M (constantFamily P V) B.carrier
      (hu'.trans hr₁.symm) (hx''.trans (hxx.symm.trans hr₂.symm))
    exact he.trans ((congrArg ((F T M).map B.cons.left) hr'.symm).trans hy'')

end Models

/-- Every actual slice morphism satisfying the constructor equations is
the constructed fold. The only induction used here is the proved internal
Pi-one candidate-graph induction of `evaluation_unique`. -/
theorem fold_unique
    (hn : ((algebra T V).withParameters P).nil ≫ m = B.nil)
    (hc : ((algebra T V).withParameters P).cons ≫ m =
      prod.map (𝟙 (constantFamily P V)) m ≫ B.cons) : m = fold T B := by
  let H := candidateMorphism T B m
  have hnil : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p y : M),
      (SyntacticListEvaluation.SliceAlgebra.unpackedGraph H.graph).val.Evalb ![p, 0, y] ↔
        (decode T B).nilOp.graph.val.Evalb ![p, y] := by
    intro M _ _ p y
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    constructor
    · intro h
      have hp := (SyntacticListEvaluation.SliceAlgebra.candidate_source H p 0 y h).1
      have hy := (H.support_model M _ y
        ((SyntacticListEvaluation.SliceAlgebra.unpackedGraph_eval H.graph p 0 y).mp h)).2
      exact (candidate_nil_typed T B m M hn ⟨p, hp⟩ ⟨y, hy⟩).mp h
    · intro h
      have hs := (decode T B).nilOp.support_model M p y h
      exact (candidate_nil_typed T B m M hn ⟨p, hs.1⟩ ⟨y, hs.2⟩).mpr h
  have hcons : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
      (p v a y : M),
      (SyntacticListEvaluation.SliceAlgebra.unpackedGraph H.graph).val.Evalb
        ![p, adjoin v a, y] ↔ V.val.Evalb ![v] ∧ ∃ x : M,
          (SyntacticListEvaluation.SliceAlgebra.unpackedGraph H.graph).val.Evalb ![p, a, x] ∧
            (decode T B).consOp.val.Evalb ![p, v, x, y] := by
    intro M _ _ _ p v a y
    constructor
    · intro h
      obtain ⟨hp, hva⟩ := SyntacticListEvaluation.SliceAlgebra.candidate_source H p (adjoin v a) y h
      obtain ⟨hv, ha⟩ := (listCarrier_cons V v a).mp hva
      have hy := (H.support_model M _ y
        ((SyntacticListEvaluation.SliceAlgebra.unpackedGraph_eval H.graph p (adjoin v a) y).mp h)).2
      obtain ⟨x, hx, hxy⟩ := (candidate_cons_typed T B m M hc
        ⟨p, hp⟩ ⟨v, hv⟩ ⟨a, ha⟩ ⟨y, hy⟩).mp h
      exact ⟨hv, x.val, hx, hxy⟩
    · rintro ⟨hv, x, hx, hxy⟩
      obtain ⟨hp, ha⟩ := SyntacticListEvaluation.SliceAlgebra.candidate_source H p a x hx
      obtain ⟨_, _, hxx, hyy⟩ := decodedCons_support T B M p v x y hxy
      exact (candidate_cons_typed T B m M hc
        ⟨p, hp⟩ ⟨v, hv⟩ ⟨a, ha⟩ ⟨y, hyy⟩).mpr ⟨⟨x, hxx⟩, hx, hxy⟩
  have he := (decode T B).evaluation_unique H hnil hcons
  change representedArrow T (chosenGraph T
    (fromRawProduct T P (listObject T V) ≫ m.left)) = _ at he
  rw [chosenGraph_class] at he
  apply Over.OverMorphism.ext
  change m.left = foldMap T B
  have hh := congrArg (fun f => toRawProduct T P (listObject T V) ≫ f) he
  simpa only [← Category.assoc, toRaw_fromRaw, Category.id_comp, foldMap] using hh

end CategoricalEssentialIncompleteness.V46.SyntacticLists
