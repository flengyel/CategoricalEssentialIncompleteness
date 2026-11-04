/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticLists

/-! # Decoding arbitrary categorical list algebras in parameter slices -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- The chosen terminal object of the slice has its actual projection
isomorphic to the identity family, independently of any numerical coding. -/
def terminalOverIso (P : PredicateCategory T) : (⊤_ (Over P)).left ≅ P :=
  (Over.forget P).mapIso ((Limits.terminalIsTerminal (C := Over P)).uniqueUpToIso Over.mkIdTerminal)

theorem terminalOverIso_hom (P : PredicateCategory T) :
    (terminalOverIso T P).hom = (⊤_ (Over P)).hom := by
  have h := Over.w (((Limits.terminalIsTerminal (C := Over P)).uniqueUpToIso
    (Over.mkIdTerminal (X := P))).hom)
  change Over.Hom.left ((Limits.terminalIsTerminal (C := Over P)).uniqueUpToIso
    (Over.mkIdTerminal (X := P))).hom = _
  exact (Category.comp_id _).symm.trans h

variable {P V : PredicateCategory T} (B : ListAlgebra (D := Over P) (constantFamily P V))

def nilMap : P ⟶ B.carrier.left := (terminalOverIso T P).inv ≫ B.nil.left

theorem nilMap_over : nilMap T B ≫ B.carrier.hom = 𝟙 P := by
  rw [nilMap, Category.assoc, Over.w B.nil, ← terminalOverIso_hom,
    (terminalOverIso T P).inv_hom_id]

def consFirst : (constantFamily P V ⨯ B.carrier).left ⟶ P ⨯ V :=
  (prod.fst : constantFamily P V ⨯ B.carrier ⟶ constantFamily P V).left

def consSecond : (constantFamily P V ⨯ B.carrier).left ⟶ B.carrier.left :=
  (prod.snd : constantFamily P V ⨯ B.carrier ⟶ B.carrier).left

/-- A literal Sigma-one graph for the cons operation, read through the
actual projections of the product in the slice. -/
def decodedCons : SyntacticListEvaluation.ConsGraph :=
  let f := (chosenGraph T (consFirst T B)).graph
  let fp := (chosenGraph T (prod.fst : P ⨯ V ⟶ P)).graph
  let fv := (chosenGraph T (prod.snd : P ⨯ V ⟶ V)).graph
  let g := (chosenGraph T (consSecond T B)).graph
  let c := (chosenGraph T B.cons.left).graph
  .mkSigma “p v x y. ∃ q u, !f.val q u ∧ !fp.val u p ∧ !fv.val u v ∧
    !g.val q x ∧ !c.val q y”

section Models

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem decodedCons_eval_raw (p v x y : M) :
    (decodedCons T B).val.Evalb ![p, v, x, y] ↔
      ∃ q u : M, (chosenGraph T (consFirst T B)).graph.val.Evalb ![q, u] ∧
        (chosenGraph T (prod.fst : P ⨯ V ⟶ P)).graph.val.Evalb ![u, p] ∧
        (chosenGraph T (prod.snd : P ⨯ V ⟶ V)).graph.val.Evalb ![u, v] ∧
        (chosenGraph T (consSecond T B)).graph.val.Evalb ![q, x] ∧
        (chosenGraph T B.cons.left).graph.val.Evalb ![q, y] := by
  simp [decodedCons]

theorem decodedCons_support (p v x y : M)
    (h : (decodedCons T B).val.Evalb ![p, v, x, y]) :
    P.val.Evalb ![p] ∧ V.val.Evalb ![v] ∧
      B.carrier.left.val.Evalb ![x] ∧ B.carrier.left.val.Evalb ![y] := by
  obtain ⟨q, u, _, hp, hv, hx, hy⟩ := (decodedCons_eval_raw T B M p v x y).mp h
  exact ⟨((chosenGraph T (prod.fst : P ⨯ V ⟶ P)).support_model M u p hp).2,
    ((chosenGraph T (prod.snd : P ⨯ V ⟶ V)).support_model M u v hv).2,
    ((chosenGraph T (consSecond T B)).support_model M q x hx).2,
    ((chosenGraph T B.cons.left).support_model M q y hy).2⟩

theorem decodedCons_model (p : Obj T M P) (v : Obj T M V)
    (x y : Obj T M B.carrier.left) :
    (decodedCons T B).val.Evalb ![p.val, v.val, x.val, y.val] ↔
      ∃ q : Obj T M (constantFamily P V ⨯ B.carrier).left,
        (F T M).map (prod.fst : P ⨯ V ⟶ P) ((F T M).map (consFirst T B) q) = p ∧
        (F T M).map (prod.snd : P ⨯ V ⟶ V) ((F T M).map (consFirst T B) q) = v ∧
        (F T M).map (consSecond T B) q = x ∧ (F T M).map B.cons.left q = y := by
  rw [decodedCons_eval_raw]
  constructor
  · rintro ⟨q, u, hf, hp, hv, hx, hy⟩
    let qq : Obj T M (constantFamily P V ⨯ B.carrier).left :=
      ⟨q, ((chosenGraph T (consFirst T B)).support_model M q u hf).1⟩
    let uu : Obj T M (P ⨯ V) :=
      ⟨u, ((chosenGraph T (consFirst T B)).support_model M q u hf).2⟩
    have hfu := (chosenGraph_map_iff T M (consFirst T B) qq uu).mp hf
    refine ⟨qq, ?_, ?_, ?_, ?_⟩
    · rw [hfu]
      exact (chosenGraph_map_iff T M prod.fst uu p).mp hp
    · rw [hfu]
      exact (chosenGraph_map_iff T M prod.snd uu v).mp hv
    · exact (chosenGraph_map_iff T M (consSecond T B) qq x).mp hx
    · exact (chosenGraph_map_iff T M B.cons.left qq y).mp hy
  · rintro ⟨q, hp, hv, hx, hy⟩
    let u := (F T M).map (consFirst T B) q
    exact ⟨q.val, u.val,
      (chosenGraph_map_iff T M (consFirst T B) q u).mpr rfl,
      (chosenGraph_map_iff T M prod.fst u p).mpr hp,
      (chosenGraph_map_iff T M prod.snd u v).mpr hv,
      (chosenGraph_map_iff T M (consSecond T B) q x).mpr hx,
      (chosenGraph_map_iff T M B.cons.left q y).mpr hy⟩

theorem decodedCons_fibers (p : Obj T M P) (v : Obj T M V)
    (x y : Obj T M B.carrier.left)
    (h : (decodedCons T B).val.Evalb ![p.val, v.val, x.val, y.val]) :
    (F T M).map B.carrier.hom x = p ∧ (F T M).map B.carrier.hom y = p := by
  obtain ⟨q, hp, _, hx, hy⟩ := (decodedCons_model T B M p v x y).mp h
  have hf := over_value T M
    (prod.fst : constantFamily P V ⨯ B.carrier ⟶ constantFamily P V) q
  have hg := over_value T M
    (prod.snd : constantFamily P V ⨯ B.carrier ⟶ B.carrier) q
  have hc := over_value T M B.cons q
  have hbase : (F T M).map (constantFamily P V ⨯ B.carrier).hom q = p :=
    hf.symm.trans hp
  exact ⟨by rw [← hx]; exact hg.trans hbase,
    by rw [← hy]; exact hc.trans hbase⟩

theorem decodedCons_existsUnique (p : Obj T M P) (v : Obj T M V)
    (x : Obj T M B.carrier.left) (hx : (F T M).map B.carrier.hom x = p) :
    ∃! y : Obj T M B.carrier.left,
      (decodedCons T B).val.Evalb ![p.val, v.val, x.val, y.val] := by
  obtain ⟨u, hup, huv⟩ := modelProduct_exists T M P V p v
  have hu : (F T M).map (constantFamily P V).hom u =
      (F T M).map B.carrier.hom x := hup.trans hx.symm
  obtain ⟨q, hqf, hqg⟩ := modelOverProduct_exists T M (constantFamily P V) B.carrier u x hu
  let y := (F T M).map B.cons.left q
  refine ⟨y, (decodedCons_model T B M p v x y).mpr ?_, ?_⟩
  · refine ⟨q, ?_, ?_, hqg, rfl⟩
    · exact (congrArg ((F T M).map (prod.fst : P ⨯ V ⟶ P)) hqf).trans hup
    · exact (congrArg ((F T M).map (prod.snd : P ⨯ V ⟶ V)) hqf).trans huv
  · intro y' hy'
    obtain ⟨q', hp', hv', hx', hy'⟩ := (decodedCons_model T B M p v x y').mp hy'
    have hu' : (F T M).map (consFirst T B) q' = u :=
      modelProduct_ext T M (hp'.trans hup.symm) (hv'.trans huv.symm)
    have hqq : q' = q := modelOverProduct_ext T M (constantFamily P V) B.carrier
      (hu'.trans hqf.symm) (hx'.trans hqg.symm)
    exact hy'.symm.trans (congrArg ((F T M).map B.cons.left) hqq)

end Models

/-- An arbitrary algebra in an arbitrary parameter slice is translated
into its actual graph operations. No evaluation map occurs in these data. -/
def decode : SyntacticListEvaluation.SliceAlgebra T P V B.carrier.left where
  projection := chosenGraph T B.carrier.hom
  nilOp := chosenGraph T (nilMap T B)
  nil_over := by
    apply complete.{0} T
    intro M _ _
    have hnil : ∀ p y : M, (chosenGraph T (nilMap T B)).graph.val.Evalb ![p, y] →
        (chosenGraph T B.carrier.hom).graph.val.Evalb ![y, p] := by
      intro p y h
      have hs := (chosenGraph T (nilMap T B)).support_model M p y h
      let pp : Obj T M P := ⟨p, hs.1⟩
      let yy : Obj T M B.carrier.left := ⟨y, hs.2⟩
      have hn := (chosenGraph_map_iff T M (nilMap T B) pp yy).mp h
      have he := congrArg (F T M).map (nilMap_over T B)
      rw [Functor.map_comp, (F T M).map_id P] at he
      have hp := ConcreteCategory.congr_hom he pp
      change (F T M).map B.carrier.hom ((F T M).map (nilMap T B) pp) = pp at hp
      rw [hn] at hp
      exact (chosenGraph_map_iff T M B.carrier.hom yy pp).mpr hp
    simpa [models_iff, SyntacticListEvaluation.nilOverSentence] using hnil
  consOp := decodedCons T B
  cons_support := by
    apply complete.{0} T
    intro M _ _
    have hsup : ∀ p v x y : M, (decodedCons T B).val.Evalb ![p, v, x, y] →
        P.val.Evalb ![p] ∧ V.val.Evalb ![v] ∧ B.carrier.left.val.Evalb ![x] ∧
          (chosenGraph T B.carrier.hom).graph.val.Evalb ![x, p] ∧
            B.carrier.left.val.Evalb ![y] ∧
              (chosenGraph T B.carrier.hom).graph.val.Evalb ![y, p] := by
      intro p v x y h
      obtain ⟨hp, hv, hx, hy⟩ := decodedCons_support T B M p v x y h
      have hfib := decodedCons_fibers T B M ⟨p, hp⟩ ⟨v, hv⟩ ⟨x, hx⟩ ⟨y, hy⟩ h
      exact ⟨hp, hv, hx, (chosenGraph_map_iff T M B.carrier.hom ⟨x, hx⟩ ⟨p, hp⟩).mpr
        hfib.1, hy, (chosenGraph_map_iff T M B.carrier.hom ⟨y, hy⟩ ⟨p, hp⟩).mpr hfib.2⟩
    simpa [models_iff, SyntacticListEvaluation.consSupportSentence] using hsup
  cons_total := by
    apply complete.{0} T
    intro M _ _
    have htotal : ∀ p v x : M, P.val.Evalb ![p] → V.val.Evalb ![v] →
        B.carrier.left.val.Evalb ![x] →
          (chosenGraph T B.carrier.hom).graph.val.Evalb ![x, p] →
            ∃! y : M, (decodedCons T B).val.Evalb ![p, v, x, y] := by
      intro p v x hp hv hx hxp
      have hfib := (chosenGraph_map_iff T M B.carrier.hom ⟨x, hx⟩ ⟨p, hp⟩).mp hxp
      obtain ⟨y, hy, hu⟩ := decodedCons_existsUnique T B M ⟨p, hp⟩ ⟨v, hv⟩ ⟨x, hx⟩ hfib
      refine ⟨y.val, hy, ?_⟩
      intro z hz
      have hsz := (decodedCons_support T B M p v x z hz).2.2.2
      exact congrArg Subtype.val (hu ⟨z, hsz⟩ hz)
    simpa [models_iff, SyntacticListEvaluation.consTotalSentence] using htotal

end CategoricalEssentialIncompleteness.V46.SyntacticLists
