/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxGeometry
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution

/-! Successful derivation codes retain exactly the original tree code.
The validator value and all computation witnesses are existential. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessCarrier
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {W F : PredicateCategory T}
  (v : @Quiver.Hom (PredicateCategory T) inferInstance W (OptionSyntax.obj F))

def valueGraph : Graph :=
  let G := (chosenGraph T v).graph
  let J := (chosenGraph T (coprod.inr : F ⟶ OptionSyntax.obj F)).graph
  .mkSigma “d z. !W.val d ∧ ∃ u, !G.val d u ∧ !J.val z u”

def carrier : Carrier := let G := valueGraph v
  .mkSigma “d. ∃ z, !G.val d z”

def inclusionGraph : Graph := let C := carrier v
  .mkSigma “d e. !C.val d ∧ d = e”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem valueGraph_eval (d z : M) :
    (valueGraph v).val.Evalb ![d, z] ↔ W.val.Evalb ![d] ∧
      ∃ u : M, (chosenGraph T v).graph.val.Evalb ![d, u] ∧
        (chosenGraph T (coprod.inr : F ⟶ OptionSyntax.obj F)).graph.val.Evalb ![z, u] := by
  simp [valueGraph]

@[simp] theorem carrier_eval (d : M) :
    (carrier v).val.Evalb ![d] ↔ ∃ z : M, (valueGraph v).val.Evalb ![d, z] := by
  simp [carrier]

@[simp] theorem inclusionGraph_eval (d e : M) :
    (inclusionGraph v).val.Evalb ![d, e] ↔ (carrier v).val.Evalb ![d] ∧ d = e := by
  simp [inclusionGraph]

theorem valueGraph_support (d z : M) (h : (valueGraph v).val.Evalb ![d, z]) :
    (carrier v).val.Evalb ![d] ∧ F.val.Evalb ![z] := by
  obtain ⟨_, u, _, hJ⟩ := (valueGraph_eval v M d z).mp h
  exact ⟨(carrier_eval v M d).mpr ⟨z, h⟩,
    ((chosenGraph T (coprod.inr : F ⟶ OptionSyntax.obj F)).support_model M z u hJ).1⟩

theorem valueGraph_functional (d y z : M)
    (hy : (valueGraph v).val.Evalb ![d, y]) (hz : (valueGraph v).val.Evalb ![d, z]) : y = z := by
  obtain ⟨hd, a, hda, hya⟩ := (valueGraph_eval v M d y).mp hy
  obtain ⟨_, b, hdb, hzb⟩ := (valueGraph_eval v M d z).mp hz
  have hab : a = b := ((chosenGraph T v).total_model M d hd).unique hda hdb
  subst b
  exact SyntacticSyntax.chosenGraph_input_unique T M
    (coprod.inr : F ⟶ OptionSyntax.obj F)
    (SyntacticSyntax.preservedSum_properties (SyntacticLists.F T M) (⊤_ _) F).2.1
    y z a hya hzb

end Models

def conclusion : GraphMorphism T (carrier v) F where
  graph := valueGraph v
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    exact valueGraph_support v M
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro d hd
    obtain ⟨z, hz⟩ := (carrier_eval v M d).mp hd
    exact ⟨z, hz, fun y hy => valueGraph_functional v M d y z hy hz⟩

def inclusion : GraphMorphism T (carrier v) W where
  graph := inclusionGraph v
  support := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, supportSentence_eval]
    intro d e h
    have he : (carrier v).val.Evalb ![d] ∧ d = e := by simpa [inclusionGraph] using h
    obtain ⟨z, hz⟩ := (carrier_eval v M d).mp he.1
    exact ⟨he.1, he.2 ▸ ((valueGraph_eval v M d z).mp hz).1⟩
  total := by
    apply complete.{0} T
    intro M _ _
    rw [models_iff, totalSentence_eval]
    intro d hd
    refine ⟨d, ?_, ?_⟩
    · simpa [inclusionGraph] using And.intro hd (rfl : d = d)
    · intro e he
      exact (show (carrier v).val.Evalb ![d] ∧ d = e by simpa [inclusionGraph] using he).2.symm

theorem square :
    representedArrow T (inclusion v) ≫ v =
      representedArrow T (conclusion v) ≫ (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  rw [Functor.map_comp, Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro d
  let c := (SyntacticLists.F T M).map (representedArrow T (conclusion v)) d
  have hc := (PredicateInterpretation.map_class_eq_iff T M (conclusion v) d c).mp rfl
  obtain ⟨hd, u, hdu, hcu⟩ := (valueGraph_eval v M d.val c.val).mp hc
  let w : Obj T M W := ⟨d.val, hd⟩
  let o : Obj T M (OptionSyntax.obj F) := ⟨u, ((chosenGraph T v).support_model M d.val u hdu).2⟩
  have hi : (SyntacticLists.F T M).map (representedArrow T (inclusion v)) d = w := by
    apply (PredicateInterpretation.map_class_eq_iff T M (inclusion v) d w).mpr
    simpa [inclusion, inclusionGraph, w] using And.intro d.property (rfl : d.val = d.val)
  have hv := (chosenGraph_map_iff T M v w o).mp hdu
  have hj := (chosenGraph_map_iff T M (coprod.inr : F ⟶ OptionSyntax.obj F) c o).mp hcu
  exact (congrArg ((SyntacticLists.F T M).map (v)) hi).trans (hv.trans hj.symm)

def comparison : @Quiver.Hom (PredicateCategory T) inferInstance (carrier v)
    (pullback (v) (coprod.inr : F ⟶ OptionSyntax.obj F)) :=
  pullback.lift (representedArrow T (inclusion v)) (representedArrow T (conclusion v)) (square v)

theorem comparison_isIso : IsIso (comparison v) := by
  apply PredicateInterpretation.isIso_of_models_bijective T
  intro M _ _
  have hp := (IsPullback.of_hasPullback (v)
    (coprod.inr : F ⟶ OptionSyntax.obj F)).map (SyntacticLists.F T M)
  constructor
  · intro x y h
    have hi := congrArg ((SyntacticLists.F T M).map (pullback.fst
      (v) (coprod.inr : F ⟶ OptionSyntax.obj F))) h
    have hv (z : Obj T M (carrier v)) :
        ((SyntacticLists.F T M).map (representedArrow T (inclusion v)) z).val = z.val := by
      let zz := (SyntacticLists.F T M).map (representedArrow T (inclusion v)) z
      have he := (PredicateInterpretation.map_class_eq_iff T M (inclusion v) z zz).mp rfl
      exact ((inclusionGraph_eval v M z.val zz.val).mp he).2.symm
    have he : (SyntacticLists.F T M).map (representedArrow T (inclusion v)) x =
        (SyntacticLists.F T M).map (representedArrow T (inclusion v)) y := by
      have hh := congrArg (SyntacticLists.F T M).map
        (pullback.lift_fst (representedArrow T (inclusion v))
          (representedArrow T (conclusion v)) (square v))
      rw [Functor.map_comp] at hh
      exact (ConcreteCategory.congr_hom hh x).symm.trans
        (hi.trans (ConcreteCategory.congr_hom hh y))
    apply Subtype.ext
    simpa only [hv] using congrArg Subtype.val he
  · intro z
    let d := (SyntacticLists.F T M).map (pullback.fst
      (v) (coprod.inr : F ⟶ OptionSyntax.obj F)) z
    let c := (SyntacticLists.F T M).map (pullback.snd
      (v) (coprod.inr : F ⟶ OptionSyntax.obj F)) z
    let o := (SyntacticLists.F T M).map (v) d
    have hw : o = (SyntacticLists.F T M).map (coprod.inr : F ⟶ OptionSyntax.obj F) c :=
      ConcreteCategory.congr_hom hp.w z
    have hdu := (chosenGraph_map_iff T M v d o).mpr rfl
    have hcu := (chosenGraph_map_iff T M (coprod.inr : F ⟶ OptionSyntax.obj F) c o).mpr hw.symm
    have hc : (valueGraph v).val.Evalb ![d.val, c.val] :=
      (valueGraph_eval v M d.val c.val).mpr ⟨d.property, o.val, hdu, hcu⟩
    let w : Obj T M (carrier v) := ⟨d.val, (carrier_eval v M d.val).mpr ⟨c.val, hc⟩⟩
    refine ⟨w, ?_⟩
    apply Types.ext_of_isPullback hp
    · change (SyntacticLists.F T M).map (pullback.fst _ _)
        ((SyntacticLists.F T M).map (comparison v) w) = d
      have he := congrArg (SyntacticLists.F T M).map
        (pullback.lift_fst (representedArrow T (inclusion v))
          (representedArrow T (conclusion v)) (square v))
      rw [Functor.map_comp] at he
      apply (ConcreteCategory.congr_hom he w).trans
      apply (PredicateInterpretation.map_class_eq_iff T M (inclusion v) w d).mpr
      simpa [inclusion, inclusionGraph, w] using And.intro w.property (rfl : d.val = d.val)
    · change (SyntacticLists.F T M).map (pullback.snd _ _)
        ((SyntacticLists.F T M).map (comparison v) w) = c
      have he := congrArg (SyntacticLists.F T M).map
        (pullback.lift_snd (representedArrow T (inclusion v))
          (representedArrow T (conclusion v)) (square v))
      rw [Functor.map_comp] at he
      apply (ConcreteCategory.congr_hom he w).trans
      exact (PredicateInterpretation.map_class_eq_iff T M (conclusion v) w c).mpr hc

def overIso : Over.mk (representedArrow T (conclusion v)) ≅
    (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
      (Over.mk (v)) := by
  letI : IsIso (comparison v) := comparison_isIso v
  exact Over.isoMk (asIso (comparison v)) (by simp [comparison])

/-- The raw carrier and chosen success pullback have the same tree
inclusion; no output code or computation record is added to the tree. -/
@[simp, reassoc] theorem overIso_tree :
    (overIso v).hom.left ≫ pullback.fst (v)
      (coprod.inr : F ⟶ OptionSyntax.obj F) = representedArrow T (inclusion v) := by
  simp [overIso, comparison]

def rawAlgebra (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
      (Over.mk (v))) ⟶
        (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
          (Over.mk (v))) : Endofunctor.Algebra H where
  a := Over.mk (representedArrow T (conclusion v))
  str := H.map (overIso v).hom ≫ α ≫ (overIso v).inv

def algebraIso (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
      (Over.mk (v))) ⟶
        (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
          (Over.mk (v))) :
    rawAlgebra v H α ≅ Endofunctor.Algebra.mk _ α :=
  Endofunctor.Algebra.isoMk (overIso v) (by simp [rawAlgebra, Category.assoc])

theorem rawAlgebra_tree (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
      (Over.mk v)) ⟶ (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
        (Over.mk v)) :
    (rawAlgebra v H α).str.left ≫ representedArrow T (inclusion v) =
      (H.map (overIso v).hom).left ≫ α.left ≫
        pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  have hi : (overIso v).inv.left ≫ representedArrow T (inclusion v) =
      pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F) := by
    rw [← overIso_tree v, ← Category.assoc]
    simp
  simp only [rawAlgebra, Over.comp_left, Category.assoc, hi]

theorem rawAlgebra_conclusion (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
      (Over.mk v)) ⟶ (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
        (Over.mk v)) :
    (rawAlgebra v H α).str.left ≫ representedArrow T (conclusion v) =
      (H.obj (Over.mk (representedArrow T (conclusion v)))).hom :=
  Over.w (rawAlgebra v H α).str

def rawInitial (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
      (Over.mk (v))) ⟶
        (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj
          (Over.mk (v)))
    (h : IsInitial (Endofunctor.Algebra.mk _ α)) : IsInitial (rawAlgebra v H α) :=
  h.ofIso (algebraIso v H α).symm

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessCarrier
