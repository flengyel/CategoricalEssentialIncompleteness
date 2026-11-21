/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticLists
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
public import CategoricalEssentialIncompleteness.V46CategoricalSyntax
public import CategoricalEssentialIncompleteness.CharacteristicArrows

/-! # Internal decidable equality for arbitrary Sigma-one variable predicates -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.PredicateInterpretation

namespace CategoricalEssentialIncompleteness.V46.SyntacticDecidableVariables
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

abbrev RawBool : PredicateCategory T := sumCarrier terminalCarrier terminalCarrier

def terminalIso : CategoryTheory.Iso (C := PredicateCategory T)
    terminalCarrier (⊤_ (PredicateCategory T)) :=
  IsTerminal.uniqueUpToIso (C := PredicateCategory T)
    (SyntacticPredicates.terminalIsTerminal T)
    (Limits.terminalIsTerminal (C := PredicateCategory T))

def booleanIso : RawBool T ≅ Two (PredicateCategory T) :=
  (sumIsColimit T terminalCarrier terminalCarrier).coconePointUniqueUpToIso
    (coprodIsCoprod (C := PredicateCategory T) terminalCarrier terminalCarrier) ≪≫
      coprod.mapIso (terminalIso T) (terminalIso T)

@[reassoc] theorem sumInr_booleanIso :
    representedArrow T (sumInr T terminalCarrier terminalCarrier) ≫ (booleanIso T).hom =
      (terminalIso T).hom ≫ coprod.inr := by
  change representedArrow T (sumInr T terminalCarrier terminalCarrier) ≫
    ((sumIsColimit T terminalCarrier terminalCarrier).coconePointUniqueUpToIso
      (coprodIsCoprod (C := PredicateCategory T) terminalCarrier terminalCarrier)).hom ≫
      coprod.map (terminalIso T).hom (terminalIso T).hom = _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (sumIsColimit T terminalCarrier terminalCarrier)
    (coprodIsCoprod (C := PredicateCategory T) terminalCarrier terminalCarrier) ⟨WalkingPair.right⟩
  erw [← Category.assoc, h, coprod.inr_map]

def rawTrue (C : PredicateCategory T) : C ⟶ RawBool T :=
  representedArrow T (terminalMap T C) ≫
    representedArrow T (sumInr T terminalCarrier terminalCarrier)

@[reassoc] theorem rawTrue_booleanIso (C : PredicateCategory T) :
    rawTrue T C ≫ (booleanIso T).hom = terminal.from C ≫ coprod.inr := by
  rw [rawTrue, Category.assoc, sumInr_booleanIso, ← Category.assoc]
  congr 1
  exact (Limits.terminalIsTerminal (C := PredicateCategory T)).hom_ext _ _

def equalityGraph (V : Carrier) : Graph :=
  .mkSigma “z b. ∃ x y, !pairDef.val z x y ∧ !V.val x ∧ !V.val y ∧
    ((x = y ∧ !pairDef.val b 0 1) ∨ (x ≠ y ∧ !pairDef.val b 0 0))”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem equalityGraph_eval (V : Carrier) (z b : M) :
    (equalityGraph V).val.Evalb ![z, b] ↔
      ∃ x y : M, z = Arithmetic.pair x y ∧ V.val.Evalb ![x] ∧ V.val.Evalb ![y] ∧
        ((x = y ∧ b = Arithmetic.pair 0 1) ∨ (x ≠ y ∧ b = Arithmetic.pair 0 0)) := by
  simp [equalityGraph]

theorem equalityGraph_pair (V : Carrier) (x y b : M) :
    (equalityGraph V).val.Evalb ![Arithmetic.pair x y, b] ↔
      V.val.Evalb ![x] ∧ V.val.Evalb ![y] ∧
        ((x = y ∧ b = Arithmetic.pair 0 1) ∨ (x ≠ y ∧ b = Arithmetic.pair 0 0)) := by
  rw [equalityGraph_eval]
  constructor
  · rintro ⟨u, v, he, hu, hv, hb⟩
    obtain ⟨rfl, rfl⟩ := (pair_eq_pair_iff _ _ _ _).mp he
    exact ⟨hu, hv, hb⟩
  · rintro ⟨hx, hy, hb⟩
    exact ⟨x, y, rfl, hx, hy, hb⟩

end ArithmeticModels

def equalityMorphism (V : PredicateCategory T) :
    GraphMorphism T (productCarrier V V) (RawBool T) where
  graph := equalityGraph V
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro z b h
    obtain ⟨x, y, he, hx, hy, hb⟩ := (equalityGraph_eval V z b).mp h
    refine ⟨(productCarrier_eval V V z).mpr ⟨x, y, he, hx, hy⟩, ?_⟩
    rcases hb with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact (sumCarrier_eval M terminalCarrier terminalCarrier _).mpr
        (Or.inr ⟨0, rfl, (terminalCarrier_eval _).mpr rfl⟩)
    · exact (sumCarrier_eval M terminalCarrier terminalCarrier _).mpr
        (Or.inl ⟨0, rfl, (terminalCarrier_eval _).mpr rfl⟩)
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro z hz
    obtain ⟨x, y, rfl, hx, hy⟩ := (productCarrier_eval V V z).mp hz
    by_cases he : x = y
    · refine ⟨Arithmetic.pair 0 1,
        (equalityGraph_pair V x y _).mpr ⟨hx, hy, Or.inl ⟨he, rfl⟩⟩, ?_⟩
      intro b hb
      rcases ((equalityGraph_pair V x y b).mp hb).2.2 with ⟨_, h⟩ | ⟨hne, _⟩
      · exact h
      · exact (hne he).elim
    · refine ⟨Arithmetic.pair 0 0,
        (equalityGraph_pair V x y _).mpr ⟨hx, hy, Or.inr ⟨he, rfl⟩⟩, ?_⟩
      intro b hb
      rcases ((equalityGraph_pair V x y b).mp hb).2.2 with ⟨heq, _⟩ | ⟨_, h⟩
      · exact (he heq).elim
      · exact h

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The literal true record, with its arithmetic structure obtained from T. -/
def trueValue : M := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact Arithmetic.pair 0 1

theorem rawTrue_value (C : PredicateCategory T) (x : Obj M C) :
    ((functor T M).map (rawTrue T C) x).val = trueValue T M := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let z := (functor T M).map (representedArrow T (terminalMap T C)) x
  have hz : z.val = 0 := (terminalCarrier_eval _).mp z.property
  change ((functor T M).map
    (representedArrow T (terminalMap T C) ≫
      representedArrow T (sumInr T terminalCarrier terminalCarrier)) x).val = _
  rw [Functor.map_comp]
  change ((functor T M).map (representedArrow T
    (sumInr T terminalCarrier terminalCarrier)) z).val = _
  rw [map_sumInr]
  change Arithmetic.pair z.val 1 = Arithmetic.pair 0 1
  rw [hz]

theorem equality_value (V : PredicateCategory T) (q : SyntacticLists.Obj T M (V ⨯ V)) :
    ((functor T M).map (SyntacticLists.toRawProduct T V V ≫
      representedArrow T (equalityMorphism T V)) q).val = trueValue T M ↔
      ((functor T M).map (prod.fst : V ⨯ V ⟶ V) q).val =
        ((functor T M).map (prod.snd : V ⨯ V ⟶ V) q).val := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let r := (functor T M).map (SyntacticLists.toRawProduct T V V) q
  let b := (functor T M).map (representedArrow T (equalityMorphism T V)) r
  have hr := SyntacticLists.toRawProduct_value T M V V q
  have hb := (map_class_eq_iff T M (equalityMorphism T V) r b).mp rfl
  change (equalityGraph V).val.Evalb ![r.val, b.val] at hb
  change r.val = _ at hr
  rw [hr, equalityGraph_pair] at hb
  rw [Functor.map_comp]
  change b.val = Arithmetic.pair 0 1 ↔ _
  constructor
  · intro ht
    rcases hb.2.2 with ⟨he, _⟩ | ⟨_, hf⟩
    · exact he
    · have h01 := ((pair_eq_pair_iff _ _ _ _).mp (hf.symm.trans ht)).2
      exact (_root_.zero_ne_one h01).elim
  · intro he
    rcases hb.2.2 with ⟨_, ht⟩ | ⟨hne, _⟩
    · exact ht
    · exact (hne he).elim

end Models

theorem raw_test_true_iff {C : PredicateCategory T} (V : PredicateCategory T)
    (a : C ⟶ V ⨯ V) :
    a ≫ SyntacticLists.toRawProduct T V V ≫
      representedArrow T (equalityMorphism T V) = rawTrue T C ↔
        a ≫ prod.fst = a ≫ prod.snd := by
  constructor
  · intro h
    apply jointly_faithful T
    intro M _ _
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    have he := congrArg (fun f => (functor T M).map f) h
    rw [Functor.map_comp] at he
    have hx := congrArg Subtype.val (ConcreteCategory.congr_hom he x)
    have hv := (equality_value T M V ((functor T M).map a x)).mp
      (hx.trans (rawTrue_value T M C x))
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hv
  · intro h
    apply jointly_faithful T
    intro M _ _
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    have he := congrArg (fun f => (functor T M).map f) h
    have hx := congrArg Subtype.val (ConcreteCategory.congr_hom he x)
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hx
    have hv := ((equality_value T M V ((functor T M).map a x)).mpr hx).trans
      (rawTrue_value T M C x).symm
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hv

def test (V : PredicateCategory T) : V ⨯ V ⟶ Two (PredicateCategory T) :=
  SyntacticLists.toRawProduct T V V ≫ representedArrow T (equalityMorphism T V) ≫
    (booleanIso T).hom

theorem test_true_iff {C : PredicateCategory T} (V : PredicateCategory T)
    (a : C ⟶ V ⨯ V) :
    a ≫ test T V = terminal.from C ≫ coprod.inr ↔ a ≫ prod.fst = a ≫ prod.snd := by
  unfold test
  rw [← rawTrue_booleanIso T C, ← Category.assoc, ← Category.assoc, cancel_mono]
  simpa only [Category.assoc] using raw_test_true_iff T V a

/-- The equality test has the diagonal as its true pullback, with the universal property
for arbitrary generalized names. -/
def decidableVariables (V : PredicateCategory T) : DecidableVariables V where
  test := test T V
  diagonal := by
    let d := prod.lift (𝟙 V) (𝟙 V)
    have hd : d ≫ test T V = terminal.from V ≫ coprod.inr :=
      (test_true_iff T V d).mpr (by simp [d])
    refine IsPullback.of_isLimit (c := PullbackCone.mk d (terminal.from V) hd) ?_
    refine PullbackCone.IsLimit.mk hd
      (fun s => s.fst ≫ prod.fst) ?_ ?_ ?_
    · intro s
      have he : s.fst ≫ prod.fst = s.fst ≫ prod.snd :=
        (test_true_iff T V s.fst).mp (by
          have hc := s.condition
          rw [show s.snd = terminal.from s.pt from terminal.hom_ext _ _] at hc
          exact hc)
      apply prod.hom_ext
      · simp [d]
      · simpa [d, Category.assoc] using he
    · intro s
      exact terminal.hom_ext _ _
    · intro s m hm _
      have h := congrArg (fun f => f ≫ prod.fst) hm
      simpa [d, Category.assoc] using h

end CategoricalEssentialIncompleteness.V46.SyntacticDecidableVariables
