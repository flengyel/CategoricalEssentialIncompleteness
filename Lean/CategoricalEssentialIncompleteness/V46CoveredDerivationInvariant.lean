/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticFiniteCoverage
public import CategoricalEssentialIncompleteness.V46DerivationInternalInduction
public import CategoricalEssentialIncompleteness.V46SyntacticLists
public import CategoricalEssentialIncompleteness.TwoBoolean

/-! # A Pi-one invariant for truth on a fixed covering support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.CoveredDerivationInvariant
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {D C P Fm : PredicateCategory T}

/-- Truth at the actual model points of the chosen parameter product. -/
def TrueAt (v : P ⨯ Fm ⟶ Two (PredicateCategory T))
    (l : Obj T M P) (f : Obj T M Fm) : Prop :=
  ∀ q : Obj T M (P ⨯ Fm),
    (F T M).map (prod.fst : P ⨯ Fm ⟶ P) q = l →
    (F T M).map (prod.snd : P ⨯ Fm ⟶ Fm) q = f →
    (F T M).map v q = (F T M).map (Two.constant (P ⨯ Fm) true) q

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
/-- An arbitrary generalized input represents the same model product point. -/
theorem trueAt_lift (v : P ⨯ Fm ⟶ Two (PredicateCategory T))
    {W : PredicateCategory T} (p : W ⟶ P) (f : W ⟶ Fm) (w : Obj T M W) :
    TrueAt T M v ((F T M).map p w) ((F T M).map f w) ↔
      (F T M).map (prod.lift p f ≫ v) w =
        (F T M).map (Two.constant W true) w := by
  have hp : (F T M).map (prod.fst : P ⨯ Fm ⟶ P)
      ((F T M).map (prod.lift p f) w) = (F T M).map p w := by
    rw [← Functor.map_comp_apply, prod.lift_fst]
  have hf : (F T M).map (prod.snd : P ⨯ Fm ⟶ Fm)
      ((F T M).map (prod.lift p f) w) = (F T M).map f w := by
    rw [← Functor.map_comp_apply, prod.lift_snd]
  have hc : (F T M).map (Two.constant (P ⨯ Fm) true)
      ((F T M).map (prod.lift p f) w) =
        (F T M).map (Two.constant W true) w := by
    rw [← Functor.map_comp_apply, Two.comp_constant]
  constructor
  · intro h
    rw [Functor.map_comp_apply, ← hc]
    exact h _ hp hf
  · intro h q hqp hqf
    have he : q = (F T M).map (prod.lift p f) w :=
      modelProduct_ext T M (hqp.trans hp.symm) (hqf.trans hf.symm)
    subst q
    rw [hc]
    simpa only [Functor.map_comp_apply] using h

variable (support : D ⟶ C) (conclusion : D ⟶ Fm)
variable (v : P ⨯ Fm ⟶ Two (PredicateCategory T)) (l : Obj T M P)

/-- All graph witnesses occur in antecedents. The finite-coverage antecedent
has a Sigma-one definition, so this invariant is Pi-one. -/
def formula : 𝚷₁.Semiformula M 1 :=
  let Gs : 𝚺₁.Semiformula M 2 := (chosenGraph T support).graph.rew Rew.emb
  let Gc : 𝚺₁.Semiformula M 2 := (chosenGraph T conclusion).graph.rew Rew.emb
  let Gp : 𝚺₁.Semiformula M 2 :=
    (chosenGraph T (prod.fst : P ⨯ Fm ⟶ P)).graph.rew Rew.emb
  let Gf : 𝚺₁.Semiformula M 2 :=
    (chosenGraph T (prod.snd : P ⨯ Fm ⟶ Fm)).graph.rew Rew.emb
  let Gv : 𝚺₁.Semiformula M 2 := (chosenGraph T v).graph.rew Rew.emb
  let Gt : 𝚺₁.Semiformula M 2 :=
    (chosenGraph T (Two.constant (P ⨯ Fm) true)).graph.rew Rew.emb
  let Cov := ArithmeticFiniteCoverage.formula (M := M)
  .mkPi “d. ∀ s f q b t, !Gs.val d s → !Gc.val d f →
    !Gp.val q &l.val → !Gf.val q f → !Cov.val s &l.val →
    !Gv.val q b → !Gt.val q t → b = t”

private theorem formula_eval_raw (d : M) :
    (formula T M support conclusion v l).val.Eval ![d] id ↔
      ∀ s f q b t : M,
        (chosenGraph T support).graph.val.Evalb ![d, s] →
        (chosenGraph T conclusion).graph.val.Evalb ![d, f] →
        (chosenGraph T (prod.fst : P ⨯ Fm ⟶ P)).graph.val.Evalb ![q, l.val] →
        (chosenGraph T (prod.snd : P ⨯ Fm ⟶ Fm)).graph.val.Evalb ![q, f] →
        ArithmeticFiniteCoverage.Covers s l.val →
        (chosenGraph T v).graph.val.Evalb ![q, b] →
        (chosenGraph T (Two.constant (P ⨯ Fm) true)).graph.val.Evalb ![q, t] → b = t := by
  simp [formula]

/-- The coded Pi-one formula states the full semantic truth invariant,
without restricting derivations, supports or formula codes to standard ones. -/
theorem formula_eval (d : Obj T M D) :
    (formula T M support conclusion v l).val.Eval ![d.val] id ↔
      (ArithmeticFiniteCoverage.Covers ((F T M).map support d).val l.val →
        TrueAt T M v l ((F T M).map conclusion d)) := by
  rw [formula_eval_raw]
  constructor
  · intro h hc q hp hf
    apply Subtype.ext
    exact h ((F T M).map support d).val ((F T M).map conclusion d).val q.val
      ((F T M).map v q).val ((F T M).map (Two.constant (P ⨯ Fm) true) q).val
      ((chosenGraph_map_iff T M support _ _).mpr rfl)
      ((chosenGraph_map_iff T M conclusion _ _).mpr rfl)
      ((chosenGraph_map_iff T M prod.fst _ _).mpr hp)
      ((chosenGraph_map_iff T M prod.snd _ _).mpr hf)
      hc ((chosenGraph_map_iff T M v _ _).mpr rfl)
      ((chosenGraph_map_iff T M (Two.constant (P ⨯ Fm) true) _ _).mpr rfl)
  · intro h s f q b t hs hf hp hq hc hb ht
    have ss := ((chosenGraph T support).support_model M _ _ hs).2
    have ff := ((chosenGraph T conclusion).support_model M _ _ hf).2
    have qq := ((chosenGraph T (prod.fst : P ⨯ Fm ⟶ P)).support_model M _ _ hp).1
    have bb := ((chosenGraph T v).support_model M _ _ hb).2
    have tt := ((chosenGraph T (Two.constant (P ⨯ Fm) true)).support_model M _ _ ht).2
    have hs' := (chosenGraph_map_iff T M support d ⟨s, ss⟩).mp hs
    have hf' := (chosenGraph_map_iff T M conclusion d ⟨f, ff⟩).mp hf
    have hp' := (chosenGraph_map_iff T M (prod.fst : P ⨯ Fm ⟶ P) ⟨q, qq⟩ l).mp hp
    have hq' := (chosenGraph_map_iff T M (prod.snd : P ⨯ Fm ⟶ Fm) ⟨q, qq⟩ ⟨f, ff⟩).mp hq
    have hb' := (chosenGraph_map_iff T M v ⟨q, qq⟩ ⟨b, bb⟩).mp hb
    have ht' := (chosenGraph_map_iff T M (Two.constant (P ⨯ Fm) true) ⟨q, qq⟩ ⟨t, tt⟩).mp ht
    have hc' : ArithmeticFiniteCoverage.Covers ((F T M).map support d).val l.val := by
      simpa only [hs'] using hc
    exact congrArg Subtype.val (hb'.symm.trans ((h hc' ⟨q, qq⟩ hp'
      (hq'.trans hf'.symm)).trans ht'))

/-- Internal rule induction with the finite-coverage truth property. The
step is checked on the actual typed rule objects and their ordered children. -/
theorem model_rule_induction {bound : ℕ} (R : RulePresentation Fm bound)
    (support : (SyntacticDerivation.derivationAlgebra T R).a.left ⟶ C)
    (step : ∀ (i : Fin (bound + 1))
      (r : Obj T M (R.ruleObject (SyntacticDerivation.derivationAlgebra T R).a i)),
      (∀ k : Fin i.val,
        ArithmeticFiniteCoverage.Covers
          ((F T M).map support ((F T M).map
            (SyntacticDerivation.StandardInduction.typedChild T R i k) r)).val l.val →
          TrueAt T M v l ((F T M).map (SyntacticDerivation.derivationAlgebra T R).a.hom
            ((F T M).map (SyntacticDerivation.StandardInduction.typedChild T R i k) r))) →
      ArithmeticFiniteCoverage.Covers
        ((F T M).map support ((F T M).map (SyntacticDerivation.derivationConstructor T R i) r)).val
        l.val →
      TrueAt T M v l ((F T M).map (SyntacticDerivation.derivationAlgebra T R).a.hom
        ((F T M).map (SyntacticDerivation.derivationConstructor T R i) r))) :
    ∀ d : Obj T M (SyntacticDerivation.derivationAlgebra T R).a.left,
      ArithmeticFiniteCoverage.Covers ((F T M).map support d).val l.val →
        TrueAt T M v l ((F T M).map (SyntacticDerivation.derivationAlgebra T R).a.hom d) := by
  have h := SyntacticDerivation.InternalInduction.model_rule_induction T M R
    (formula T M support (SyntacticDerivation.derivationAlgebra T R).a.hom v l) (by
      intro i r ih
      apply (formula_eval T M support _ v l _).mpr
      apply step i r
      intro k
      exact (formula_eval T M support _ v l _).mp (ih k))
  intro d
  exact (formula_eval T M support _ v l d).mp (h d)

end CoveredDerivationInvariant
end CategoricalEssentialIncompleteness.V46
