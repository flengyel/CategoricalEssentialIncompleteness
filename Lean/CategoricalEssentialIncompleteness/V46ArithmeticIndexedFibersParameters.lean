/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersInference
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedRules

/-! # Parameter-preserving restriction of the actual finite inference data

Every child keeps its own formula coordinate. Only its external parameter
is identified with that of its rule instance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {E F P : D} (R : RulePresentation (E ⨯ F) 2)

structure ParameterPreserving : Prop where
  unary : R.premises 1 ≫ prod.fst = R.conclusion 1 ≫ prod.fst
  binary_first : R.premises 2 ≫ prod.fst ≫ prod.fst = R.conclusion 2 ≫ prod.fst
  binary_second : R.premises 2 ≫ prod.snd ≫ prod.fst = R.conclusion 2 ≫ prod.fst

variable (m : P ⟶ E)

def parameterRule (i : Fin 3) : D := pullback (R.conclusion i ≫ prod.fst) m

def parameterRuleConclusion (i : Fin 3) : parameterRule R m i ⟶ P ⨯ F :=
  prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.conclusion i ≫ prod.snd)

/-- Restriction changes coefficient objects by the actual parameter
pullbacks and repeats that same parameter in each ordered premise. -/
def parameterRules : RulePresentation (P ⨯ F) 2 where
  instances := parameterRule R m
  premises := Fin.cases (terminal.from _)
    (Fin.cases (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.premises 1 ≫ prod.snd))
      (Fin.cases
        (prod.lift
          (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.premises 2 ≫ prod.fst ≫ prod.snd))
          (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.premises 2 ≫ prod.snd ≫ prod.snd)))
        (fun i => Fin.elim0 i)))
  conclusion := parameterRuleConclusion R m

omit [FinitaryExtensive D] in
/-- The conclusion parameter pullback is also the full conclusion
square after retaining its original formula coordinate. -/
theorem parameterRuleSquare (i : Fin 3) :
    IsPullback (pullback.fst (R.conclusion i ≫ prod.fst) m)
      (parameterRuleConclusion R m i) (R.conclusion i) (prod.map m (𝟙 F)) := by
  have hw : pullback.fst (R.conclusion i ≫ prod.fst) m ≫ R.conclusion i =
      parameterRuleConclusion R m i ≫ prod.map m (𝟙 F) := by
    apply prod.hom_ext
    · simpa [parameterRuleConclusion,Category.assoc] using
        (pullback.condition (f := R.conclusion i ≫ prod.fst) (g := m))
    · simp [parameterRuleConclusion]
  have outer : IsPullback (pullback.fst (R.conclusion i ≫ prod.fst) m)
      (parameterRuleConclusion R m i ≫ prod.fst) (R.conclusion i ≫ prod.fst) m := by
    simpa only [parameterRuleConclusion,prod.lift_fst] using
      (IsPullback.of_hasPullback (R.conclusion i ≫ prod.fst) m)
  exact outer.of_bot hw (IsPullback.of_prod_fst_with_id m F).flip

/-- These are the two printed shared-parameter equations, used to derive
the premise comparison; no fiber comparison is assumed. -/
def parameterRuleData (h : ParameterPreserving R) :
    RuleBaseChange.Data (prod.map m (𝟙 F)) (parameterRules R m) R where
  instanceMap i := pullback.fst (R.conclusion i ≫ prod.fst) m
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.premises 1 ≫ prod.snd)) ≫
          prod.map m (𝟙 F) = pullback.fst _ _ ≫ R.premises 1
      apply prod.hom_ext
      · simp only [Category.assoc,prod.map_fst,prod.lift_fst_assoc]
        rw [h.unary]
        exact (pullback.condition (f := R.conclusion 1 ≫ prod.fst) (g := m)).symm
      · simp
    · change (prod.lift
          (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.premises 2 ≫ prod.fst ≫ prod.snd))
          (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ R.premises 2 ≫ prod.snd ≫ prod.snd))) ≫
        prod.map (prod.map m (𝟙 F)) (prod.map m (𝟙 F)) = pullback.fst _ _ ≫ R.premises 2
      apply prod.hom_ext
      · apply prod.hom_ext
        · simp only [Category.assoc,prod.map_fst,prod.lift_fst_assoc]
          change pullback.snd (R.conclusion 2 ≫ prod.fst) m ≫ m =
            pullback.fst (R.conclusion 2 ≫ prod.fst) m ≫ R.premises 2 ≫ prod.fst ≫ prod.fst
          have he := congrArg (fun k => pullback.fst (R.conclusion 2 ≫ prod.fst) m ≫ k) h.binary_first
          exact ((pullback.condition (f := R.conclusion 2 ≫ prod.fst) (g := m)).symm).trans
            (by simpa only [Category.assoc] using he.symm)
        · simp; rfl
      · apply prod.hom_ext
        · simp only [Category.assoc,prod.map_snd,prod.lift_snd_assoc,prod.map_fst,prod.lift_fst_assoc]
          change pullback.snd (R.conclusion 2 ≫ prod.fst) m ≫ m =
            pullback.fst (R.conclusion 2 ≫ prod.fst) m ≫ R.premises 2 ≫ prod.snd ≫ prod.fst
          have he := congrArg (fun k => pullback.fst (R.conclusion 2 ≫ prod.fst) m ≫ k) h.binary_second
          exact ((pullback.condition (f := R.conclusion 2 ≫ prod.fst) (g := m)).symm).trans
            (by simpa only [Category.assoc] using he.symm)
        · simp; rfl
  conclusion := parameterRuleSquare R m

/-- Actual parameter preservation of the family rules, including the two
distinct MP conclusions. -/
theorem familyParameterPreserving (E : D) {V L S A : D}
    (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ E ⨯ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) :
    ParameterPreserving (ArithmeticIndexedRules.rules E logical sentence axioms all imp) :=
  ⟨ArithmeticIndexedRules.unary_parameter E logical sentence axioms all imp,
    ArithmeticIndexedRules.binary_first_parameter E logical sentence axioms all imp,
    ArithmeticIndexedRules.binary_second_parameter E logical sentence axioms all imp⟩

/-- The complement's inference functor is the actual coefficient
restriction prescribed in the manuscript, with derived base change. -/
def parameterInferenceComparison (h : ParameterPreserving R) :
    R.inference ⋙ Over.pullback (prod.map m (𝟙 F)) ≅
      Over.pullback (prod.map m (𝟙 F)) ⋙ (parameterRules R m).inference :=
  RuleBaseChange.comparison _ _ _ (parameterRuleData R m h)

/-- Equality of the original base morphisms induces the actual pullback
functor comparison, independently of their chosen graph expressions. -/
def pullbackEqIso {A B : D} {f g : A ⟶ B} (h : f = g) :
    Over.pullback f ≅ Over.pullback g := by
  cases h
  exact Iso.refl _

def parameterInferenceComparisonAlong (h : ParameterPreserving R)
    (k : P ⨯ F ⟶ E ⨯ F) (hk : k = prod.map m (𝟙 F)) :
    R.inference ⋙ Over.pullback k ≅ Over.pullback k ⋙ (parameterRules R m).inference :=
  Functor.isoWhiskerLeft R.inference (pullbackEqIso hk) ≪≫
    parameterInferenceComparison R m h ≪≫
      Functor.isoWhiskerRight (pullbackEqIso hk).symm (parameterRules R m).inference

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
