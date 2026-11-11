/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOriginalInputs
public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution

/-! A rule operation extended by failure exactly at a decidable premise mismatch. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.CheckedRoot
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {F : D} {N : ℕ} (R : RulePresentation F N) (Q : Over F) (i : Fin (N + 1))
variable (E : DecidableVariables (finitePower F i.val))

def test : R.instances i ⨯ finitePower Q.left i.val ⟶ Two D :=
  prod.lift (prod.fst ≫ R.premises i) (prod.snd ≫ finitePowerMap Q.hom i.val) ≫ E.test

def matchingMap : R.ruleObject Q i ⟶ R.instances i ⨯ finitePower Q.left i.val :=
  prod.lift (pullback.fst _ _) (pullback.snd _ _)

theorem matching_test : matchingMap R Q i ≫ test R Q i E =
    Two.constant (R.ruleObject Q i) true := by
  simp only [matchingMap, test, ← Category.assoc, prod.comp_lift, prod.lift_fst,
    prod.lift_snd]
  exact (E.test_true_iff _ _).mpr pullback.condition

def matchingToTrue : R.ruleObject Q i ⟶ pullback (test R Q i E) coprod.inr :=
  pullback.lift (matchingMap R Q i) (terminal.from _) (matching_test R Q i E)

def trueToMatching : pullback (test R Q i E) coprod.inr ⟶ R.ruleObject Q i :=
  pullback.lift (pullback.fst _ coprod.inr ≫ prod.fst)
    (pullback.fst _ coprod.inr ≫ prod.snd) (by
      apply (E.test_true_iff _ _).mp
      simp only [Category.assoc]
      rw [← prod.comp_lift_assoc]
      change pullback.fst (test R Q i E) coprod.inr ≫ test R Q i E = _
      rw [pullback.condition]
      congr 1
      exact Subsingleton.elim _ _)

def matchingIso : R.ruleObject Q i ≅ pullback (test R Q i E) coprod.inr where
  hom := matchingToTrue R Q i E
  inv := trueToMatching R Q i E
  hom_inv_id := by
    apply pullback.hom_ext
    · simp [matchingToTrue, trueToMatching, matchingMap]
    · simp [matchingToTrue, trueToMatching, matchingMap]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [matchingToTrue, Category.assoc, pullback.lift_fst, trueToMatching,
        matchingMap, prod.comp_lift, pullback.lift_fst, pullback.lift_snd]
      rw [← prod.comp_lift, prod.lift_fst_snd, Category.comp_id, Category.id_comp]
    · exact Subsingleton.elim _ _

variable {Z : D} (h : R.ruleObject Q i ⟶ Z)

/-- Both branches have typed sources.  Failure tests the equality of two
computed premise tuples; it does not test rule-label membership. -/
def operation : R.instances i ⨯ finitePower Q.left i.val ⟶ OptionSyntax.obj Z :=
  SumFibers.caseOf (test R Q i E) OptionSyntax.fail
    ((matchingIso R Q i E).inv ≫ h ≫ coprod.inr)

@[simp, reassoc] theorem operation_matching :
    matchingMap R Q i ≫ operation R Q i E h = h ≫ coprod.inr := by
  unfold operation
  rw [SumFibers.comp_caseOf_inr _ _ _ _ (terminal.from _) (matching_test R Q i E)]
  change (matchingIso R Q i E).hom ≫ ((matchingIso R Q i E).inv ≫ h ≫ coprod.inr) = _
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The success domain is the original rule-input pullback, including
arity zero and arbitrary, independently varying premise conclusions. -/
theorem operation_isPullback :
    IsPullback (matchingMap R Q i) h (operation R Q i E h) coprod.inr := by
  have hv := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (coprodIsCoprod (⊤_ D) Z))
    (BinaryCofan.mk (pullback.fst (test R Q i E) coprod.inl)
      (pullback.fst (test R Q i E) coprod.inr))
  have hp : IsPullback (pullback.fst (test R Q i E) coprod.inr)
      ((matchingIso R Q i E).inv ≫ h) (operation R Q i E h) coprod.inr :=
    ((hv (terminal.from _) ((matchingIso R Q i E).inv ≫ h) (operation R Q i E h)
      (SumFibers.inl_caseOf _ _ _).symm
      (by simpa only [BinaryCofan.mk_inr, Category.assoc, operation] using
        (SumFibers.inr_caseOf (test R Q i E) OptionSyntax.fail
          ((matchingIso R Q i E).inv ≫ h ≫ coprod.inr)).symm)).mp
        ⟨SumFibers.isColimit (test R Q i E)⟩).2
  apply hp.of_iso' (matchingIso R Q i E) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [matchingIso, matchingToTrue]
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  · simp
  · simp

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.CheckedRoot
