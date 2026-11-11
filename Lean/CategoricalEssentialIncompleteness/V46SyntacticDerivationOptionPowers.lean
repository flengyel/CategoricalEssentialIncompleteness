/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import CategoricalEssentialIncompleteness.V46Inference
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution

/-! Total option collection for the finite ordered premise powers. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionPowers
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

def pair (A B : D) : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ OptionSyntax.obj (A ⨯ B) :=
  SumFibers.caseOf (prod.fst : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ _)
    OptionSyntax.fail
    (SumFibers.caseOf
      (pullback.fst (prod.fst : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ _) coprod.inr ≫ prod.snd)
      OptionSyntax.fail
      (prod.lift
        (pullback.fst _ coprod.inr ≫ pullback.snd
          (prod.fst : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ _) coprod.inr)
        (pullback.snd _ coprod.inr) ≫ coprod.inr))

theorem pair_some (A B : D) :
    prod.map (coprod.inr : A ⟶ OptionSyntax.obj A) (coprod.inr : B ⟶ OptionSyntax.obj B) ≫
      pair A B = coprod.inr := by
  let k := prod.map (coprod.inr : A ⟶ OptionSyntax.obj A) (coprod.inr : B ⟶ OptionSyntax.obj B)
  let t := (prod.fst : OptionSyntax.obj A ⨯ OptionSyntax.obj B ⟶ OptionSyntax.obj A)
  have hk : k ≫ t = prod.fst ≫ coprod.inr := by simp [k, t]
  let l := pullback.lift k prod.fst hk
  change k ≫ SumFibers.caseOf t _ _ = _
  rw [SumFibers.comp_caseOf_inr t _ _ k prod.fst hk]
  have hl : l ≫ (pullback.fst t coprod.inr ≫ prod.snd) = prod.snd ≫ coprod.inr := by
    simp [l, k]
  change l ≫ SumFibers.caseOf (pullback.fst t coprod.inr ≫ prod.snd) _ _ = _
  rw [SumFibers.comp_caseOf_inr _ _ _ l prod.snd hl]
  simp [l, k, t, prod.comp_lift_assoc]

def collect (Q : D) : (n : ℕ) → finitePower (OptionSyntax.obj Q) n ⟶
    OptionSyntax.obj (finitePower Q n)
  | 0 => coprod.inr
  | 1 => 𝟙 _
  | n + 2 => prod.map (collect Q (n + 1)) (𝟙 _) ≫ pair (finitePower Q (n + 1)) Q

@[simp, reassoc] theorem collect_some (Q : D) (n : ℕ) :
    finitePowerMap (coprod.inr : Q ⟶ OptionSyntax.obj Q) n ≫ collect Q n = coprod.inr := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    cases n with
    | zero => exact Category.comp_id _
    | succ n =>
      change prod.map _ _ ≫ (prod.map _ _ ≫ _) = _
      rw [← Category.assoc, prod.map_map, ih, Category.comp_id, pair_some]
      rfl

/-- A partial root operation is extended to a total option operation;
the only new branch is failure of its collected children. -/
def liftRoot {A Q Z : D} (h : A ⨯ Q ⟶ OptionSyntax.obj Z) :
    A ⨯ OptionSyntax.obj Q ⟶ OptionSyntax.obj Z :=
  SumFibers.caseOf (prod.snd : A ⨯ OptionSyntax.obj Q ⟶ OptionSyntax.obj Q)
    OptionSyntax.fail
    (prod.lift (pullback.fst _ coprod.inr ≫ prod.fst)
      (pullback.snd _ coprod.inr) ≫ h)

@[simp, reassoc] theorem liftRoot_some {A Q Z : D} (h : A ⨯ Q ⟶ OptionSyntax.obj Z) :
    prod.map (𝟙 A) (coprod.inr : Q ⟶ OptionSyntax.obj Q) ≫ liftRoot h = h := by
  unfold liftRoot
  rw [SumFibers.comp_caseOf_inr _ _ _ _ prod.snd (by simp)]
  simp [prod.comp_lift_assoc]

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionPowers
