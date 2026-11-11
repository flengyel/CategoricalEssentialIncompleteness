/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry
public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation

/-! # The actual mapped PA inference signature

Only the arithmetic interpretation functor's proved finite-limit
preservation is used. No preservation of initial algebras is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open NumericalArithmetic
abbrev K := numericalInterpretation

/-- Ordered powers include the chosen nullary terminal object. -/
def finitePowerIso (X : PredicateCategory 𝗣𝗔) :
    (n : ℕ) → K.obj (finitePower X n) ≅ finitePower (K.obj X) n
  | 0 => asIso (terminalComparison K)
  | 1 => Iso.refl _
  | n + 2 => asIso (prodComparison K (finitePower X (n+1)) X) ≪≫
      prod.mapIso (finitePowerIso X (n+1)) (Iso.refl _)

@[reassoc] theorem finitePowerIso_natural {X Y : PredicateCategory 𝗣𝗔} (f : X ⟶ Y) (n : ℕ) :
    K.map (finitePowerMap f n) ≫ (finitePowerIso Y n).hom =
      (finitePowerIso X n).hom ≫ finitePowerMap (K.map f) n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
      cases n with
      | zero => simp only [finitePowerIso,finitePowerMap,Iso.refl_hom,Category.comp_id,Category.id_comp]
      | succ n =>
          simp only [finitePowerIso,Iso.trans_hom,asIso_hom,prod.mapIso_hom,Iso.refl_hom,finitePowerMap]
          rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,ih]
          simp [prod.map_map]

variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

/-- The coefficients and conclusions are the actual source images;
premises use the canonical ordered finite-power comparison. -/
def interpretedRules : RulePresentation (K.obj F) N where
  instances i := K.obj (R.instances i)
  premises i := K.map (R.premises i) ≫ (finitePowerIso F i.val).hom
  conclusion i := K.map (R.conclusion i)

abbrev overFunctor (_R : RulePresentation F N) : Over F ⥤ Over (K.obj F) := Over.post K

theorem input_square (Q : Over F) (i : Fin (N+1)) :
    IsPullback
      (K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)))
      (K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso Q.left i.val).hom)
      ((interpretedRules R).premises i) (finitePowerMap (K.map Q.hom) i.val) := by
  apply ((IsPullback.of_hasPullback (R.premises i) (finitePowerMap Q.hom i.val)).map K).of_iso
    (Iso.refl _) (Iso.refl _) (finitePowerIso Q.left i.val) (finitePowerIso F i.val)
  · simp
  · simp
  · simp only [Iso.refl_hom,Category.id_comp,interpretedRules]
  · exact finitePowerIso_natural Q.hom i.val

def inputIso (Q : Over F) (i : Fin (N+1)) :
    K.obj (R.ruleObject Q i) ≅ (interpretedRules R).ruleObject ((overFunctor R).obj Q) i :=
  (input_square R Q i).isoPullback

@[simp,reassoc] theorem inputIso_fst (Q : Over F) (i : Fin (N+1)) :
    (inputIso R Q i).hom ≫ pullback.fst _ _ =
      K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) :=
  (input_square R Q i).isoPullback_hom_fst

@[simp,reassoc] theorem inputIso_snd (Q : Over F) (i : Fin (N+1)) :
    (inputIso R Q i).hom ≫ pullback.snd _ _ =
      K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso Q.left i.val).hom :=
  (input_square R Q i).isoPullback_hom_snd

/-- A coefficient image is unary and its tuple code is the source label itself. -/
theorem coefficient_labels (C : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (NumericalSyntaxTreeChart.E.inverse.obj (K.obj C)).val.Evalb (M := ℕ) ![n] ↔
      C.val.Evalb (M := ℕ) ![n] := by
  apply (NumericalCoordinates.codedPredicate_eval (K.obj C) n).trans
  change (∃ x : ℕ, C.val.Evalb (M := ℕ) ![x] ∧ x = n) ↔ C.val.Evalb (M := ℕ) ![n]
  simp

theorem interpreted_rule_labels (i : Fin (N+1)) (n : ℕ) :
    (NumericalSyntaxTreeChart.E.inverse.obj
      (SyntacticDerivation.PolynomialComparison.coefficients (interpretedRules R) i.val)).val.Evalb
        (M := ℕ) ![n] ↔ (R.instances i).val.Evalb (M := ℕ) ![n] := by
  rw [SyntacticDerivation.PolynomialComparison.coefficients_fin]
  exact coefficient_labels (R.instances i) n

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
