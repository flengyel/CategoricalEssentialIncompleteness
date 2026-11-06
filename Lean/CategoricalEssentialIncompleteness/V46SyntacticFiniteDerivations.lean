/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivationsPowers

/-! # Explicit finite typed derivations and the constructed proof object

The external tree retains the original rule label and its own ordered
premise conclusions. Interpretation uses the actual rule-input pullback.
The converse on standard codes uses the proved arithmetic size induction,
not preservation of initial algebras by the model functor.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
open SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable {Fm : PredicateCategory T} {bound : ℕ} (R : RulePresentation Fm bound)

/-- Each node is an original rule instance, with independently typed
children at exactly its prescribed ordered premises. -/
inductive Derives : Obj T M Fm → Prop
  | node (i : Fin (bound + 1)) (r : Obj T M (R.instances i))
      (children : ∀ k : Fin i.val,
        Derives ((F T M).map (R.premises i ≫ finiteChild T Fm i.val k) r)) :
      Derives ((F T M).map (R.conclusion i) r)

/-- Every external finite derivation is realized by a genuine point
of the constructed Sigma-one proof carrier. -/
theorem realizes {φ : Obj T M Fm} (h : Derives T M R φ) :
    ∃ p : Obj T M (derivationAlgebra T R).a.left,
      (F T M).map (derivationAlgebra T R).a.hom p = φ := by
  induction h with
  | node i r _children ih =>
      choose p hp using ih
      obtain ⟨tuple,htuple⟩ := powerPoints_exists T M (derivationAlgebra T R).a.left i.val p
      have hm : (F T M).map (R.premises i) r =
          (F T M).map (finitePowerMap (derivationAlgebra T R).a.hom i.val) tuple := by
        apply powerPoints_ext T M Fm i.val
        intro k
        calc
          _ = (F T M).map (R.premises i ≫ finiteChild T Fm i.val k) r :=
            ((F T M).map_comp_apply _ _ r).symm
          _ = (F T M).map (derivationAlgebra T R).a.hom (p k) := (hp k).symm
          _ = (F T M).map (derivationAlgebra T R).a.hom
              ((F T M).map (finiteChild T (derivationAlgebra T R).a.left i.val k) tuple) :=
            congrArg ((F T M).map (derivationAlgebra T R).a.hom) (htuple k).symm
          _ = _ := by
            have hn := congrArg (fun f => (F T M).map f tuple)
              (finiteChild_natural T (derivationAlgebra T R).a.hom i.val k)
            simpa only [Functor.map_comp_apply] using hn.symm
      obtain ⟨input,hr,_⟩ := Types.exists_of_isPullback
        ((IsPullback.of_hasPullback (R.premises i)
          (finitePowerMap (derivationAlgebra T R).a.hom i.val)).map (F T M)) r tuple hm
      refine ⟨(F T M).map (derivationConstructor T R i) input,?_⟩
      erw [← Functor.map_comp_apply,derivationConstructor_conclusion,
        RulePresentation.ruleConclusion,Functor.map_comp_apply]
      exact congrArg ((F T M).map (R.conclusion i)) hr

end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
