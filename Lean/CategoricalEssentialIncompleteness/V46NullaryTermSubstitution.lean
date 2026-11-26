/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxTerms
public import CategoricalEssentialIncompleteness.V46CategoricalVariableSubstitution
public import CategoricalEssentialIncompleteness.V46StableListComparison
public import CategoricalEssentialIncompleteness.V46VariableTests

/-! # Term substitution under interpretation of propositional atoms -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

def substitutionParameterMap : S.substitutionParameters ⟶ Q.substitutionParameters :=
  prod.map (𝟙 V) (interpretation S Q f).1

@[reassoc (attr := simp)] theorem substitutionParameterMap_fst :
    substitutionParameterMap S Q f ≫ prod.fst = prod.fst := by
  simp [substitutionParameterMap]

@[reassoc (attr := simp)] theorem substitutionParameterMap_snd :
    substitutionParameterMap S Q f ≫ prod.snd = prod.snd ≫ (interpretation S Q f).1 := by
  simp [substitutionParameterMap]

theorem term_substitution_value {Z : D} (t : Z ⟶ S.algebra.a.1)
    (p : Z ⟶ S.substitutionParameters) :
    prod.lift t p ≫ S.termSubstitution ≫ (interpretation S Q f).1 =
      prod.lift (t ≫ (interpretation S Q f).1) (p ≫ substitutionParameterMap S Q f) ≫
        Q.termSubstitution := by
  let y := t ≫ (variableIso S).inv
  have hy : y ≫ S.variableConstructor = t := by
    change (t ≫ (variableIso S).inv) ≫ (variableIso S).hom = t
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hyQ : y ≫ Q.variableConstructor = t ≫ (interpretation S Q f).1 := by
    rw [← variable_law S Q f, ← Category.assoc, hy]
  let b := prod.lift y (p ≫ prod.fst) ≫ S.decidableVariables.test
  have hS : prod.lift t p ≫ S.termSubstitution ≫ (interpretation S Q f).1 =
      Two.branch b (t ≫ (interpretation S Q f).1)
        (p ≫ prod.snd ≫ (interpretation S Q f).1) := by
    have h := congrArg (fun k => k ≫ (interpretation S Q f).1)
      (S.variable_substitution p y)
    rw [StableListAlgebra.Comparison.branch_postcomp] at h
    simpa only [hy, Category.assoc] using h
  have hQ : prod.lift (t ≫ (interpretation S Q f).1)
        (p ≫ substitutionParameterMap S Q f) ≫ Q.termSubstitution =
      Two.branch b (t ≫ (interpretation S Q f).1)
        (p ≫ prod.snd ≫ (interpretation S Q f).1) := by
    have h := Q.variable_substitution (p ≫ substitutionParameterMap S Q f) y
    have hE := S.decidableVariables.unique Q.decidableVariables
    simpa only [hyQ, Category.assoc, substitutionParameterMap_fst,
      substitutionParameterMap_snd, b, hE] using h
  exact hS.trans hQ.symm

theorem term_substitution : S.termSubstitution ≫ (interpretation S Q f).1 =
    prod.map (interpretation S Q f).1 (substitutionParameterMap S Q f) ≫ Q.termSubstitution := by
  have h := term_substitution_value S Q f prod.fst prod.snd
  simpa only [prod.lift_fst_snd, Category.id_comp, ← prod.lift_map] using h

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
