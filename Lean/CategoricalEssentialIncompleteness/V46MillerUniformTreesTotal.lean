/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerUniformTreesEvaluation
import CategoricalEssentialIncompleteness.V46MillerTotalProducts

/-! # The constructed positive-record evaluator is a total carrier morphism

Its support is the supplied valid-input carrier. Transition hypotheses
express the invariant/totality argument for the actual supplied algebra;
they do not assume a fold or its universal property.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
namespace CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
variable {P : Uniform.Family}
variable (step : Input → Part ℕ) (initial steps : ℕ → ℕ)
variable (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
variable (hi : Computable initial) (hn : Computable steps)
variable (X Y : Total.Carrier P) (I : ℕ → ℕ → ℕ → Prop)
variable (hz : ∀ x ∈ X.support,I x 0 (initial x))
variable (ht : ∀ x ∈ X.support,∀ i < steps x,∀ v,I x i v →
  ∃ w,w ∈ step (x,(i,v)) ∧ I x (i+1) w)
variable (hout : ∀ x ∈ X.support,∀ y,I x (steps x) y → y ∈ Y.support)

def foldArrow : X ⟶ Y :=
  let r : Uniform.N P ⟶ Uniform.N P := ⟨run step initial steps,run_represented step initial steps hs hi hn⟩
  let k := Uniform.identityOn (Uniform.N P) X.support X.enumerable ≫ r
  Total.arrow k.val k.represented (by
    intro x y hy
    obtain ⟨u,hu,_⟩ := Part.mem_bind_iff.mp hy
    exact ((Total.mem_supportIdentity X.support x u).mp hu).1) (by
    intro x y hy
    obtain ⟨u,hu,huy⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨hx,hux⟩ := (Total.mem_supportIdentity X.support x u).mp hu
    subst u
    exact hout x hx y (run_output_invariant step initial steps X.support I hz ht hx huy))

theorem mem_foldArrow (x y : ℕ) :
    y ∈ Total.val (foldArrow step initial steps hs hi hn X Y I hz ht hout) x ↔
      x ∈ X.support ∧ y ∈ run step initial steps x := by
  change y ∈ (Total.supportIdentity X.support x).bind (run step initial steps) ↔ _
  simp only [Part.mem_bind_iff,Total.mem_supportIdentity]
  aesop

theorem foldArrow_total : isTotal (foldArrow step initial steps hs hi hn X Y I hz ht hout) := by
  apply (Total.total_iff _).mpr
  intro x hx
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp (run_total_on step initial steps X.support I hz ht x hx)
  exact Part.dom_iff_mem.mpr ⟨y,(mem_foldArrow step initial steps hs hi hn X Y I hz ht hout x y).mpr ⟨hx,hy⟩⟩

def totalFold : (⟨X⟩ : Total.TotalCategory P) ⟶ ⟨Y⟩ :=
  ⟨foldArrow step initial steps hs hi hn X Y I hz ht hout,
    foldArrow_total step initial steps hs hi hn X Y I hz ht hout⟩

theorem totalFold_graph (x y : ℕ) :
    y ∈ Total.val (totalFold step initial steps hs hi hn X Y I hz ht hout).hom x ↔
      x ∈ X.support ∧ ∃ states,Record step initial x (steps x) states ∧ states.getD (steps x) 0 = y := by
  exact (mem_foldArrow step initial steps hs hi hn X Y I hz ht hout x y).trans
    (and_congr_right (fun _ => mem_run step initial steps x y))

end CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
