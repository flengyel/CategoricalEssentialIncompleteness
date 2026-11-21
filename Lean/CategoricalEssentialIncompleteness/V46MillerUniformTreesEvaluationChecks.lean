/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerUniformTreesEvaluation


/-! # Selected finite positive operation records -/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
variable {P : Uniform.Family}
variable (step : Input → Part ℕ) (initial steps : ℕ → ℕ)

example : Primrec₂ callAt := callAt_primrec
example : Primrec calls := calls_primrec
example (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
    (hi : Computable initial) :
    Uniform.Enumerable P (fun a : RecordInput => Record step initial a.1.1 a.1.2 a.2) :=
  record_enumerable step initial hs hi
example (x : ℕ) : Record step initial x 0 [initial x] := record_zero step initial x
example {x n : ℕ} {states : List ℕ} (h : Record step initial x n states)
    {new : ℕ} (hn : new ∈ step (x,(n,states.getD n 0))) :
    Record step initial x (n+1) (states ++ [new]) := record_append step initial h hn
example {x n : ℕ} {left right : List ℕ}
    (hl : Record step initial x n left) (hr : Record step initial x n right) : left=right :=
  record_states_unique step initial hl hr
example (hs : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat step)
    (hi : Computable initial) (hn : Computable steps) :
    ∃ e : ℕ,∀ p ∈ P.oracles,∀ x y,
      y ∈ run step initial steps x ↔ y ∈ OracleProgram.numberedEval e p x :=
  run_represented step initial steps hs hi hn
example (x : ℕ) :
    (run step initial steps x).Dom ↔ ∃ states,Record step initial x (steps x) states :=
  run_domain step initial steps x
example (A : Set ℕ) (I : ℕ → ℕ → ℕ → Prop)
    (hz : ∀ x ∈ A,I x 0 (initial x))
    (ht : ∀ x ∈ A,∀ i < steps x,∀ v,I x i v →
      ∃ w,w ∈ step (x,(i,v)) ∧ I x (i+1) w) :
    ∀ x ∈ A,(run step initial steps x).Dom := run_total_on step initial steps A I hz ht
end CategoricalEssentialIncompleteness.V46.Miller.UniformTrees
