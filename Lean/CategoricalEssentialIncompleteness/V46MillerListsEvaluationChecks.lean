/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerListsEvaluation


/-! # Positive value records for arbitrary uniform list algebras -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X : Over R} (V : Total.Carrier P)
variable (h0 : Syntax.Raw.object R X X .unit ⟶ X)
variable (hc : Syntax.Raw.object R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ X)
example : Uniform.Enumerable P (fun a : (ℕ × List ℕ) × ℕ => Lists.Evaluates V h0 hc a.1.1 a.1.2 a.2) :=
  Lists.evaluates_enumerable V h0 hc
example (r : ℕ) (L : List ℕ) (hr : r ∈ R.obj.support) (hL : ∀ a ∈ L,a ∈ V.support) :
    ∃ v,Lists.Evaluates V h0 hc r L v := Lists.evaluates_exists V h0 hc r L hr hL
example {r v w : ℕ} {L : List ℕ} (hv : Lists.Evaluates V h0 hc r L v) (hw : Lists.Evaluates V h0 hc r L w) :
    v=w := Lists.evaluates_functional V h0 hc hv hw
