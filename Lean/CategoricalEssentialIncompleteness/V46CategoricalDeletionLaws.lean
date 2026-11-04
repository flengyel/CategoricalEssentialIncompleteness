/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalDeletionLawsBoolean

/-! # Membership after categorical deletion, by parameterized initiality -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

namespace StableListAlgebra

variable {V : D} (L : StableListAlgebra V) (E : DecidableVariables V)

@[simp] theorem deletion_nil_general {X : D} (y : X ⟶ V) :
    prod.lift y (terminal.from X ≫ L.algebra.nil) ≫ L.deletion E =
      terminal.from X ≫ L.algebra.nil := by
  simpa using congrArg (fun k => y ≫ k) (L.deletion_nil E)

@[simp] theorem deletion_cons_general {X : D} (y z : X ⟶ V)
    (w : X ⟶ L.algebra.carrier) :
    prod.lift y (prod.lift z w ≫ L.algebra.cons) ≫ L.deletion E =
      Two.branch (prod.lift y z ≫ E.test)
        (prod.lift z (prod.lift y w ≫ L.deletion E) ≫ L.algebra.cons)
        (prod.lift y w ≫ L.deletion E) := by
  simpa [branch_natural] using
    congrArg (fun k => prod.lift y (prod.lift z w) ≫ k) (L.deletion_cons E)

@[simp] theorem deletion_cons_arrow {X : D} (y : X ⟶ V)
    (p : X ⟶ V ⨯ L.algebra.carrier) :
    prod.lift y (p ≫ L.algebra.cons) ≫ L.deletion E =
      Two.branch (prod.lift y (p ≫ prod.fst) ≫ E.test)
        (prod.lift (p ≫ prod.fst)
          (prod.lift y (p ≫ prod.snd) ≫ L.deletion E) ≫ L.algebra.cons)
        (prod.lift y (p ≫ prod.snd) ≫ L.deletion E) := by
  simpa using L.deletion_cons_general E y (p ≫ prod.fst) (p ≫ prod.snd)

@[simp] theorem membership_branch {X : D} (x : X ⟶ V) (b : X ⟶ Two D)
    (w₀ w₁ : X ⟶ L.algebra.carrier) :
    prod.lift x (Two.branch b w₀ w₁) ≫ L.membership E =
      Two.branch b (prod.lift x w₀ ≫ L.membership E)
        (prod.lift x w₁ ≫ L.membership E) := by
  apply Two.hom_ext b
  · simp only [prod.comp_lift_assoc, Two.fiberι_branch, Bool.false_eq_true, ↓reduceIte]
  · simp only [prod.comp_lift_assoc, Two.fiberι_branch, ↓reduceIte]

/-- The Appendix A.2 deletion identity on the parameter source `(x,y,w)`. -/
theorem membership_deletion_parameter :
    prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ L.deletion E) ≫ L.membership E =
      Two.binary Bool.and (Two.unary Bool.not (prod.fst ≫ E.test))
        (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ L.membership E) := by
  let n := Two.constant (V ⨯ V) false
  let c : (V ⨯ V) ⨯ (V ⨯ Two D) ⟶ Two D :=
    Two.branch (prod.lift (prod.fst ≫ prod.snd) (prod.snd ≫ prod.fst) ≫ E.test)
      (Two.binary Bool.or
        (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.fst) ≫ E.test)
        (prod.snd ≫ prod.snd))
      (prod.snd ≫ prod.snd)
  let f : (V ⨯ V) ⨯ L.algebra.carrier ⟶ Two D :=
    prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ L.deletion E) ≫ L.membership E
  let g : (V ⨯ V) ⨯ L.algebra.carrier ⟶ Two D :=
    Two.binary Bool.and (Two.unary Bool.not (prod.fst ≫ E.test))
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ L.membership E)
  change f = g
  have hf : f = L.parameterFold n c := by
    apply L.parameterFold_unique n c f
    · simp [f, n, parameterNil]
    · simp [f, c, parameterCons, parameterRec, branch_natural,
        -prod.lift_fst_comp_snd_comp]
  have hg : g = L.parameterFold n c := by
    apply L.parameterFold_unique n c g
    · suffices h : Two.binary Bool.and
          (Two.unary Bool.not (E.test : V ⨯ V ⟶ Two D))
          (Two.constant (V ⨯ V) false) = n by
        simpa [g, parameterNil] using h
      exact inf_bot_eq _
    · simpa [g, c, parameterCons, parameterRec, branch_natural,
        -prod.lift_fst_comp_snd_comp] using
        (E.deletion_boolean_step
          (prod.fst ≫ prod.fst : (V ⨯ V) ⨯ (V ⨯ L.algebra.carrier) ⟶ V)
          (prod.fst ≫ prod.snd) (prod.snd ≫ prod.fst)
          (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.snd) ≫ L.membership E)).symm
  exact hf.trans hg.symm

/-- The manuscript identity with arbitrary generalized elements;
the deleted name and the tested name retain their original roles. -/
theorem membership_deletion {X : D} (x y : X ⟶ V)
    (w : X ⟶ L.algebra.carrier) :
    prod.lift x (prod.lift y w ≫ L.deletion E) ≫ L.membership E =
      Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ E.test))
        (prod.lift x w ≫ L.membership E) := by
  simpa using congrArg (fun k => prod.lift (prod.lift x y) w ≫ k)
    (L.membership_deletion_parameter E)

end StableListAlgebra

end CategoricalEssentialIncompleteness.V46
