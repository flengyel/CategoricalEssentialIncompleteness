/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax
public import CategoricalEssentialIncompleteness.TwoBoolean

/-! # Membership and deletion as categorical folds with parameters -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

/-- The coefficient of the cons step, read from a product in the slice. -/
def listStepHead (P V X : D) :
    (constantFamily P V ⨯ constantFamily P X).left ⟶ V :=
  (prod.fst : constantFamily P V ⨯ constantFamily P X ⟶
    constantFamily P V).left ≫ prod.snd

/-- The recursively computed value of the cons step. -/
def listStepValue (P V X : D) :
    (constantFamily P V ⨯ constantFamily P X).left ⟶ X :=
  (prod.snd : constantFamily P V ⨯ constantFamily P X ⟶
    constantFamily P X).left ≫ prod.snd

namespace StableListAlgebra

variable {V : D} (L : StableListAlgebra V) (E : DecidableVariables V)

theorem nil_mono : Mono L.algebra.nil := by
  let : IsIso (coprod.desc L.algebra.nil L.algebra.cons) :=
    Endofunctor.Algebra.Initial.str_isIso L.initial
  have h : L.algebra.nil =
      (coprod.inl : (⊤_ D) ⟶ (⊤_ D) ⨿ (V ⨯ L.algebra.carrier)) ≫
        coprod.desc L.algebra.nil L.algebra.cons :=
    (coprod.inl_desc _ _).symm
  rw [h]
  infer_instance

/-- The membership fold has the tested variable as parameter and returns
a truth value. Its cons step is equality of the head or membership in
the recursive list. -/
def membershipAlgebra : ListAlgebra (constantFamily V V) where
  carrier := constantFamily V (Two D)
  nil := Over.homMk (prod.lift (⊤_ (Over V)).hom
    (Two.constant (⊤_ (Over V)).left false)) (by simp [constantFamily])
  cons := Over.homMk (prod.lift
    (constantFamily V V ⨯ constantFamily V (Two D)).hom
    (Two.binary Bool.or
      (prod.lift (constantFamily V V ⨯ constantFamily V (Two D)).hom
        (listStepHead V V (Two D)) ≫ E.test)
      (listStepValue V V (Two D)))) (by simp [constantFamily])

def membershipFold : constantFamily V L.algebra.carrier ⟶ constantFamily V (Two D) :=
  L.foldWithParameters V (membershipAlgebra E)

/-- The membership morphism has source `V × W`, with the tested variable
as the first coordinate. -/
def membership : V ⨯ L.algebra.carrier ⟶ Two D :=
  (L.membershipFold E).left ≫ prod.snd

theorem membershipFold_nil :
    (L.algebra.withParameters V).nil ≫ L.membershipFold E =
      (membershipAlgebra E).nil :=
  L.foldWithParameters_nil V (membershipAlgebra E)

theorem membershipFold_cons :
    (L.algebra.withParameters V).cons ≫ L.membershipFold E =
      prod.map (𝟙 (constantFamily V V)) (L.membershipFold E) ≫
        (membershipAlgebra E).cons :=
  L.foldWithParameters_cons V (membershipAlgebra E)

theorem membership_nil :
    prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) ≫ L.membership E =
      Two.constant V false := by
  let j : Over.mk (𝟙 V) ⟶ ⊤_ (Over V) := terminal.from _
  have h := L.membershipFold_nil E
  have hh := congrArg (fun k => j.left ≫ k.left ≫ prod.snd) h
  change j.left ≫ ((prod.lift (⊤_ (Over V)).hom
    (terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil) ≫
      (L.membershipFold E).left) ≫ prod.snd) =
    j.left ≫ (prod.lift (⊤_ (Over V)).hom
      (Two.constant (⊤_ (Over V)).left false) ≫ prod.snd) at hh
  have hj : j.left ≫ (⊤_ (Over V)).hom = 𝟙 V := Over.w j
  have hn : j.left ≫ prod.lift (⊤_ (Over V)).hom
      (terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil) =
      prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) := by
    rw [prod.comp_lift, hj, ← Category.assoc, terminal.comp_from]
    rfl
  simp only [← Category.assoc] at hh
  rw [hn] at hh
  simpa only [membership, Category.assoc, prod.lift_snd,
    Two.comp_constant, Over.mk_left] using hh

/-- Deletion returns the recursive result when the head equals the
parameter and prepends the head otherwise. The conditional is the
constructed coproduct-fiber conditional on the Boolean object. -/
def deletionAlgebra : ListAlgebra (constantFamily V V) where
  carrier := constantFamily V L.algebra.carrier
  nil := Over.homMk (prod.lift (⊤_ (Over V)).hom
    (terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil)) (by simp [constantFamily])
  cons := Over.homMk (prod.lift
    (constantFamily V V ⨯ constantFamily V L.algebra.carrier).hom
    (Two.branch
      (prod.lift (constantFamily V V ⨯ constantFamily V L.algebra.carrier).hom
        (listStepHead V V L.algebra.carrier) ≫ E.test)
      (prod.lift (listStepHead V V L.algebra.carrier)
        (listStepValue V V L.algebra.carrier) ≫ L.algebra.cons)
      (listStepValue V V L.algebra.carrier))) (by simp [constantFamily])

def deletionFold :
    constantFamily V L.algebra.carrier ⟶ constantFamily V L.algebra.carrier :=
  L.foldWithParameters V (L.deletionAlgebra E)

def deletion : V ⨯ L.algebra.carrier ⟶ L.algebra.carrier :=
  (L.deletionFold E).left ≫ prod.snd

theorem deletionFold_nil :
    (L.algebra.withParameters V).nil ≫ L.deletionFold E = (L.deletionAlgebra E).nil :=
  L.foldWithParameters_nil V (L.deletionAlgebra E)

theorem deletionFold_cons :
    (L.algebra.withParameters V).cons ≫ L.deletionFold E =
      prod.map (𝟙 (constantFamily V V)) (L.deletionFold E) ≫ (L.deletionAlgebra E).cons :=
  L.foldWithParameters_cons V (L.deletionAlgebra E)

theorem deletion_nil :
    prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) ≫ L.deletion E =
      terminal.from V ≫ L.algebra.nil := by
  let j : Over.mk (𝟙 V) ⟶ ⊤_ (Over V) := terminal.from _
  have h := L.deletionFold_nil E
  have hh := congrArg (fun k => j.left ≫ k.left ≫ prod.snd) h
  change j.left ≫ ((prod.lift (⊤_ (Over V)).hom
    (terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil) ≫
      (L.deletionFold E).left) ≫ prod.snd) =
    j.left ≫ (prod.lift (⊤_ (Over V)).hom
      (terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil) ≫ prod.snd) at hh
  have hj : j.left ≫ (⊤_ (Over V)).hom = 𝟙 V := Over.w j
  have hn : j.left ≫ prod.lift (⊤_ (Over V)).hom
      (terminal.from (⊤_ (Over V)).left ≫ L.algebra.nil) =
      prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) := by
    rw [prod.comp_lift, hj, ← Category.assoc, terminal.comp_from]
    rfl
  simp only [← Category.assoc] at hh
  rw [hn] at hh
  simpa only [deletion, Category.assoc, prod.lift_snd, terminal.comp_from] using hh

def singleton : V ⟶ L.algebra.carrier :=
  prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil) ≫ L.algebra.cons

end StableListAlgebra

end CategoricalEssentialIncompleteness.V46
