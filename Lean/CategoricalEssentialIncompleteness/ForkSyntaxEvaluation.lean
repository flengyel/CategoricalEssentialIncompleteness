/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkNumericalAlgebras

/-! # Natural formula evaluation into an arbitrary fork algebra -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EnumerableCarriers (Carrier val)
open EffectiveFork (Object V)

theorem transport_output {C D E F : Carrier} {r : C ⟶ D} {s : E ⟶ F}
    {f : C ⟶ E} {g : D ⟶ F} (h : EffectiveFork.Respects r s f g)
    (hs : isTotal s) {x y u v : ℕ} (hy : y ∈ val f x) (hu : u ∈ val r x)
    (hv : v ∈ val g u) : v ∈ val s y := by
  obtain ⟨w,hw⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff s).mp hs y
    (EnumerableCarriers.val_target f x y hy))
  exact Part.mem_unique (h x y u w hy hu hw) hv ▸ hw

theorem eval_natural {C D : Carrier} (A : NumericalAlgebra C) (B : NumericalAlgebra D)
    (r : C ⟶ D) (hr : isTotal r) (f : ℕ → ℕ) (hf : Computable f)
    (ha : EffectiveFork.Respects (natArrow f hf) r A.atom B.atom)
    (hn : EffectiveFork.Respects r r A.neg B.neg)
    (hi : EffectiveFork.Respects (EnumerableCarriers.partialProdMap r r) r A.imp B.imp)
    (p : Formula) : (B.eval (p.mapAtoms f)).val ∈ val r (A.eval p).val := by
  induction p with
  | atom x =>
    exact transport_output ha hr (A.eval_atom x) ((mem_natArrow f hf x _).mpr rfl)
      (B.eval_atom (f x))
  | neg p ih => exact transport_output hn hr (A.eval_neg p) ih (B.eval_neg _)
  | imp p q ihp ihq =>
    apply transport_output hi hr (A.eval_imp p q) _ (B.eval_imp _ _)
    apply (EnumerableCarriers.mem_partialProdMap_iff r r _ _).mpr
    simpa only [Nat.unpair_pair] using And.intro ihp ihq

/-- A polynomial algebra presented by its three total constructor morphisms. -/
structure Algebra (Z : Object) where
  atom : V ⟶ Z
  neg : Z ⟶ Z
  imp : EffectiveFork.product Z Z ⟶ Z
  atom_total : isTotal atom
  neg_total : isTotal neg
  imp_total : isTotal imp

namespace Algebra

variable {Z : Object}

def center (A : Algebra Z) : NumericalAlgebra Z.center :=
  ⟨A.atom.center,A.neg.center,A.imp.center,((EffectiveFork.total_iff _).mp A.atom_total).1,
    ((EffectiveFork.total_iff _).mp A.neg_total).1,((EffectiveFork.total_iff _).mp A.imp_total).1⟩
def left (A : Algebra Z) : NumericalAlgebra Z.left :=
  ⟨A.atom.left,A.neg.left,A.imp.left,((EffectiveFork.total_iff _).mp A.atom_total).2.1,
    ((EffectiveFork.total_iff _).mp A.neg_total).2.1,((EffectiveFork.total_iff _).mp A.imp_total).2.1⟩
def right (A : Algebra Z) : NumericalAlgebra Z.right :=
  ⟨A.atom.right,A.neg.right,A.imp.right,((EffectiveFork.total_iff _).mp A.atom_total).2.2,
    ((EffectiveFork.total_iff _).mp A.neg_total).2.2,((EffectiveFork.total_iff _).mp A.imp_total).2.2⟩

theorem natural_left (A : Algebra Z) (p : Formula) :
    (A.left.eval (p.mapAtoms EffectiveFork.leftCoordinate)).val ∈
      val Z.leftMap (A.center.eval p).val :=
  eval_natural A.center A.left Z.leftMap Z.left_total _ EffectiveFork.leftCoordinate_computable
    A.atom.natural_left A.neg.natural_left A.imp.natural_left p

theorem natural_right (A : Algebra Z) (p : Formula) :
    (A.right.eval (p.mapAtoms EffectiveFork.rightCoordinate)).val ∈
      val Z.rightMap (A.center.eval p).val :=
  eval_natural A.center A.right Z.rightMap Z.right_total _ EffectiveFork.rightCoordinate_computable
    A.atom.natural_right A.neg.natural_right A.imp.natural_right p

def fold (A : Algebra Z) : S ⟶ Z :=
  EffectiveFork.computedMap (X := S) (Y := Z)
    A.center.foldCode A.left.foldCode A.right.foldCode
    A.center.foldCode_computable A.left.foldCode_computable A.right.foldCode_computable
    (fun n _ => (A.center.eval (Formula.decode n)).property)
    (fun n _ => (A.left.eval (Formula.decode n)).property)
    (fun n _ => (A.right.eval (Formula.decode n)).property)
    (by
      intro x u hu
      rw [(mem_S_left x u).mp hu]
      change (A.left.eval (Formula.decode (Formula.encode
        (Formula.mapAtoms EffectiveFork.leftCoordinate (Formula.decode x))))).val ∈ _
      rw [Formula.decode_encode]
      exact A.natural_left _)
    (by
      intro x u hu
      rw [(mem_S_right x u).mp hu]
      change (A.right.eval (Formula.decode (Formula.encode
        (Formula.mapAtoms EffectiveFork.rightCoordinate (Formula.decode x))))).val ∈ _
      rw [Formula.decode_encode]
      exact A.natural_right _)

theorem fold_total (A : Algebra Z) : isTotal A.fold := by
  unfold fold
  apply EffectiveFork.computedMap_total

end Algebra
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
