/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkFormulaEvaluation
public import CategoricalEssentialIncompleteness.ForkSyntaxObjects

/-! # Effective evaluation into arbitrary c.e. formula algebras -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EnumerableCarriers (Carrier val)
open EffectiveFork (natCarrier)

def totalValue {X Y : Carrier} (f : X ⟶ Y) (hf : isTotal f) (x : {n // n ∈ X.support}) :
    {n // n ∈ Y.support} :=
  ⟨(val f x.val).get ((EnumerableCarriers.total_iff f).mp hf x.val x.property),
    EnumerableCarriers.val_target f _ _ (Part.get_mem _)⟩

theorem totalValue_mem {X Y : Carrier} (f : X ⟶ Y) (hf : isTotal f)
    (x : {n // n ∈ X.support}) : (totalValue f hf x).val ∈ val f x.val := Part.get_mem _

structure NumericalAlgebra (Z : Carrier) where
  atom : natCarrier ⟶ Z
  neg : Z ⟶ Z
  imp : EnumerableCarriers.product Z Z ⟶ Z
  atom_total : isTotal atom
  neg_total : isTotal neg
  imp_total : isTotal imp

namespace NumericalAlgebra

variable {Z : Carrier}

def eval (A : NumericalAlgebra Z) : Formula → {n // n ∈ Z.support}
  | .atom x => totalValue A.atom A.atom_total ⟨x,Set.mem_univ x⟩
  | .neg p => totalValue A.neg A.neg_total (eval A p)
  | .imp p q => totalValue A.imp A.imp_total
      ⟨Nat.pair (eval A p).val (eval A q).val,
        by exact ⟨by simpa using (eval A p).property,by simpa using (eval A q).property⟩⟩

theorem eval_atom (A : NumericalAlgebra Z) (x : ℕ) :
    (A.eval (.atom x)).val ∈ val A.atom x :=
  totalValue_mem A.atom A.atom_total ⟨x,Set.mem_univ x⟩

theorem eval_neg (A : NumericalAlgebra Z) (p : Formula) :
    (A.eval (.neg p)).val ∈ val A.neg (A.eval p).val :=
  totalValue_mem A.neg A.neg_total (A.eval p)

theorem eval_imp (A : NumericalAlgebra Z) (p q : Formula) :
    (A.eval (.imp p q)).val ∈ val A.imp (Nat.pair (A.eval p).val (A.eval q).val) :=
  totalValue_mem A.imp A.imp_total
    ⟨Nat.pair (A.eval p).val (A.eval q).val,
      ⟨by simpa using (A.eval p).property,by simpa using (A.eval q).property⟩⟩

theorem eval_computable (A : NumericalAlgebra Z) : Computable (fun p => (A.eval p).val) :=
  Formula.fold_computable_of_partial (EnumerableCarriers.val_partrec A.atom)
    (EnumerableCarriers.val_partrec A.neg) (EnumerableCarriers.val_partrec A.imp)
    (fun p => (A.eval p).val) A.eval_atom A.eval_neg A.eval_imp

def foldCode (A : NumericalAlgebra Z) (n : ℕ) : ℕ := (A.eval (Formula.decode n)).val

theorem foldCode_computable (A : NumericalAlgebra Z) : Computable A.foldCode :=
  Computable.comp (f := fun p => (A.eval p).val) (g := Formula.decode)
    A.eval_computable Formula.decode_computable

def foldArrow (A : NumericalAlgebra Z) : natCarrier ⟶ Z :=
  EnumerableCarriers.totalFromFunction A.foldCode A.foldCode_computable
    (fun n _ => (A.eval (Formula.decode n)).property)

theorem foldArrow_total (A : NumericalAlgebra Z) : isTotal A.foldArrow :=
  EnumerableCarriers.totalFromFunction_total A.foldCode A.foldCode_computable
    (fun n _ => (A.eval (Formula.decode n)).property)

theorem mem_foldArrow (A : NumericalAlgebra Z) (n y : ℕ) :
    y ∈ val A.foldArrow n ↔ y=A.foldCode n :=
  (EnumerableCarriers.mem_totalFromFunction _ _ _ n y).trans (and_iff_right (Set.mem_univ n))

theorem foldCode_encode (A : NumericalAlgebra Z) (p : Formula) :
    A.foldCode p.encode=(A.eval p).val := by
  unfold foldCode
  rw [Formula.decode_encode]

end NumericalAlgebra
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
