/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsStable

/-! # Checks for constructed stable list algebras -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (P V : PredicateCategory T)

example : StableListAlgebra (D := PredicateCategory T) V := stableListAlgebra T V

example : IsInitial (algebra T V).asAlgebra := (stableListAlgebra T V).initial

example : IsInitial ((algebra T V).withParameters P).asAlgebra :=
  (stableListAlgebra T V).stable P

example (B : ListAlgebra (D := Over P) (constantFamily P V)) :
    ((algebra T V).withParameters P).nil ≫ fold T B = B.nil := fold_nil T B

example (B : ListAlgebra (D := Over P) (constantFamily P V))
    (m : constantFamily P (listObject T V) ⟶ B.carrier)
    (hn : ((algebra T V).withParameters P).nil ≫ m = B.nil)
    (hc : ((algebra T V).withParameters P).cons ≫ m =
      prod.map (𝟙 (constantFamily P V)) m ≫ B.cons) : m = fold T B :=
  fold_unique T B m hn hc
