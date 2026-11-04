/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticListsInitial

/-! # Checks for the constructed arbitrary-slice list universal property -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (P V : PredicateCategory T)
variable (B : ListAlgebra (D := Over P) (constantFamily P V))

example : IsInitial ((algebra T V).withParameters P).asAlgebra :=
  withParametersInitial T P V

example : (fold T B).left ≫ B.carrier.hom =
    (constantFamily P (listObject T V)).hom := Over.w _

example : ((algebra T V).withParameters P).nil ≫ fold T B = B.nil := fold_nil T B

example : ((algebra T V).withParameters P).cons ≫ fold T B =
    prod.map (𝟙 (constantFamily P V)) (fold T B) ≫ B.cons := fold_cons T B

example (m : constantFamily P (listObject T V) ⟶ B.carrier)
    (hn : ((algebra T V).withParameters P).nil ≫ m = B.nil)
    (hc : ((algebra T V).withParameters P).cons ≫ m =
      prod.map (𝟙 (constantFamily P V)) m ≫ B.cons) : m = fold T B :=
  fold_unique T B m hn hc
