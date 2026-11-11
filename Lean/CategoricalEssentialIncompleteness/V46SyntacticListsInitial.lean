/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListsUnique

/-! # Actual list initiality in every predicate-category parameter slice -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (P V : PredicateCategory T)

def targetListAlgebra (B : Endofunctor.Algebra (listFunctor (constantFamily P V))) :
    ListAlgebra (constantFamily P V) where
  carrier := B.a
  nil := coprod.inl ≫ B.str
  cons := coprod.inr ≫ B.str

/-- The graph-constructed fold is a morphism of complete endofunctor
algebras, not merely an external numerical evaluator. -/
def foldHom (B : Endofunctor.Algebra (listFunctor (constantFamily P V))) :
    ((algebra T V).withParameters P).asAlgebra ⟶ B where
  f := fold T (targetListAlgebra T P V B)
  h := by
    change coprod.map (𝟙 (⊤_ (Over P)))
      (prod.map (𝟙 (constantFamily P V)) (fold T (targetListAlgebra T P V B))) ≫
        B.str = coprod.desc ((algebra T V).withParameters P).nil
          ((algebra T V).withParameters P).cons ≫ fold T (targetListAlgebra T P V B)
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_map, Category.id_comp,
        ← Category.assoc, coprod.inl_desc]
      exact (fold_nil T (targetListAlgebra T P V B)).symm
    · simp only [← Category.assoc, coprod.inr_map, coprod.inr_desc]
      rw [Category.assoc]
      exact (fold_cons T (targetListAlgebra T P V B)).symm

/-- The canonical list carrier and its actual pulled-back constructors
are initial in `PredicateCategory T / P`, for every parameter predicate.
The target algebra may be any family over `P`. -/
def withParametersInitial : IsInitial ((algebra T V).withParameters P).asAlgebra :=
  IsInitial.ofUniqueHom (foldHom T P V) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    apply fold_unique T (targetListAlgebra T P V B) m.f
    · have h := congrArg (fun k => coprod.inl ≫ k) m.h
      change coprod.inl ≫
        (coprod.map (𝟙 (⊤_ (Over P))) (prod.map (𝟙 (constantFamily P V)) m.f) ≫ B.str) =
          coprod.inl ≫ (coprod.desc ((algebra T V).withParameters P).nil
            ((algebra T V).withParameters P).cons ≫ m.f) at h
      rw [← Category.assoc, coprod.inl_map, Category.id_comp,
        ← Category.assoc, coprod.inl_desc] at h
      exact h.symm
    · have h := congrArg (fun k => coprod.inr ≫ k) m.h
      change coprod.inr ≫
        (coprod.map (𝟙 (⊤_ (Over P))) (prod.map (𝟙 (constantFamily P V)) m.f) ≫ B.str) =
          coprod.inr ≫ (coprod.desc ((algebra T V).withParameters P).nil
            ((algebra T V).withParameters P).cons ≫ m.f) at h
      simp only [← Category.assoc, coprod.inr_map, coprod.inr_desc] at h
      rw [Category.assoc] at h
      exact h.symm)

end CategoricalEssentialIncompleteness.V46.SyntacticLists
