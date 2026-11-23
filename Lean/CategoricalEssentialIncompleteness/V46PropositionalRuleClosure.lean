/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationInference
public import CategoricalEssentialIncompleteness.V46ErasureLogicalSchemes

/-! # The three Hilbert axiom schemes and modus ponens in a regular category -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.PropositionalRules

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {S A : D} (neg : S ⟶ S) (imp : S ⨯ S ⟶ S) (a : A ⟶ S)

def axioms := coprod.desc (coprod.desc (coprod.desc (ErasureLogicalSchemes.one imp)
  (ErasureLogicalSchemes.two imp)) (ErasureLogicalSchemes.three neg imp)) a

/-- The instance object at arity one is the initial object. -/
def rules : RulePresentation S 2 where
  instances := ![_, ⊥_ D, S ⨯ S]
  premises := Fin.cases (terminal.from _)
    (Fin.cases (initial.to S) (Fin.cases (prod.lift prod.fst imp) (fun j => Fin.elim0 j)))
  conclusion := Fin.cases (axioms neg imp a)
    (Fin.cases (initial.to S) (Fin.cases prod.snd (fun j => Fin.elim0 j)))

/-- Containment of the nullary instances and closure under modus ponens characterize
an algebra on any conclusion morphism. -/
theorem closed_iff {Q : D} (m : Q ⟶ S) :
    ClosedUnder (rules neg imp a).inference m ↔
      (∃ k, k ≫ m = axioms neg imp a) ∧
      ∃ k, k ≫ m = pullback.fst (prod.lift prod.fst imp) (prod.map m m) ≫ prod.snd := by
  let R := rules neg imp a
  let X := Over.mk m
  constructor
  · rintro ⟨α⟩
    refine ⟨R.closed_contains_nullary m α, ⟨Sigma.ι (R.ruleObject X) 2 ≫ α.left, ?_⟩⟩
    have hα : α.left ≫ m = Sigma.desc (R.ruleConclusion X) := Over.w α
    rw [Category.assoc, hα, Sigma.ι_comp_desc]
    rfl
  · rintro ⟨⟨k, hk⟩, ⟨p, hp⟩⟩
    have branches (j : Fin 3) :
        ∃ h : R.ruleObject X j ⟶ Q, h ≫ m = R.ruleConclusion X j := by
      fin_cases j
      · refine ⟨pullback.fst _ _ ≫ k, ?_⟩
        rw [Category.assoc, hk]
        rfl
      · exact ⟨pullback.snd (initial.to S) m, (pullback.condition (f := initial.to S) (g := m)).symm⟩
      · exact ⟨p, hp⟩
    refine ⟨Over.homMk (Sigma.desc (fun j => (branches j).choose)) ?_⟩
    apply Sigma.hom_ext
    intro j
    change Sigma.ι _ j ≫ Sigma.desc _ ≫ m = Sigma.ι _ j ≫ Sigma.desc _
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (branches j).choose_spec

/-- The regular image of the initial deduction algebra is the least theorem subobject. -/
theorem least_theorems (P : Endofunctor.Algebra (rules neg imp a).inference)
    (hP : IsInitial P) :
    ClosedUnder (rules neg imp a).inference (image.ι P.a.hom) ∧
      ∀ {Q : D} (m : Q ⟶ S) [Mono m], ClosedUnder (rules neg imp a).inference m →
        ∃ w : image P.a.hom ⟶ Q, w ≫ m = image.ι P.a.hom :=
  (rules neg imp a).least_theorem_subobject P hP

end CategoricalEssentialIncompleteness.V46.PropositionalRules
