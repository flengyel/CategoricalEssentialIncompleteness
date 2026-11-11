/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebra
public import CategoricalEssentialIncompleteness.V46NullarySyntaxInterpretation

/-! # Terms of the nullary-predicate language -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)

def variableInputIso (Z : D) : Z ≅ Z ⨿ ((⊥_ D) ⨯ (⊤_ D)) where
  hom := coprod.inl
  inv := coprod.desc (𝟙 Z) ((NullarySyntaxAlgebra.emptyFunctionsInitial (D := D)).to Z)
  hom_inv_id := coprod.inl_desc _ _
  inv_hom_id := by
    apply coprod.hom_ext
    · simp
    · exact (NullarySyntaxAlgebra.emptyFunctionsInitial (D := D)).hom_ext _ _

instance variable_isIso : IsIso S.variableConstructor := by
  have : IsIso S.algebra.str := Endofunctor.Algebra.Initial.str_isIso S.initial
  have : IsIso S.algebra.str.1 := by
    change IsIso ((CategoryTheory.Prod.fst D D).map S.algebra.str)
    infer_instance
  have : IsIso (coprod.inl : V ⟶ V ⨿ ((⊥_ D) ⨯ (⊤_ D))) :=
    (variableInputIso V).isIso_hom
  let e : V ≅ S.algebra.a.1 := variableInputIso V ≪≫ asIso S.algebra.str.1
  exact e.isIso_hom

def variableIso : V ≅ S.algebra.a.1 := asIso S.variableConstructor

variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

theorem interpretation_term : (interpretation S Q f).1 = (variableIso S).inv ≫
    Q.variableConstructor := by
  apply (cancel_epi (variableIso S).hom).mp
  change S.variableConstructor ≫ (interpretation S Q f).1 =
    (variableIso S).hom ≫ ((variableIso S).inv ≫ Q.variableConstructor)
  rw [variable_law, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
