/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels
public import CategoricalEssentialIncompleteness.V46CategoricalListLawsParameters

/-! # Opaque evaluation of projections of constant-family operations -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem parameterHom_point_value {P X Y : PredicateCategory T} (f : P ⨯ X ⟶ Y)
    (q : Obj T M (P ⨯ X)) :
    (F T M).map (prod.snd : P ⨯ Y ⟶ Y) ((F T M).map (parameterHom f).left q) =
      (F T M).map f q :=
  model_lift_snd T M (prod.fst : P ⨯ X ⟶ P) f q

/-- Normalize the interpretation of a proved three-morphism diagram while its morphisms
remain opaque. This avoids re-elaborating quotient morphisms inside a concrete
model-point calculation. -/
theorem model_three_composition_equality {A B C D E : PredicateCategory T}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (v : D ⟶ E)
    (comm : (f ≫ g) ≫ v = (h ≫ k) ≫ v) (q : Obj T M A) :
    (F T M).map v ((F T M).map g ((F T M).map f q)) =
      (F T M).map v ((F T M).map k ((F T M).map h q)) := by
  have he := congrArg (fun arrow => (F T M).map arrow q) comm
  simpa only [Functor.map_comp_apply] using he

/-- The structural morphism k and its projection remain opaque while the constant-family
comparison is evaluated. -/
theorem constant_projection_value {P A B : PredicateCategory T} {X : Over P}
    (k : X ⟶ constantFamily P A) (π : A ⟶ B) (r : X ⟶ constantFamily P B)
    (h : k ≫ (constantFamilyFunctor P).map π = r) (q : Obj T M X.left) :
    (F T M).map π ((F T M).map (prod.snd : P ⨯ A ⟶ A) ((F T M).map k.left q)) =
      (F T M).map (prod.snd : P ⨯ B ⟶ B) ((F T M).map r.left q) := by
  have he := congrArg (fun f => (F T M).map f.left q) h
  change (F T M).map (k.left ≫ ((constantFamilyFunctor P).map π).left) q =
    (F T M).map r.left q at he
  rw [Functor.map_comp_apply] at he
  have hs := congrArg ((F T M).map (prod.snd : P ⨯ B ⟶ B)) he
  have hm := model_map_snd T M (𝟙 P) π ((F T M).map k.left q)
  exact hm.symm.trans hs

theorem constant_projection_after_value {P A B : PredicateCategory T} {X W : Over P}
    (k : X ⟶ constantFamily P A) (π : A ⟶ B)
    (j : X ⟶ W) (op : W ⟶ constantFamily P B)
    (h : k ≫ (constantFamilyFunctor P).map π = j ≫ op) (q : Obj T M X.left) :
    (F T M).map π ((F T M).map (prod.snd : P ⨯ A ⟶ A) ((F T M).map k.left q)) =
      (F T M).map (prod.snd : P ⨯ B ⟶ B) ((F T M).map op.left ((F T M).map j.left q)) := by
  have hc := constant_projection_value T M k π (j ≫ op) h q
  have he : (F T M).map (prod.snd : P ⨯ B ⟶ B) ((F T M).map (j ≫ op).left q) =
      (F T M).map (prod.snd : P ⨯ B ⟶ B) ((F T M).map op.left ((F T M).map j.left q)) := by
    change (F T M).map prod.snd ((F T M).map (j.left ≫ op.left) q) = _
    rw [Functor.map_comp_apply]
  exact hc.trans he

/-- A retained-parameter state point is fixed by its original projection and its result
point. -/
theorem model_statePoint_ext {P A B : PredicateCategory T}
    (x y : Obj T M (P ⨯ (A ⨯ B)))
    (ho : (F T M).map ((constantFamilyFunctor P).map (prod.fst : A ⨯ B ⟶ A)).left x =
      (F T M).map ((constantFamilyFunctor P).map (prod.fst : A ⨯ B ⟶ A)).left y)
    (hr : (F T M).map (prod.snd : A ⨯ B ⟶ B) ((F T M).map prod.snd x) =
      (F T M).map (prod.snd : A ⨯ B ⟶ B) ((F T M).map prod.snd y)) : x = y := by
  apply modelProduct_ext T M
  · have h := congrArg ((F T M).map (prod.fst : P ⨯ A ⟶ P)) ho
    erw [model_map_fst T M (𝟙 P) (prod.fst : A ⨯ B ⟶ A) x,
      model_map_fst T M (𝟙 P) (prod.fst : A ⨯ B ⟶ A) y,
      Functor.map_id_apply,Functor.map_id_apply] at h
    exact h
  · apply modelProduct_ext T M
    · have h := congrArg ((F T M).map (prod.snd : P ⨯ A ⟶ A)) ho
      erw [model_map_snd T M (𝟙 P) (prod.fst : A ⨯ B ⟶ A) x,
        model_map_snd T M (𝟙 P) (prod.fst : A ⨯ B ⟶ A) y] at h
      exact h
    · exact hr

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
