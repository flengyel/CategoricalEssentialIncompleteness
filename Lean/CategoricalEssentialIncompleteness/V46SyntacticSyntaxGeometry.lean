/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRaw
import CategoricalEssentialIncompleteness.V46SyntacticListsDecode
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Over

/-! # Actual model coproduct and parameter-fiber geometry -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax

/-- A preserved binary coproduct has injective, disjoint injections
covering every interpreted point, rather than just represented numerals. -/
theorem preservedSum_properties {C : Type u} [Category.{v} C]
    (G : C ⥤ Type) (A B : C) [HasBinaryCoproduct A B]
    [PreservesColimit (pair A B) G] :
    Function.Injective (G.map (coprod.inl : A ⟶ A ⨿ B)) ∧
      Function.Injective (G.map (coprod.inr : B ⟶ A ⨿ B)) ∧
        IsCompl (Set.range (G.map (coprod.inl : A ⟶ A ⨿ B)))
          (Set.range (G.map (coprod.inr : B ⟶ A ⨿ B))) := by
  have h := isColimitOfHasBinaryCoproductOfPreservesColimit G A B
  exact (Types.binaryCofan_isColimit_iff _).mp ⟨h⟩

theorem graph_functional_model {T : ArithmeticTheory} {C D : Carrier}
    (f : GraphMorphism T C D) {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (x y y' : M) (h : f.graph.val.Evalb ![x, y])
    (h' : f.graph.val.Evalb ![x, y']) : y = y' :=
  (f.total_model M x (f.support_model M x y h).1).unique h h'

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem chosenGraph_input_unique {C D : PredicateCategory T} (f : C ⟶ D)
    (hf : Function.Injective ((F T M).map f)) (x x' y : M)
    (h : (chosenGraph T f).graph.val.Evalb ![x, y])
    (h' : (chosenGraph T f).graph.val.Evalb ![x', y]) : x = x' := by
  let xx : Obj T M C := ⟨x, ((chosenGraph T f).support_model M x y h).1⟩
  let xx' : Obj T M C := ⟨x', ((chosenGraph T f).support_model M x' y h').1⟩
  let yy : Obj T M D := ⟨y, ((chosenGraph T f).support_model M x y h).2⟩
  exact congrArg Subtype.val (hf (((chosenGraph_map_iff T M f xx yy).mp h).trans
    ((chosenGraph_map_iff T M f xx' yy).mp h').symm))

theorem overGraph_target {P : PredicateCategory T} {A B : Over P} (f : A ⟶ B)
    (x y p : M) (h : (chosenGraph T f.left).graph.val.Evalb ![x, y])
    (hp : (chosenGraph T A.hom).graph.val.Evalb ![x, p]) :
    (chosenGraph T B.hom).graph.val.Evalb ![y, p] := by
  let xx : Obj T M A.left := ⟨x, ((chosenGraph T f.left).support_model M x y h).1⟩
  let yy : Obj T M B.left := ⟨y, ((chosenGraph T f.left).support_model M x y h).2⟩
  let pp : Obj T M P := ⟨p, ((chosenGraph T A.hom).support_model M x p hp).2⟩
  have hf := (chosenGraph_map_iff T M f.left xx yy).mp h
  have hx := (chosenGraph_map_iff T M A.hom xx pp).mp hp
  have hw := over_value T M f xx
  rw [hf, hx] at hw
  exact (chosenGraph_map_iff T M B.hom yy pp).mpr hw

theorem overGraph_source {P : PredicateCategory T} {A B : Over P} (f : A ⟶ B)
    (x y p : M) (h : (chosenGraph T f.left).graph.val.Evalb ![x, y])
    (hp : (chosenGraph T B.hom).graph.val.Evalb ![y, p]) :
    (chosenGraph T A.hom).graph.val.Evalb ![x, p] := by
  let xx : Obj T M A.left := ⟨x, ((chosenGraph T f.left).support_model M x y h).1⟩
  let yy : Obj T M B.left := ⟨y, ((chosenGraph T f.left).support_model M x y h).2⟩
  let pp : Obj T M P := ⟨p, ((chosenGraph T B.hom).support_model M y p hp).2⟩
  have hf := (chosenGraph_map_iff T M f.left xx yy).mp h
  have hy := (chosenGraph_map_iff T M B.hom yy pp).mp hp
  have hw := over_value T M f xx
  rw [hf, hy] at hw
  exact (chosenGraph_map_iff T M A.hom xx pp).mpr hw.symm

theorem modelSum_cases (A B : PredicateCategory T) (z : Obj T M (A ⨿ B)) :
    (∃ x : Obj T M A, (F T M).map (coprod.inl : A ⟶ A ⨿ B) x = z) ∨
      (∃ y : Obj T M B, (F T M).map (coprod.inr : B ⟶ A ⨿ B) y = z) := by
  have hc := (preservedSum_properties (F T M) A B).2.2
  have hz : z ∈ Set.range ((F T M).map (coprod.inl : A ⟶ A ⨿ B)) ⊔
      Set.range ((F T M).map (coprod.inr : B ⟶ A ⨿ B)) := by
    rw [hc.sup_eq_top]
    trivial
  exact hz

theorem modelSum_disjoint (A B : PredicateCategory T)
    (x : Obj T M A) (y : Obj T M B) :
    (F T M).map (coprod.inl : A ⟶ A ⨿ B) x ≠
      (F T M).map (coprod.inr : B ⟶ A ⨿ B) y := by
  intro h
  exact Set.disjoint_left.mp (preservedSum_properties (F T M) A B).2.2.disjoint
    ⟨x, rfl⟩ ⟨y, h.symm⟩

theorem modelSum_graph_disjoint (A B : PredicateCategory T) (x y z : M)
    (h : (chosenGraph T (coprod.inl : A ⟶ A ⨿ B)).graph.val.Evalb ![x, z])
    (h' : (chosenGraph T (coprod.inr : B ⟶ A ⨿ B)).graph.val.Evalb ![y, z]) : False := by
  let xx : Obj T M A :=
    ⟨x, ((chosenGraph T (coprod.inl : A ⟶ A ⨿ B)).support_model M x z h).1⟩
  let yy : Obj T M B :=
    ⟨y, ((chosenGraph T (coprod.inr : B ⟶ A ⨿ B)).support_model M y z h').1⟩
  let zz : Obj T M (A ⨿ B) :=
    ⟨z, ((chosenGraph T (coprod.inl : A ⟶ A ⨿ B)).support_model M x z h).2⟩
  exact modelSum_disjoint T M A B xx yy
    (((chosenGraph_map_iff T M coprod.inl xx zz).mp h).trans
      ((chosenGraph_map_iff T M coprod.inr yy zz).mp h').symm)

/-- The chosen terminal predicate has an actual point in every model. -/
def modelTerminalPoint : Obj T M (⊤_ (PredicateCategory T)) := by
  let C : PredicateCategory T := terminalCarrier
  let x : Obj T M C := ⟨0, by simp [C, terminalCarrier]⟩
  exact (F T M).map (terminal.from C) x

theorem modelOverSum_properties {P : PredicateCategory T} (A B : Over P) :
    Function.Injective ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left) ∧
      Function.Injective ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left) ∧
        IsCompl (Set.range ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left))
          (Set.range ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left)) :=
  preservedSum_properties (Over.forget P ⋙ F T M) A B

theorem modelOverSum_cases {P : PredicateCategory T} (A B : Over P)
    (z : Obj T M (A ⨿ B).left) :
    (∃ x : Obj T M A.left, (F T M).map (coprod.inl : A ⟶ A ⨿ B).left x = z) ∨
      (∃ y : Obj T M B.left, (F T M).map (coprod.inr : B ⟶ A ⨿ B).left y = z) := by
  have hc := (modelOverSum_properties T M A B).2.2
  have hz : z ∈ Set.range ((F T M).map (coprod.inl : A ⟶ A ⨿ B).left) ⊔
      Set.range ((F T M).map (coprod.inr : B ⟶ A ⨿ B).left) := by
    rw [hc.sup_eq_top]
    trivial
  exact hz

theorem modelOverSum_disjoint {P : PredicateCategory T} (A B : Over P)
    (x : Obj T M A.left) (y : Obj T M B.left) :
    (F T M).map (coprod.inl : A ⟶ A ⨿ B).left x ≠
      (F T M).map (coprod.inr : B ⟶ A ⨿ B).left y := by
  intro h
  exact Set.disjoint_left.mp (modelOverSum_properties T M A B).2.2.disjoint
    ⟨x, rfl⟩ ⟨y, h.symm⟩

/-- Every parameter has exactly one point in the terminal slice family. -/
theorem modelOverTerminal_existsUnique (P : PredicateCategory T) (p : Obj T M P) :
    ∃! z : Obj T M (⊤_ (Over P)).left, (F T M).map (⊤_ (Over P)).hom z = p := by
  let i := SyntacticLists.terminalOverIso T P
  let e := ((F T M).mapIso i).toEquiv
  refine ⟨e.symm p, ?_, ?_⟩
  · erw [← SyntacticLists.terminalOverIso_hom T P]
    exact e.apply_symm_apply p
  · intro z hz
    apply e.injective
    erw [← SyntacticLists.terminalOverIso_hom T P] at hz
    exact hz.trans (e.apply_symm_apply p).symm

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
