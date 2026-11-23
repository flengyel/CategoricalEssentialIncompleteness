/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleTuringFibres
public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluationCoproducts

/-! # The partial spans and parameters of Proposition 10.1 and Theorem B.7 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.Kleene (eval)
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks

open NumericalTuples (Point Tuple code)
open ForkDiagonalObstruction (tupleDiagram tupleSpace)

example (j : WalkingSpan) {X Y : PartialMaps.Par (WalkingSpan ⥤ NumericalTuples.Object)}
    (s : PartialMaps.Raw X Y) :
    (evaluation j).map (PartialMaps.ofSpan s) = PartialMaps.ofSpan
      (⟨s.apex.obj j, s.l.app j, s.r.app j, by
        change Mono (s.l.app j)
        let : Mono s.l := s.wl
        exact (baseEval j).map_mono s.l, by trivial⟩ :
        PartialMaps.Raw ((evaluation j).obj X) ((evaluation j).obj Y)) := evaluation_span j s

example {X Y : ForkSpans} (j : WalkingSpan) (f : X ⟶ Y) :
    (evaluation j).map (rst f) = rst ((evaluation j).map f) ∧
      (evaluation j).map (0 : X ⟶ Y) = 0 ∧
      (evaluation j).map (Ranges.range f).hom = (Ranges.range ((evaluation j).map f)).hom :=
  ⟨evaluation_restriction j f, evaluation_zero j X Y, evaluation_range j f⟩

example {ι : Type*} {X : ForkSpans} (j : WalkingSpan) (s : Finset ι) (a : ι → Idem X) :
    evaluatedIdem j (s.sup a) = s.sup (fun i => evaluatedIdem j (a i)) :=
  evaluation_finset j s a

example {W X Y Z : ForkSpans} (j : WalkingSpan) (f : W ⟶ X) (g : Y ⟶ Z) :
    (evaluation j).map (forkProducts.map f g) ≫ (productComparison j X Z).hom =
      (productComparison j W Y).hom ≫ tupleProducts.map ((evaluation j).map f) ((evaluation j).map g) :=
  evaluation_product j f g

example (j : WalkingSpan) (X Y : ForkSpans) :
    IsColimit (BinaryCofan.mk ((evaluation j).map (PartialMaps.ofTotal coprod.inl : X ⟶ forkSum X Y))
      ((evaluation j).map (PartialMaps.ofTotal coprod.inr : Y ⟶ forkSum X Y))) :=
  evaluatedSumColimit j X Y

theorem endpoint_morphisms :
    @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
      tupleProducts.pcategoryLaws ⟨tupleSpace 2⟩ ⟨tupleSpace 2⟩ ⟨tupleSpace 2⟩
        ((productComparison .left universal universal).inv ≫ (evaluation .left).map tau) ∧
    @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
      tupleProducts.pcategoryLaws ⟨tupleSpace 2⟩ ⟨tupleSpace 2⟩ ⟨tupleSpace 2⟩
        ((productComparison .right universal universal).inv ≫ (evaluation .right).map tau) :=
  ⟨left_isTuring, right_isTuring⟩

theorem endpoint_graphs (k p l x a b : ℕ) :
    (Graph (evaluatedTau .left) (pairPoint (point₂ k p) (point₂ l x)) (point₂ a b) ↔
      (a,b) ∈ Part.map Nat.unpair (eval p (Nat.pair l x))) ∧
    (Graph (evaluatedTau .right) (pairPoint (point₂ k p) (point₂ l x)) (point₂ a b) ↔
      (a,b) ∈ Part.map Nat.unpair (eval p (Nat.pair l x))) :=
  ⟨left_graph _ _ _ _ _ _, right_graph _ _ _ _ _ _⟩

theorem endpoint_parameter {Z : PartialMaps.Par NumericalTuples.Object}
    (f : tupleProduct Z endpoint ⟶ endpoint) :
    ∃ (s : Tuple Z.obj.dimension → ℕ) (c : Z ⟶ endpoint), Computable s ∧ isTotal c ∧
      (∀ (z : Point Z.obj) (q : Point (tupleSpace 2)), Graph c z q ↔ q.val = (0, s z.val)) ∧
      (∀ (z : Point Z.obj) (l x a b : ℕ), Graph f (pairPoint z (point₂ l x)) (point₂ a b) ↔
        (a,b) ∈ Part.map Nat.unpair (eval (s z.val) (Nat.pair l x))) ∧
      tupleProducts.map c (𝟙 endpoint) ≫ evaluatedTau .left = f ∧
      tupleProducts.map c (𝟙 endpoint) ≫ evaluatedTau .right = f := by
  refine ⟨fun z => endpointIndex f (code _ z), endpointParameter f,
    (endpointIndex_computable f).comp Computable.encode, endpointParameter_total f,
    endpointParameter_graph f, endpoint_decoded_fibre f, ?_, ?_⟩
  · rw [left_tau]
    exact endpoint_parameterizes f
  · rw [right_tau]
    exact endpoint_parameterizes f

theorem fork_morphism :
    @RecursionCategory.IsTuringMorphism (PartialMaps.Par (WalkingSpan ⥤ NumericalTuples.Object)) _
      forkProducts.pcategoryStruct forkProducts.pcategoryLaws
        ⟨tupleDiagram⟩ ⟨tupleDiagram⟩ ⟨tupleDiagram⟩ tau := tau_isTuring

theorem center_computation (k p₀ p₁ p₂ l x₀ x₁ x₂ h y₀ y₁ y₂ : ℕ) :
    Graph ((productComparison .zero universal universal).inv ≫ (evaluation .zero).map tau)
      (pairPoint (point₄ k p₀ p₁ p₂) (point₄ l x₀ x₁ x₂)) (point₄ h y₀ y₁ y₂) ↔
      EffectiveFork.quadCode (h,y₀,y₁,y₂) ∈ eval p₀ (EffectiveFork.quadCode (l,x₀,x₁,x₂)) ∧
      Nat.pair h y₁ ∈ eval p₁ (Nat.pair l x₁) ∧ Nat.pair h y₂ ∈ eval p₂ (Nat.pair l x₂) :=
  center_tuple_graph _ _ _ _ _ _ _ _ _ _ _ _

theorem fork_parameter {Y : PartialMaps.Par (WalkingSpan ⥤ NumericalTuples.Object)}
    (f : forkProduct Y universal ⟶ universal) :
    ∃ c : Y ⟶ universal, isTotal c ∧ forkProducts.map c (𝟙 universal) ≫ tau = f ∧
      (∀ (z : Point (Y.obj.obj .left)) (q : Point (tupleSpace 2)),
        Graph ((evaluation .left).map c) z q ↔ q.val = (0, componentIndex f .left (code _ z.val))) ∧
      (∀ (z : Point (Y.obj.obj .right)) (q : Point (tupleSpace 2)),
        Graph ((evaluation .right).map c) z q ↔ q.val = (0, componentIndex f .right (code _ z.val))) ∧
      (∀ (z : Point (Y.obj.obj .zero)) (q : Point (tupleSpace 4)),
        Graph ((evaluation .zero).map c) z q ↔
          q.val = (0, componentIndex f .zero (code _ z.val),
            componentIndex f .left (code _ ((Y.obj.map WalkingSpan.Hom.fst).toFun z).val),
            componentIndex f .right (code _ ((Y.obj.map WalkingSpan.Hom.snd).toFun z).val))) ∧
      (∀ (j : WalkingSpan), Computable (fun z : Tuple (Y.obj.obj j).dimension =>
        componentIndex f j (code _ z))) ∧
      (∀ (j : WalkingSpan) (z : Point (Y.obj.obj j)) (x w : Point (universal.obj.obj j)),
        code _ w.val ∈ eval (componentIndex f j (code _ z.val)) (code _ x.val) ↔
          Graph ((productComparison j Y universal).inv ≫ (evaluation j).map f) (pairPoint z x) w) :=
  ⟨forkParameter f, forkParameter_total f, fork_parameterizes f, forkParameter_left f,
    forkParameter_right f, forkParameter_center f, componentIndex_computable f,
    fun j => component_fibre j f⟩

example (m n : ℕ) (G : Tuple m × Tuple n → Part ℕ) (h : Partrec G) :
    ∃ s : Tuple m → ℕ, Computable s ∧ ∀ y x, eval (s y) (code n x) = G (y,x) :=
  specialize_tuples m n G h

example (m : ℕ) : ∃ e : Tuple (m+1) ≃ ℕ, Computable e ∧ Computable e.symm ∧
    ∀ t, e t = code (m+1) t :=
  ⟨positiveTupleCoding m, (positiveTuple_computable m).1, (positiveTuple_computable m).2, fun _ => rfl⟩

example {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) (j : WalkingSpan)
    (z : Tuple (Y.obj.obj j).dimension) (hz : z ∉ (Y.obj.obj j).support) (x : ℕ) :
    eval (componentIndex f j (code _ z)) x = Part.none :=
  componentIndex_outside j f z hz x

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks

#print axioms CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks.endpoint_morphisms
#print axioms CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks.endpoint_graphs
#print axioms CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks.endpoint_parameter
#print axioms CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks.fork_morphism
#print axioms CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks.center_computation
#print axioms CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation.Checks.fork_parameter
