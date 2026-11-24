/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UltrapowerComparison

/-! The arithmetic comparison is checked on every total-split morphism. -/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter CategoryTheory
open CategoricalEssentialIncompleteness.V46

namespace CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower.Checks

open SyntacticPredicates

variable {I : Type} (U : Ultrafilter I)

theorem unary_predicate (C : Carrier) (x : I → ℕ) :
    C.val.Evalb (M := Model U) ![Germ.ofFun x] ↔
      ∀ᶠ i in (U : Filter I), C.val.Evalb ![x i] := by
  simpa only [germ_cons, coordinate_cons, Matrix.empty_eq] using
    eval_representative U C.val ![x]

theorem graph_value {C D : Carrier} (f : GraphMorphism 𝗣𝗔 C D)
    (x : I → PredicateInterpretation.Obj ℕ C) :
    f.graph.val.Evalb (M := Model U)
      ![Germ.ofFun (fun i => (x i).val),
        Germ.ofFun (fun i => (PredicateInterpretation.value 𝗣𝗔 ℕ f (x i)).val)] := by
  have h := eval_representative U f.graph.val
    ![fun i => (x i).val, fun i => (PredicateInterpretation.value 𝗣𝗔 ℕ f (x i)).val]
  simp only [germ_cons, coordinate_cons, Matrix.empty_eq] at h
  exact h.mpr (Filter.Eventually.of_forall
    (fun i => PredicateInterpretation.value_graph 𝗣𝗔 ℕ f (x i)))

theorem pa_axiom (φ : ArithmeticSentence) (h : φ ∈ 𝗣𝗔) : (Model U)↓[ℒₒᵣ] ⊧ φ :=
  (sentence_iff U φ).mpr (models_of_mem h)

end CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower.Checks

#print axioms ArithmeticUltrapower.Checks.unary_predicate
#print axioms ArithmeticUltrapower.Checks.graph_value
#print axioms ArithmeticUltrapower.Checks.pa_axiom

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.functor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.functor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.predicateComparison U

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.totalFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.totalFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.comparison U

example {I : Type} (U : Ultrafilter I)
    {X Y : SyntacticPredicates.TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (Ultrapower.functor U).map ((PredicateInterpretation.totalFunctor 𝗣𝗔 ℕ).map f) ≫
        (ArithmeticUltrapower.comparison U).hom.app Y =
      (ArithmeticUltrapower.comparison U).hom.app X ≫
        (PredicateInterpretation.totalFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map f :=
  ArithmeticUltrapower.comparison_naturality U f

example {I : Type} (U : Ultrafilter I) :
    PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U) :=
  ArithmeticUltrapower.canonicalComparison U

example {I : Type} (U : Ultrafilter I)
    {X Y : SyntacticPredicates.TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (Ultrapower.functor U).map
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map f) ≫
        (ArithmeticUltrapower.canonicalComparison U).hom.app Y =
      (ArithmeticUltrapower.canonicalComparison U).hom.app X ≫
        (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (ArithmeticUltrapower.Model U)).map f :=
  ArithmeticUltrapower.canonicalComparison_naturality U f
