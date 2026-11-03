/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticUltrapower
import CategoricalEssentialIncompleteness.V46PredicateInterpretation
import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain
import CategoricalEssentialIncompleteness.V46UltrapowerTransport
import Mathlib.CategoryTheory.Whiskering

/-! # Comparison of code interpretation with the arithmetic ultrapower -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower

variable {I : Type} (U : Ultrafilter I)

theorem predicate_eval (C : Carrier) (a : Model U) :
    C.val.Evalb ![a] ↔ Germ.LiftPred (fun n : ℕ => C.val.Evalb ![n]) a := by
  induction a using Germ.inductionOn with | _ a =>
    simpa only [germ_cons, coordinate_cons, Matrix.empty_eq, Germ.liftPred_coe] using
      eval_representative U C.val ![a]

/-- The predicate comparison includes empty predicates and maps a family
of elements of C(N) to the same family in the arithmetic quotient. -/
def predicateEquiv (C : Carrier) :
    Ultrapower.Obj U (PredicateInterpretation.Obj ℕ C) ≃
      PredicateInterpretation.Obj (Model U) C :=
  (Ultrapower.subtypeEquiv U (fun n : ℕ => C.val.Evalb ![n])).trans
    { toFun := fun a => ⟨a.val, (predicate_eval U C a.val).mpr a.property⟩
      invFun := fun a => ⟨a.val, (predicate_eval U C a.val).mp a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem predicateEquiv_representative (C : Carrier)
    (a : I → PredicateInterpretation.Obj ℕ C) :
    (predicateEquiv U C (Germ.ofFun a)).val = Germ.ofFun (fun i => (a i).val) := rfl

/-- The same-family comparison is natural for every PA-provably total
functional graph, without an assumption of standard input coordinates. -/
def predicateComparison :
    PredicateInterpretation.functor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.functor 𝗣𝗔 (Model U) :=
  NatIso.ofComponents (fun C => (predicateEquiv U C).toIso) (by
    intro C D f
    induction f using Quotient.inductionOn with | _ f =>
      ext a
      induction a using Germ.inductionOn with | _ a =>
        symm
        apply (PredicateInterpretation.value_eq_iff 𝗣𝗔 (Model U) f _ _).mpr
        change f.graph.val.Evalb
          ![Germ.ofFun (fun i => (a i).val),
            Germ.ofFun (fun i => (PredicateInterpretation.value 𝗣𝗔 ℕ f (a i)).val)]
        have h : ∀ᶠ i in (U : Filter I), f.graph.val.Evalb
            ![(a i).val, (PredicateInterpretation.value 𝗣𝗔 ℕ f (a i)).val] :=
          Filter.Eventually.of_forall (fun i => PredicateInterpretation.value_graph 𝗣𝗔 ℕ f (a i))
        have hl := eval_representative U f.graph.val
          ![fun i => (a i).val,
            fun i => (PredicateInterpretation.value 𝗣𝗔 ℕ f (a i)).val]
        simp only [germ_cons, coordinate_cons, Matrix.empty_eq] at hl
        exact hl.mpr h)

/-- Arithmetic-ultrapower comparison on the actual total restriction
splitting, for the model functors defined through predicate presentations. -/
def comparison :
    PredicateInterpretation.totalFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.totalFunctor 𝗣𝗔 (Model U) :=
  Functor.associator (SyntacticPredicates.predicateEquivalence 𝗣𝗔).inverse
      (PredicateInterpretation.functor 𝗣𝗔 ℕ) (Ultrapower.functor U) ≪≫
    Functor.isoWhiskerLeft (SyntacticPredicates.predicateEquivalence 𝗣𝗔).inverse
      (predicateComparison U)

theorem comparison_naturality {X Y : TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (Ultrapower.functor U).map ((PredicateInterpretation.totalFunctor 𝗣𝗔 ℕ).map f) ≫
        (comparison U).hom.app Y =
      (comparison U).hom.app X ≫
        (PredicateInterpretation.totalFunctor 𝗣𝗔 (Model U)).map f :=
  (comparison U).hom.naturality f

/-- Lemma 6.8 for the model functors obtained by the actual chosen
domain splittings of the existing partial model interpretation. -/
def canonicalComparison :
    PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ ⋙ Ultrapower.functor U ≅
      PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (Model U) :=
  (Functor.isoWhiskerRight (PredicateInterpretation.totalCanonicalComparison 𝗣𝗔 ℕ)
    (Ultrapower.functor U)).symm ≪≫ comparison U ≪≫
      PredicateInterpretation.totalCanonicalComparison 𝗣𝗔 (Model U)

theorem canonicalComparison_naturality {X Y : TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (Ultrapower.functor U).map
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map f) ≫
        (canonicalComparison U).hom.app Y =
      (canonicalComparison U).hom.app X ≫
        (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (Model U)).map f :=
  (canonicalComparison U).hom.naturality f

/-- With a standard soundness factor supplied, transport it through the
constructed arithmetic comparison. This does not assume a comparison
isomorphism as additional data. -/
theorem canonical_soundness_transport {P S : TotalSplit 𝗣𝗔} (c : P ⟶ S) (ν : S ⟶ S)
    {V : Type} (v : V ⟶ (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).obj S)
    [Mono v] (e : (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).obj P ⟶ V)
    (he : e ≫ v = (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map c)
    (hc : Disjoint (Set.range v)
      (((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map ν) ⁻¹' Set.range v)) :
    Mono (Ultrapower.transportValidity U (canonicalComparison U) v) ∧
      Ultrapower.transportSoundness U (canonicalComparison U) e ≫
          Ultrapower.transportValidity U (canonicalComparison U) v =
        (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (Model U)).map c ∧
      Disjoint (Set.range (Ultrapower.transportValidity U (canonicalComparison U) v))
        (((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 (Model U)).map ν) ⁻¹'
          Set.range (Ultrapower.transportValidity U (canonicalComparison U) v)) :=
  Ultrapower.soundness_transport U (canonicalComparison U) c ν v e he hc

end CategoricalEssentialIncompleteness.V46.ArithmeticUltrapower
