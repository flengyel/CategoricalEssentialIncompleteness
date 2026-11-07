/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalSyntax
import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain
import CategoricalEssentialIncompleteness.EnumerableUnderlying
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-! # Literal predicate presentations of numerical tuples -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalCoordinates

def predicateSupport (C : PredicateCategory 𝗧𝗔) : Set ℕ :=
  {n | C.val.Evalb ![n]}

theorem predicateSupport_enumerable (C : PredicateCategory 𝗧𝗔) :
    REPred (· ∈ predicateSupport C) := by
  apply rePred_iff_sigma1.mpr
  refine ⟨C.rew Rew.emb, ?_⟩
  intro v
  simp [predicateSupport, ← Matrix.fun_eq_vec_one]

def predicateCarrier (C : PredicateCategory 𝗧𝗔) : EnumerableCarriers.Total :=
  ⟨⟨predicateSupport C, predicateSupport_enumerable C⟩⟩

def predicateObject (C : PredicateCategory 𝗧𝗔) : NumericalTuples.Object :=
  NumericalTuples.unary (predicateCarrier C)

theorem standardPredicate_domain (C : PredicateCategory 𝗧𝗔) :
    (NumericalStableLists.standardTotalEquivalence.functor.obj
      ((realization 𝗧𝗔).obj C)).obj.domain =
      ClassicalPrograms.supportIdem (predicateSupport C) (predicateSupport_enumerable C) := by
  apply Idem.ext
  apply FunctorImage.Hom.ext
  change (SyntacticModel.modelFunctor 𝗧𝗔 ℕ).map
      (SyntacticPredicates.omegaArrow 𝗧𝗔 (predicateClass 𝗧𝗔 C)) =
    supportIdentity (predicateSupport C)
  apply PFun.ext
  intro (x : ℕ) (y : ℕ)
  have hm := SyntacticModel.mem_model 𝗧𝗔 ℕ
    (SyntacticPredicates.omegaArrow 𝗧𝗔 (predicateClass 𝗧𝗔 C)) x y
  have ha := SyntacticModel.mem_arrow 𝗧𝗔 ℕ
    (SyntacticPredicates.omegaArrow 𝗧𝗔 (predicateClass 𝗧𝗔 C))
    (SyntacticModel.codingEquiv 𝗧𝗔 ℕ (objectCode (omegaObject 𝗧𝗔)) x)
    (SyntacticModel.codingEquiv 𝗧𝗔 ℕ (objectCode (omegaObject 𝗧𝗔)) y)
  exact hm.trans (ha.trans ((predicateClass_model 𝗧𝗔 C ℕ x y).trans
    (mem_supportIdentity (predicateSupport C) x y).symm))

theorem standardPredicate_object (C : PredicateCategory 𝗧𝗔) :
    NumericalStableLists.standardTotalEquivalence.functor.obj ((realization 𝗧𝗔).obj C) =
      NumericalTuples.classicalTotalEquivalence.functor.obj (predicateObject C) := by
  have hc := NumericalTuples.codedObject_unary (predicateCarrier C)
  change (⟨⟨ClassicalPrograms.U, _⟩⟩ :
      PartialSpans.Total (SplitObject ClassicalPrograms.Rec)) =
    EnumerableCarriers.inclusion_rst.totalEquivalence.functor.obj
      (NumericalTuples.codedObject (predicateObject C))
  rw [show NumericalTuples.codedObject (predicateObject C) = predicateCarrier C from hc]
  exact congrArg (fun e : Idem ClassicalPrograms.U =>
    (⟨⟨ClassicalPrograms.U, e⟩⟩ : PartialSpans.Total (SplitObject ClassicalPrograms.Rec)))
      (standardPredicate_domain C)

/-- The map is an actual numerical isomorphism, so both directions have
partial-recursive realizers total on their respective carriers. -/
def predicatePresentationIso (C : PredicateCategory 𝗧𝗔) :
    NumericalSyntax.predicateEquivalence.functor.obj C ≅ predicateObject C :=
  NumericalTuples.classicalTotalEquivalence.functor.preimageIso
    (NumericalTuples.classicalTotalEquivalence.counitIso.app
      (NumericalStableLists.standardTotalEquivalence.functor.obj ((realization 𝗧𝗔).obj C)) ≪≫
        eqToIso (standardPredicate_object C))

end CategoricalEssentialIncompleteness.V46.NumericalCoordinates
