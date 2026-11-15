/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedEssential
public import CategoricalEssentialIncompleteness.V46EquivalenceSubobjects
public import CategoricalEssentialIncompleteness.V46ClosedTheoryTransfer
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTotal

/-! # The diagonal signed theory in the total restriction splitting

The rule morphisms are transported by the constructed predicate equivalence.
The proof algebras in the target are the actual coded derivation algebras,
indexed only by axiom subobjects.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTotal
open ArithmeticSignedAtoms ArithmeticSignedTheoryTruth
local notation "E" => predicateEquivalence 𝗣𝗔
local notation "G" => SyntacticPredicates.realization 𝗣𝗔
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔} (F : NullaryPresentations V)
local notation "S" => NullaryPresentations.syntaxData F N

/-- The actual transported first-order rule presentation. -/
def rules (A : Subobject ((G).obj (S).sentenceObject)) :=
  firstOrderRules ((G).map (S).logicalAxioms) ((G).map (S).sentenceInclusion) A.arrow
    (FirstOrderRuleTransport.mappedAll (G) (S).quantifierConstructor)
    (FirstOrderRuleTransport.mappedImp (G) (S).implicationConstructor)

def proofs (A : Subobject ((G).obj (S).sentenceObject)) :
    Endofunctor.Algebra (rules F A).inference :=
  SyntacticDerivation.totalDerivationAlgebra 𝗣𝗔 (rules F A)

def initial (A : Subobject ((G).obj (S).sentenceObject)) : IsInitial (proofs F A) :=
  SyntacticDerivation.totalDerivationInitial 𝗣𝗔 (rules F A)

def atom : (G).obj N ⟶ (G).obj (S).sentenceObject :=
  (G).map (NullaryInterpretation.atomSentence (S))

def negation : (G).obj (S).sentenceObject ⟶ (G).obj (S).sentenceObject :=
  (G).map (S).sentenceNegation

def positive : Subobject ((G).obj N) := FiniteLimitSubobjects.object (G) positiveSubobject

def negative : Subobject ((G).obj N) := FiniteLimitSubobjects.object (G) negativeSubobject

def axioms : Subobject ((G).obj (S).sentenceObject) :=
  (Subobject.«exists» (atom F)).obj positive ⊔
    (Subobject.«exists» (atom F ≫ negation F)).obj negative

def theory : FirstOrderReflection.Theory (proofs F) :=
  ⟨FirstOrderReflection.generated (proofs F) (axioms F),
    FirstOrderReflection.idempotent (proofs F) (initial F) _⟩

theorem axioms_comparison : axioms F =
    FiniteLimitSubobjects.object (G)
      (SignedFirstOrder.axioms F positiveSubobject negativeSubobject) := by
  change _ = EquivalenceSubobjects.orderIso (E) (S).sentenceObject _
  rw [SignedFirstOrder.axioms, OrderIso.map_sup]
  rw [EquivalenceSubobjects.orderIso_apply, EquivalenceSubobjects.orderIso_apply,
    EquivalenceSubobjects.object_exists, EquivalenceSubobjects.object_exists]
  simp only [axioms, atom, negation, positive, negative, Functor.map_comp]
  rfl

/-- These are the images of the actual split-subobject inclusions. -/
theorem axioms_image : axioms F =
    imageSubobject ((G).map (numberInclusion ArithmeticDiagonalCodes.alpha) ≫ atom F) ⊔
      imageSubobject ((G).map (numberInclusion ArithmeticDiagonalCodes.beta) ≫
        atom F ≫ negation F) := by
  have hp : positive = Subobject.mk ((G).map (numberInclusion ArithmeticDiagonalCodes.alpha)) :=
    FiniteLimitSubobjects.object_mk (G) _
  have hn : negative = Subobject.mk ((G).map (numberInclusion ArithmeticDiagonalCodes.beta)) :=
    FiniteLimitSubobjects.object_mk (G) _
  exact congrArg₂ (· ⊔ ·)
    ((congrArg (fun A => (Subobject.«exists» (atom F)).obj A) hp).trans
      (SubobjectImagePresentations.exists_mk _ _))
    ((congrArg (fun A => (Subobject.«exists» (atom F ≫ negation F)).obj A) hn).trans
      (SubobjectImagePresentations.exists_mk _ _))

theorem theory_le_image : (theory F).val ≤
    FiniteLimitSubobjects.object (G)
      (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val := by
  change FirstOrderReflection.generated (proofs F) (axioms F) ≤ _
  rw [axioms_comparison]
  exact ClosedTheoryTransfer.generation_le_image (G) (F.proofs N) (F.initial N)
    (proofs F) (initial F) _

/-- Consistency is proved for the generated target theory, rather than
supplied as a preservation hypothesis. -/
theorem consistent :
    (theory F).val ⊓ (Subobject.pullback (negation F)).obj (theory F).val = ⊥ := by
  let T := (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val
  let e := EquivalenceSubobjects.orderIso (E) (S).sentenceObject
  have hc : e T ⊓ (Subobject.pullback (negation F)).obj (e T) = ⊥ := by
    change e T ⊓ (Subobject.pullback ((G).map (S).sentenceNegation)).obj
      (FiniteLimitSubobjects.object (G) T) = ⊥
    rw [← FiniteLimitSubobjects.object_pullback]
    change e T ⊓ e ((Subobject.pullback (S).sentenceNegation).obj T) = ⊥
    rw [← e.map_inf]
    have hs := signed_theory_consistent F
    change T ⊓ (Subobject.pullback (S).sentenceNegation).obj T = ⊥ at hs
    rw [hs, e.map_bot]
  apply le_antisymm _ bot_le
  exact (inf_le_inf (theory_le_image F)
    ((Subobject.pullback (negation F)).monotone (theory_le_image F))).trans_eq hc

theorem atomic_bounds :
    positive ≤ (Subobject.pullback (atom F)).obj (theory F).val ∧
    negative ≤ (Subobject.pullback (atom F)).obj
      ((Subobject.pullback (negation F)).obj (theory F).val) := by
  have he := FirstOrderReflection.extensive (proofs F) (axioms F)
  constructor
  · exact (Subobject.existsPullbackAdj (atom F)).gc _ _ |>.mp
      ((le_sup_left : _ ≤ axioms F).trans he)
  · have hb := (Subobject.existsPullbackAdj (atom F ≫ negation F)).gc _ _ |>.mp
      ((le_sup_right : _ ≤ axioms F).trans he)
    simp only [Subobject.pullback_comp] at hb
    exact hb

theorem inseparable : SubobjectInseparable positive negative :=
  EquivalenceSubobjects.inseparable (E) ArithmeticSignedEssential.diagonal_inseparable

/-- All internal extensions are covered, including arbitrary closed
subobjects of the actual target sentence object. -/
theorem every_consistent_extension_incomplete
    (U : FirstOrderReflection.Theory (proofs F))
    (hExt : (theory F).val ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (negation F)).obj U.val = ⊥) :
    U.val ⊔ (Subobject.pullback (negation F)).obj U.val ≠ ⊤ := by
  intro hcomp
  have hb := atomic_bounds F
  have hp := hb.1.trans ((Subobject.pullback (atom F)).monotone hExt)
  have hn := hb.2.trans ((Subobject.pullback (atom F)).monotone
    ((Subobject.pullback (negation F)).monotone hExt))
  have hs : HasSubobjectSeparator U.val ((Subobject.pullback (negation F)).obj U.val) :=
    ⟨⟨U.val, (Subobject.pullback (negation F)).obj U.val,
      ⟨disjoint_iff.mpr hc, codisjoint_iff.mpr hcomp⟩⟩, le_rfl, le_rfl⟩
  exact inseparable.2 (subobject_separator_mono hp hn
    (subobject_separator_pullback (atom F) hs))

theorem essentially_incomplete :
    ((theory F).val ⊓ (Subobject.pullback (negation F)).obj (theory F).val = ⊥) ∧
    ∀ U : FirstOrderReflection.Theory (proofs F), (theory F).val ≤ U.val →
      U.val ⊓ (Subobject.pullback (negation F)).obj U.val = ⊥ →
      U.val ⊔ (Subobject.pullback (negation F)).obj U.val ≠ ⊤ :=
  ⟨consistent F, every_consistent_extension_incomplete F⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTotal
