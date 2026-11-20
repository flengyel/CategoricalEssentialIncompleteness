module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # The calculus and its subobject predicates -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CEIPalomar

variable {D : Type u} [Category.{v} D]

/-- The formula and sentence objects, the atomic sentence and negation morphisms,
and the initial algebra of derivations from each axiom subobject. An object
of the slice over formulas is a family with its conclusion morphism. -/
structure Calculus (X : D) where
  formula : D
  sentence : D
  inclusion : sentence ⟶ formula
  inclusionMono : Mono inclusion
  atom : X ⟶ sentence
  negate : sentence ⟶ sentence
  inference : Subobject sentence → Over formula ⥤ Over formula
  proofs : (A : Subobject sentence) → Endofunctor.Algebra (inference A)
  initial : ∀ A, IsInitial (proofs A)

variable [Regular D] [FinitaryExtensive D]

namespace Calculus

variable {X : D} (P : Calculus X)

/-- The image of the conclusion morphism restricted to derivations of sentences. -/
def generated (A : Subobject P.sentence) : Subobject P.sentence :=
  imageSubobject (pullback.snd (P.proofs A).a.hom P.inclusion)

/-- Deductive closure of the positive and negative atomic axioms. -/
def signedTheory (a b : Subobject X) : Subobject P.sentence :=
  P.generated ((Subobject.«exists» P.atom).obj a ⊔
    (Subobject.«exists» (P.atom ≫ P.negate)).obj b)

/-- Sentences whose negations belong to the given subobject. -/
def refutations (T : Subobject P.sentence) : Subobject P.sentence :=
  (Subobject.pullback P.negate).obj T

/-- No sentence is both provable and refutable. -/
def consistent (T : Subobject P.sentence) : Prop :=
  T ⊓ P.refutations T = ⊥

/-- The theorem and refutation subobjects cover the sentence object. -/
def complete (T : Subobject P.sentence) : Prop :=
  T ⊔ P.refutations T = ⊤

/-- The base theory is consistent and every consistent deductively closed
extension in the same language is incomplete. -/
def essentiallyIncomplete (T : Subobject P.sentence) : Prop :=
  P.consistent T ∧ ∀ U : Subobject P.sentence,
    P.generated U = U → T ≤ U → P.consistent U → ¬ P.complete U

end Calculus

/-- Two disjoint subobjects which no complementary subobjects separate. -/
def inseparable {X : D} (a b : Subobject X) : Prop :=
  a ⊓ b = ⊥ ∧
    ¬ ∃ c d : Subobject X, IsCompl c d ∧ a ≤ c ∧ b ≤ d

end CEIPalomar
