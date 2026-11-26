module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # Signed theories and inseparable subobjects -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CEIPalomar

variable {D : Type u} [Category.{v} D]

/-- A calculus with an atomic-sentence morphism from `X`. For each axiom subobject
`A`, the derivations form an initial algebra for `inference A`. Its carrier
in the slice over the formula object is the conclusion morphism. -/
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

/-- The inverse image of `T` under sentence negation. -/
def refutations (T : Subobject P.sentence) : Subobject P.sentence :=
  (Subobject.pullback P.negate).obj T

/-- The theorem and refutation subobjects are disjoint. -/
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

/-- The subobjects `a` and `b` are disjoint and no pair of complementary
subobjects separates them. -/
def inseparable {X : D} (a b : Subobject X) : Prop :=
  a ⊓ b = ⊥ ∧
    ¬ ∃ c d : Subobject X, IsCompl c d ∧ a ≤ c ∧ b ≤ d

end CEIPalomar
