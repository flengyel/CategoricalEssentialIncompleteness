module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Inseparability and essential incompleteness in a recursion category

Let `a` and `b` be disjoint domains of partial morphisms on an object `X` of a
recursion category `R`. In the first-order calculus of Theorem 4.7, form the
theory `T` internal to `R` by asserting the nullary predicates indexed by `a`
and the negations of those indexed by `b`. Suppose `T` is consistent. Then
`T` has a complete consistent closed internal extension in the same language
if and only if the two domains can be separated (Corollary 4.8).

The syntax and derivations lie in the category of total morphisms of the
restriction idempotent completion of `R`. There `a` and `b` are subobjects
of `X`. A separator is a pair of complementary subobjects of `X` containing
`a` and `b`, respectively. Let `S` be the sentence object and `θ : X ⟶ S` the
morphism assigning to each index its atomic sentence. In a complete consistent
closed extension of `T`, the theorem and refutation subobjects of `S` are
complementary. Their inverse images along `θ` separate `a` and `b`.

Conversely, a separator expresses `X` as a coproduct. Assigning true to the
summand containing `a` and false to the summand containing `b` defines a
morphism `d : X ⟶ 1 ⨿ 1`, where `1` is terminal. This assignment extends to
a Boolean valuation of formulas. Its true sentences form a complete
consistent closed extension of `T`.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CEIPalomar

variable {D : Type u} [Category.{v} D]

/-- A calculus with atomic sentences indexed by `X`. For each axiom subobject
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

/-- The calculus `P` is the value at `X` of a family of first-order presentations
with decidable variable object `V`, equality, negation, implication and universal
quantification. At each object `Y`, the only nonlogical symbols are nullary
predicates indexed by `Y`. The parameter-stable initial syntax and list algebras
determine substitution and the logical rule instances. For each axiom subobject,
the derivations form an initial algebra for the corresponding inference functor. -/
def IsNullaryCalculus {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    (V : D) {X : D} (P : Calculus X) : Prop := by
  sorry

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

/-- The subobjects `a` and `b` are disjoint, and there are no complementary
subobjects `c` and `d` of `X` with `a ≤ c` and `b ≤ d`. -/
def inseparable {X : D} (a b : Subobject X) : Prop :=
  a ⊓ b = ⊥ ∧
    ¬ ∃ c d : Subobject X, IsCompl c d ∧ a ≤ c ∧ b ≤ d

/-- Let `a` and `b` be disjoint subobjects of `X` whose signed theory is
consistent. This theory is essentially incomplete if and only if `a` and `b`
are inseparable. -/
theorem essential_incomplete_iff_inseparable {V X : D}
    (P : Calculus X) (hP : IsNullaryCalculus V P) (a b : Subobject X)
    (hab : a ⊓ b = ⊥) (hc : P.consistent (P.signedTheory a b)) :
    P.essentiallyIncomplete (P.signedTheory a b) ↔ inseparable a b := by
  sorry

/-- Let `1` be the terminal object. For each `d : X ⟶ 1 ⨿ 1` there is a closed,
consistent, complete theory `T` containing `P.signedTheory a b` for every pair
of subobjects `a, b` on which `d` restricts to true and false, respectively.
The right coproduct injection denotes true and the left denotes false. -/
theorem boolean_assignment {V X : D} (P : Calculus X) (hP : IsNullaryCalculus V P)
    (d : X ⟶ (⊤_ D) ⨿ (⊤_ D)) :
    ∃ T : Subobject P.sentence, P.generated T = T ∧ P.consistent T ∧ P.complete T ∧
      ∀ a b : Subobject X, a.arrow ≫ d = terminal.from (a : D) ≫ coprod.inr →
        b.arrow ≫ d = terminal.from (b : D) ≫ coprod.inl → P.signedTheory a b ≤ T := by
  sorry

/-- In some regular category with disjoint, pullback-stable finite coproducts,
there is a nullary first-order calculus with an inseparable pair of subobjects
of its index object. The signed theory of this pair is essentially incomplete. -/
theorem exists_inseparable_example :
    ∃ (D : Type) (cat : Category.{0} D), letI := cat
      ∃ (reg : Regular D) (ext : FinitaryExtensive D), letI := reg; letI := ext
        ∃ (V X : D) (P : Calculus X) (a b : Subobject X),
          IsNullaryCalculus V P ∧ inseparable a b ∧
          P.essentiallyIncomplete (P.signedTheory a b) := by
  sorry

end CEIPalomar
