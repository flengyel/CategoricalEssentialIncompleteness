module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Inseparability and essential incompleteness in a recursion category

To construct a first-order theory internal to a recursion category `R`, start
with two disjoint domains `a` and `b` of partial morphisms on an object `X`.
In the category of total morphisms of the restriction idempotent completion
of `R`, the domains are represented by inclusions `i_a : A ↪ X` and
`i_b : B ↪ X`. The syntax and derivations are formed in this total category.

The only nonlogical symbols are nullary predicates. A nullary predicate takes
no arguments, so it is already an atomic sentence. Let `S` be the sentence
object. The family of these atomic sentences is given by a morphism `θ : X ⟶ S`.
For any object `W`, an index `x : W ⟶ X` gives a family of atomic sentences
`x ≫ θ : W ⟶ S`. The index lies in `a` when `x = u ≫ i_a` for some
`u : W ⟶ A`. Then `x ≫ θ = u ≫ (i_a ≫ θ)`. Thus the atoms indexed by `a`
form the restricted family `i_a ≫ θ : A ⟶ S`.

Take the image of this family as the subobject of positive axioms. For the
negative axioms, restrict the family to `b` and apply sentence negation
`ν : S ⟶ S`. Their subobject is the image of `i_b ≫ θ ≫ ν : B ⟶ S`. Let `T`
be the least deductively closed subobject of `S` containing both images.
Its theorems are precisely the sentences derivable from these axioms in the
internal calculus.

The domains `a` and `b` are inseparable if no pair of complementary domains
on `X` contains them respectively. Suppose `T` is consistent. It is essentially
incomplete if every consistent deductively closed internal extension of `T` in
the same language is incomplete. Corollary 4.8 says that `T` is essentially
incomplete if and only if `a` and `b` are inseparable.

Assume the total category is regular with disjoint, pullback-stable finite
coproducts and that its monomorphisms have partial inverses in the completion.
Fix a decidable variable object. For each index object assume parameter-stable
syntax and list algebras and an initial derivation algebra for each axiom
subobject.

Fix a target presentation with this variable object. Let `S_U` be its sentence
object and `U` a consistent internal theory in that presentation. The free
first-order adjunction (Theorem 4.7) says that a morphism `f : X ⟶ S_U` extends
to a unique translation of `T` into `U` exactly when it sends `a` into the
theorems of `U` and `b` into its refutations. A sentence is refuted when its
negation is a theorem.

In a complete consistent closed extension of `T` in the same language,
the theorem and refutation subobjects of `S` are complementary. Their
inverse images along `θ` are complementary subobjects of `X`. They contain
`a` and `b`, respectively, because the extension contains the generating axioms
of `T`.

Conversely, let `C` and `D` be complementary subobjects of `X` with `a ≤ C`
and `b ≤ D`. This separator gives a coproduct decomposition `X ≅ C ⨿ D`.
With `1` terminal, the morphism `d : X ⟶ 1 ⨿ 1` that is true on `C` and false
on `D` extends to a Boolean valuation of formulas. The inverse image of true
under the valuation on sentences is a complete consistent closed extension of `T`.
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
