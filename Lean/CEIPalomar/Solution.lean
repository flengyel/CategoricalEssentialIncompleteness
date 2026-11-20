module

public import CEIPalomar.CalculusDefinitions
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTheory

/-! # The signed-theory equivalence and its realization in the PA predicate category -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CEIPalomar

variable {D : Type u} [Category.{v} D]

variable [Regular D] [FinitaryExtensive D]

open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

/-- The sentence and formula objects, constructors, and initial derivation algebras
of the specified first-order presentation at the index object. -/
def ofNative {V : D} (F : NullaryPresentations V) (X : D) : Calculus X where
  formula := (F.syntaxData X).algebra.a.2
  sentence := (F.syntaxData X).sentenceObject
  inclusion := (F.syntaxData X).sentenceInclusion
  inclusionMono := inferInstance
  atom := NullaryInterpretation.atomSentence (F.syntaxData X)
  negate := (F.syntaxData X).sentenceNegation
  inference A := ((F.syntaxData X).logicalRules A.arrow).inference
  proofs := F.proofs X
  initial := F.initial X

/-- Membership in the family of nullary first-order calculi used in the
manuscript: equality includes the syntax operations, rule functors and proof
algebras recorded in the displayed calculus. -/
def IsNullaryCalculus {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    (V : D) {X : D} (P : Calculus X) : Prop :=
  ∃ F : NullaryPresentations V, P = ofNative F X

private theorem native_inseparable_iff {X : D} (a b : Subobject X) :
    SubobjectInseparable a b ↔ inseparable a b := by
  constructor
  · rintro ⟨hab, hn⟩
    refine ⟨hab, ?_⟩
    rintro ⟨c, d, hcd, hac, hbd⟩
    exact hn ⟨⟨c, d, hcd⟩, hac, hbd⟩
  · rintro ⟨hab, hn⟩
    refine ⟨hab, ?_⟩
    rintro ⟨p, hp, hq⟩
    exact hn ⟨p.positive, p.negative, p.complementary, hp, hq⟩

private theorem native_essential_iff {V X : D} (F : NullaryPresentations V)
    (a b : Subobject X) :
    (ofNative F X).essentiallyIncomplete ((ofNative F X).signedTheory a b) ↔
      (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro U hU hcU
    exact h U.val U.property hU hcU
  · rintro ⟨hc, h⟩
    refine ⟨hc, ?_⟩
    intro U closed hU hcU
    exact h ⟨U, closed⟩ hU hcU

/-- A consistent signed atomic theory is essentially incomplete exactly when
its two generating subobjects are inseparable. -/
theorem essential_incomplete_iff_inseparable {V X : D}
    (P : Calculus X) (hP : IsNullaryCalculus V P) (a b : Subobject X)
    (hab : a ⊓ b = ⊥) (hc : P.consistent (P.signedTheory a b)) :
    P.essentiallyIncomplete (P.signedTheory a b) ↔ inseparable a b := by
  obtain ⟨F, rfl⟩ := hP
  exact (native_essential_iff F a b).trans
    ((SignedFirstOrder.essential_incomplete_iff_subobject_inseparable F a b hab hc).trans
      (native_inseparable_iff a b))

/-- A Boolean assignment to the atomic predicates gives a closed, consistent,
complete theory extending every set of signed axioms respected by that assignment.
The first coproduct injection denotes false and the second denotes true. -/
theorem boolean_assignment {V X : D} (P : Calculus X) (hP : IsNullaryCalculus V P)
    (d : X ⟶ (⊤_ D) ⨿ (⊤_ D)) :
    ∃ T : Subobject P.sentence, P.generated T = T ∧ P.consistent T ∧ P.complete T ∧
      ∀ a b : Subobject X, a.arrow ≫ d = terminal.from (a : D) ≫ coprod.inr →
        b.arrow ≫ d = terminal.from (b : D) ≫ coprod.inl → P.signedTheory a b ≤ T := by
  obtain ⟨F, rfl⟩ := hP
  refine ⟨(SignedFirstOrder.booleanTheory F d).val,
    (SignedFirstOrder.booleanTheory F d).property,
    SignedFirstOrder.booleanTheory_consistent F d,
    SignedFirstOrder.booleanTheory_complete F d, ?_⟩
  intro a b ha hb
  exact SignedFirstOrder.booleanTheory_extends F d a b ⟨ha, hb⟩

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

/-- There exists a calculus and an inseparable pair whose signed theory
is consistent and essentially incomplete. The predicate category for Peano
arithmetic and its diagonal pair furnish the witness. -/
theorem exists_inseparable_example :
    ∃ (D : Type) (cat : Category.{0} D), letI := cat
      ∃ (reg : Regular D) (ext : FinitaryExtensive D), letI := reg; letI := ext
        ∃ (V X : D) (P : Calculus X) (a b : Subobject X),
          IsNullaryCalculus V P ∧ inseparable a b ∧
          P.essentiallyIncomplete (P.signedTheory a b) := by
  let X : SyntacticPredicates.PredicateCategory 𝗣𝗔 := PrintedObjectCoding.Number
  let F := ArithmeticSignedTheory.presentation
  let a := ArithmeticSignedAtoms.positiveSubobject
  let b := ArithmeticSignedAtoms.negativeSubobject
  refine ⟨SyntacticPredicates.PredicateCategory 𝗣𝗔, inferInstance, inferInstance, inferInstance,
    X, X, ofNative F X, a, b, ⟨F, rfl⟩, ?_, ?_⟩
  · exact (native_inseparable_iff a b).mp ArithmeticSignedEssential.diagonal_inseparable
  · exact (native_essential_iff F a b).mpr (ArithmeticSignedEssential.essentially_incomplete F)

end CEIPalomar
