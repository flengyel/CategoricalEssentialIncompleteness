module

public import CEIPalomar.CalculusDefinitions
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTheory

/-! # Essential incompleteness and inseparable subobjects -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CEIPalomar

variable {D : Type u} [Category.{v} D]

variable [Regular D] [FinitaryExtensive D]

open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

/-- The calculus of the family of nullary first-order presentations `F` at `X`. -/
def ofNullaryPresentation {V : D} (F : NullaryPresentations V) (X : D) : Calculus X where
  formula := (F.syntaxData X).algebra.a.2
  sentence := (F.syntaxData X).sentenceObject
  inclusion := (F.syntaxData X).sentenceInclusion
  inclusionMono := inferInstance
  atom := NullaryInterpretation.atomSentence (F.syntaxData X)
  negate := (F.syntaxData X).sentenceNegation
  inference A := ((F.syntaxData X).logicalRules A.arrow).inference
  proofs := F.proofs X
  initial := F.initial X

@[inherit_doc ofNullaryPresentation]
abbrev ofNative {V : D} (F : NullaryPresentations V) (X : D) : Calculus X :=
  ofNullaryPresentation F X

/-- `P` is the calculus at `X` of a family of nullary first-order presentations
with variable object `V`. -/
def IsNullaryCalculus {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    (V : D) {X : D} (P : Calculus X) : Prop :=
  ∃ F : NullaryPresentations V, P = ofNullaryPresentation F X

/-- A partition separating `a` and `b` consists of complementary subobjects
`c` and `d` with `a ≤ c` and `b ≤ d`. -/
theorem subobjectInseparable_iff_inseparable {X : D} (a b : Subobject X) :
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

@[inherit_doc subobjectInseparable_iff_inseparable]
alias native_inseparable_iff := subobjectInseparable_iff_inseparable

/-- The closed extensions of a theory `T` are the sentence subobjects `U`
with `T ≤ U` and `generated U = U`. -/
theorem essentiallyIncomplete_signedTheory_iff {V X : D} (F : NullaryPresentations V)
    (a b : Subobject X) :
    (ofNullaryPresentation F X).essentiallyIncomplete
        ((ofNullaryPresentation F X).signedTheory a b) ↔
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

@[inherit_doc essentiallyIncomplete_signedTheory_iff]
alias native_essential_iff := essentiallyIncomplete_signedTheory_iff

/-- Let `a` and `b` be disjoint subobjects of `X` whose signed theory is
consistent. This theory is essentially incomplete if and only if `a` and `b`
are inseparable. -/
theorem essential_incomplete_iff_inseparable {V X : D}
    (P : Calculus X) (hP : IsNullaryCalculus V P) (a b : Subobject X)
    (hab : a ⊓ b = ⊥) (hc : P.consistent (P.signedTheory a b)) :
    P.essentiallyIncomplete (P.signedTheory a b) ↔ inseparable a b := by
  obtain ⟨F, rfl⟩ := hP
  exact (essentiallyIncomplete_signedTheory_iff F a b).trans
    ((SignedFirstOrder.essential_incomplete_iff_subobject_inseparable F a b hab hc).trans
      (subobjectInseparable_iff_inseparable a b))

/-- Let `1` be the terminal object. For each `d : X ⟶ 1 ⨿ 1` there is a closed,
consistent, complete theory `T` containing `P.signedTheory a b` for every pair
of subobjects `a, b` on which `d` restricts to true and false, respectively.
The right coproduct injection denotes true and the left denotes false. -/
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

/-- In the predicate category of Peano arithmetic the two diagonal subobjects of
the number object are inseparable and their signed theory is essentially incomplete. -/
theorem pa_diagonal_witness :
    let N : SyntacticPredicates.PredicateCategory 𝗣𝗔 := PrintedObjectCoding.Number
    let P := ofNullaryPresentation ArithmeticSignedTheory.presentation N
    let a := ArithmeticSignedAtoms.positiveSubobject
    let b := ArithmeticSignedAtoms.negativeSubobject
    IsNullaryCalculus N P ∧ inseparable a b ∧ P.essentiallyIncomplete (P.signedTheory a b) := by
  let F := ArithmeticSignedTheory.presentation
  let N : SyntacticPredicates.PredicateCategory 𝗣𝗔 := PrintedObjectCoding.Number
  let a := ArithmeticSignedAtoms.positiveSubobject
  let b := ArithmeticSignedAtoms.negativeSubobject
  have hP : IsNullaryCalculus N (ofNullaryPresentation F N) := ⟨F, rfl⟩
  have hi := (subobjectInseparable_iff_inseparable a b).mp
    ArithmeticSignedEssential.diagonal_inseparable
  exact ⟨hP, hi, (essential_incomplete_iff_inseparable (ofNullaryPresentation F N) hP a b hi.1
    (ArithmeticSignedTheoryTruth.signed_theory_consistent F)).mpr hi⟩

/-- In some regular category with disjoint, pullback-stable finite coproducts,
there is a nullary first-order calculus with an inseparable pair of subobjects
of its index object. The signed theory of this pair is essentially incomplete. -/
theorem exists_inseparable_example :
    ∃ (D : Type) (cat : Category.{0} D), letI := cat
      ∃ (reg : Regular D) (ext : FinitaryExtensive D), letI := reg; letI := ext
        ∃ (V X : D) (P : Calculus X) (a b : Subobject X),
          IsNullaryCalculus V P ∧ inseparable a b ∧
          P.essentiallyIncomplete (P.signedTheory a b) := by
  let X : SyntacticPredicates.PredicateCategory 𝗣𝗔 := PrintedObjectCoding.Number
  exact ⟨SyntacticPredicates.PredicateCategory 𝗣𝗔, inferInstance, inferInstance, inferInstance,
    X, X, ofNullaryPresentation ArithmeticSignedTheory.presentation X,
    ArithmeticSignedAtoms.positiveSubobject, ArithmeticSignedAtoms.negativeSubobject,
    pa_diagonal_witness⟩

end CEIPalomar
