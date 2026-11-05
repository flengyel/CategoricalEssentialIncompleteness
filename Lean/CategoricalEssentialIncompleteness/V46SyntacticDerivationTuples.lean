import CategoricalEssentialIncompleteness.V46Inference
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRepresentation

/-! Literal ordered premise tuples and their actual graph-defined action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation

/-- The nullary tuple is literal zero; positive tuples use the same
left-associated products as the categorical inference endofunctor. -/
def tupleCarrier (F : Carrier) (n : ℕ) : Carrier :=
  rawCarrier F F (SyntaxPolynomial.power .term n)

/-- This relation changes each premise independently. It imposes no
condition that the premise conclusions coincide with one another. -/
def tupleGraph (g : Graph) : ℕ → Graph
  | 0 => .mkSigma “x y. x = 0 ∧ y = 0”
  | 1 => g
  | n + 2 => let G := tupleGraph g (n + 1)
    .mkSigma “x y. ∃ a b c d,
      !pairDef.val x a b ∧ !pairDef.val y c d ∧ !G.val a c ∧ !g.val b d”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem tupleCarrier_zero (F : Carrier) (x : M) :
    (tupleCarrier F 0).val.Evalb ![x] ↔ x = 0 := by
  simp [tupleCarrier, SyntaxPolynomial.power, rawCarrier]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem tupleCarrier_one (F : Carrier) (x : M) :
    (tupleCarrier F 1).val.Evalb ![x] ↔ F.val.Evalb ![x] := by
  simp [tupleCarrier, SyntaxPolynomial.power, rawCarrier]

@[simp] theorem tupleCarrier_product (F : Carrier) (n : ℕ) (x : M) :
    (tupleCarrier F (n + 2)).val.Evalb ![x] ↔
      ∃ a b : M, x = Arithmetic.pair a b ∧
        (tupleCarrier F (n + 1)).val.Evalb ![a] ∧ F.val.Evalb ![b] := by
  simpa only [tupleCarrier, SyntaxPolynomial.power, rawCarrier] using
    rawCarrier_product_eval F F (SyntaxPolynomial.power .term (n + 1)) .term x

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem tupleGraph_zero (g : Graph) (x y : M) :
    (tupleGraph g 0).val.Evalb ![x, y] ↔ x = 0 ∧ y = 0 := by
  simp [tupleGraph]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
@[simp] theorem tupleGraph_one (g : Graph) (x y : M) :
    (tupleGraph g 1).val.Evalb ![x, y] ↔ g.val.Evalb ![x, y] := Iff.rfl

@[simp] theorem tupleGraph_product (g : Graph) (n : ℕ) (x y : M) :
    (tupleGraph g (n + 2)).val.Evalb ![x, y] ↔
      ∃ a b c d : M, x = Arithmetic.pair a b ∧ y = Arithmetic.pair c d ∧
        (tupleGraph g (n + 1)).val.Evalb ![a, c] ∧ g.val.Evalb ![b, d] := by
  simp [tupleGraph]

end Models

variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F G : Carrier}
variable (f : GraphMorphism T F G)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [𝗣𝗔 ⪯ T] in
theorem tupleGraph_support (n : ℕ) (x y : M)
    (h : (tupleGraph f.graph n).val.Evalb ![x, y]) :
    (tupleCarrier F n).val.Evalb ![x] ∧ (tupleCarrier G n).val.Evalb ![y] := by
  induction n generalizing x y with
  | zero => simpa only [tupleGraph_zero, tupleCarrier_zero] using h
  | succ n ih =>
    cases n with
    | zero =>
      simpa only [Nat.zero_add, tupleGraph_one, tupleCarrier_one] using f.support_model M x y h
    | succ n =>
      obtain ⟨a, b, c, d, hx, hy, hac, hbd⟩ := (tupleGraph_product f.graph n x y).mp h
      obtain ⟨ha, hc⟩ := ih a c hac
      obtain ⟨hb, hd⟩ := f.support_model M b d hbd
      exact ⟨(tupleCarrier_product F n x).mpr ⟨a, b, hx, ha, hb⟩,
        (tupleCarrier_product G n y).mpr ⟨c, d, hy, hc, hd⟩⟩

omit [𝗣𝗔 ⪯ T] in
/-- Totality is proved on each typed input tuple, in every model of T.
No simultaneous conclusion parameter is imposed on the components. -/
theorem tupleGraph_total (n : ℕ) (x : M)
    (hx : (tupleCarrier F n).val.Evalb ![x]) :
    ∃! y : M, (tupleGraph f.graph n).val.Evalb ![x, y] := by
  induction n generalizing x with
  | zero =>
    have hx' : x = 0 := (tupleCarrier_zero F x).mp hx
    exact ⟨0, (tupleGraph_zero f.graph x 0).mpr ⟨hx', rfl⟩,
      fun y hy => ((tupleGraph_zero f.graph x y).mp hy).2⟩
  | succ n ih =>
    cases n with
    | zero => exact f.total_model M x ((tupleCarrier_one F x).mp hx)
    | succ n =>
      obtain ⟨a, b, hx, ha, hb⟩ := (tupleCarrier_product F n x).mp hx
      obtain ⟨c, hc, hcu⟩ := ih a ha
      obtain ⟨d, hd, hdu⟩ := f.total_model M b hb
      refine ⟨Arithmetic.pair c d,
        (tupleGraph_product f.graph n x _).mpr ⟨a, b, c, d, hx, rfl, hc, hd⟩, ?_⟩
      intro y hy
      obtain ⟨a', b', c', d', hx', hy', hc', hd'⟩ := (tupleGraph_product f.graph n x y).mp hy
      have hea : a' = a := by
        simpa only [pi₁_pair] using congrArg pi₁ (hx'.symm.trans hx)
      have heb : b' = b := by
        simpa only [pi₂_pair] using congrArg pi₂ (hx'.symm.trans hx)
      subst a'
      subst b'
      rw [hcu c' hc', hdu d' hd'] at hy'
      exact hy'

end Models

/-- The arithmetic tuple action is constructed from the supplied total
morphism, rather than included as additional rule data. -/
def tupleMorphism (n : ℕ) : GraphMorphism T (tupleCarrier F n) (tupleCarrier G n) where
  graph := tupleGraph f.graph n
  support := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    rw [models_iff, supportSentence_eval]
    exact tupleGraph_support f M n
  total := by
    apply complete.{0} T
    intro M _ hM
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
    rw [models_iff, totalSentence_eval]
    exact tupleGraph_total f M n

variable (T) (F : PredicateCategory T)

theorem finitePower_eq_polynomial (n : ℕ) :
    finitePower (D := PredicateCategory T) F n =
      (SyntaxPolynomial.power .term n).eval.obj (F, F) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (finitePower (D := PredicateCategory T) F (n + 1) ⨯ F) =
        ((SyntaxPolynomial.power .term (n + 1)).eval.obj (F, F) ⨯ F)
      rw [ih]

/-- Actual chosen finite powers are encoded by the already constructed
polynomial graph. This introduces no representation hypothesis. -/
def finitePowerEncoder (n : ℕ) :
    GraphMorphism T (finitePower (D := PredicateCategory T) F n) (tupleCarrier F n) :=
  (chosenGraph T (eqToHom (C := PredicateCategory T) (finitePower_eq_polynomial T F n) :
    (finitePower (D := PredicateCategory T) F n : PredicateCategory T) ⟶
      (SyntaxPolynomial.power .term n).eval.obj (F, F))).composition
    (encodePolynomial T F F (SyntaxPolynomial.power .term n))

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
