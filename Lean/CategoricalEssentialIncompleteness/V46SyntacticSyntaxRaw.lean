/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalSyntax
import CategoricalEssentialIncompleteness.V46SyntacticPredicates

/-! # Sigma-one polynomial fibers for arbitrary named-syntax algebras -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax

abbrev RawPolynomial := SyntaxPolynomial Carrier
abbrev TernaryGraph := 𝚺₁.Semisentence 3

/-- Literal numerical presentation of a polynomial value. Products use
pairing and sums the same pair tags zero and one as the predicate coproduct. -/
def rawCarrier (X Y : Carrier) : RawPolynomial → Carrier
  | .term => X
  | .formula => Y
  | .coefficient C => C
  | .unit => .mkSigma “u. u = 0”
  | .product a b =>
      let A := rawCarrier X Y a
      let B := rawCarrier X Y b
      .mkSigma “u. ∃ v w, !pairDef.val u v w ∧ !A.val v ∧ !B.val w”
  | .sum a b =>
      let A := rawCarrier X Y a
      let B := rawCarrier X Y b
      .mkSigma “u. (∃ v, !pairDef.val u v 0 ∧ !A.val v) ∨
        (∃ w, !pairDef.val u w 1 ∧ !B.val w)”

/-- A polynomial value in one common parameter fiber. The projections
are actual given graph operations and need only be provable in T. -/
def rawFiber (P X Y : Carrier) (ξ υ : Graph) : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => .mkSigma “p u. !P.val p ∧ !X.val u ∧ !ξ.val u p”
  | .formula => .mkSigma “p u. !P.val p ∧ !Y.val u ∧ !υ.val u p”
  | .coefficient C => .mkSigma “p u. !P.val p ∧ !C.val u”
  | .unit => .mkSigma “p u. !P.val p ∧ u = 0”
  | .product a b =>
      let A := rawFiber P X Y ξ υ a
      let B := rawFiber P X Y ξ υ b
      .mkSigma “p u. ∃ v w, !pairDef.val u v w ∧ !A.val p v ∧ !B.val p w”
  | .sum a b =>
      let A := rawFiber P X Y ξ υ a
      let B := rawFiber P X Y ξ υ b
      .mkSigma “p u. (∃ v, !pairDef.val u v 0 ∧ !A.val p v) ∨
        (∃ w, !pairDef.val u w 1 ∧ !B.val p w)”

/-- The polynomial action on graph-defined term and formula maps.
Labels are retained, child values are transformed in their given order,
and no evaluation map or induction conclusion is included in these data. -/
def mapRaw (P : Carrier) (hT hF : TernaryGraph) : RawPolynomial → TernaryGraph
  | .term => hT
  | .formula => hF
  | .coefficient C => .mkSigma “p u v. !P.val p ∧ !C.val u ∧ v = u”
  | .unit => .mkSigma “p u v. !P.val p ∧ u = 0 ∧ v = 0”
  | .product a b =>
      let A := mapRaw P hT hF a
      let B := mapRaw P hT hF b
      .mkSigma “p u v. ∃ a b c d,
        !pairDef.val u a b ∧ !pairDef.val v c d ∧ !A.val p a c ∧ !B.val p b d”
  | .sum a b =>
      let A := mapRaw P hT hF a
      let B := mapRaw P hT hF b
      .mkSigma “p u v. (∃ a c,
        !pairDef.val u a 0 ∧ !pairDef.val v c 0 ∧ !A.val p a c) ∨
        (∃ b d, !pairDef.val u b 1 ∧ !pairDef.val v d 1 ∧ !B.val p b d)”

section Models
variable {M : Type} [ORingStructure M]
variable (P X Y : Carrier) (ξ υ : Graph)

@[simp] theorem rawFiber_term_eval (p u : M) :
    (rawFiber P X Y ξ υ .term).val.Evalb ![p, u] ↔
      P.val.Evalb ![p] ∧ X.val.Evalb ![u] ∧ ξ.val.Evalb ![u, p] := by
  simp [rawFiber]

@[simp] theorem rawFiber_formula_eval (p u : M) :
    (rawFiber P X Y ξ υ .formula).val.Evalb ![p, u] ↔
      P.val.Evalb ![p] ∧ Y.val.Evalb ![u] ∧ υ.val.Evalb ![u, p] := by
  simp [rawFiber]

@[simp] theorem rawFiber_coefficient_eval (C : Carrier) (p u : M) :
    (rawFiber P X Y ξ υ (.coefficient C)).val.Evalb ![p, u] ↔
      P.val.Evalb ![p] ∧ C.val.Evalb ![u] := by simp [rawFiber]

@[simp] theorem rawFiber_unit_eval (p u : M) :
    (rawFiber P X Y ξ υ .unit).val.Evalb ![p, u] ↔ P.val.Evalb ![p] ∧ u = 0 := by
  simp [rawFiber]

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

@[simp] theorem rawCarrier_product_eval (a b : RawPolynomial) (u : M) :
    (rawCarrier X Y (.product a b)).val.Evalb ![u] ↔
      ∃ v w : M, u = Arithmetic.pair v w ∧
        (rawCarrier X Y a).val.Evalb ![v] ∧ (rawCarrier X Y b).val.Evalb ![w] := by
  simp [rawCarrier]

@[simp] theorem rawCarrier_sum_eval (a b : RawPolynomial) (u : M) :
    (rawCarrier X Y (.sum a b)).val.Evalb ![u] ↔
      (∃ v : M, u = Arithmetic.pair v 0 ∧ (rawCarrier X Y a).val.Evalb ![v]) ∨
      (∃ w : M, u = Arithmetic.pair w 1 ∧ (rawCarrier X Y b).val.Evalb ![w]) := by
  simp [rawCarrier]

@[simp] theorem rawFiber_product_eval (a b : RawPolynomial) (p u : M) :
    (rawFiber P X Y ξ υ (.product a b)).val.Evalb ![p, u] ↔
      ∃ v w : M, u = Arithmetic.pair v w ∧
        (rawFiber P X Y ξ υ a).val.Evalb ![p, v] ∧
          (rawFiber P X Y ξ υ b).val.Evalb ![p, w] := by simp [rawFiber]

@[simp] theorem rawFiber_sum_eval (a b : RawPolynomial) (p u : M) :
    (rawFiber P X Y ξ υ (.sum a b)).val.Evalb ![p, u] ↔
      (∃ v : M, u = Arithmetic.pair v 0 ∧ (rawFiber P X Y ξ υ a).val.Evalb ![p, v]) ∨
      (∃ w : M, u = Arithmetic.pair w 1 ∧ (rawFiber P X Y ξ υ b).val.Evalb ![p, w]) := by
  simp [rawFiber]

theorem rawFiber_parameter (a : RawPolynomial) (p u : M)
    (h : (rawFiber P X Y ξ υ a).val.Evalb ![p, u]) : P.val.Evalb ![p] := by
  induction a generalizing u with
  | term => exact ((rawFiber_term_eval P X Y ξ υ p u).mp h).1
  | formula => exact ((rawFiber_formula_eval P X Y ξ υ p u).mp h).1
  | coefficient C => exact ((rawFiber_coefficient_eval P X Y ξ υ C p u).mp h).1
  | unit => exact ((rawFiber_unit_eval P X Y ξ υ p u).mp h).1
  | product a b ia _ =>
      obtain ⟨v, _, _, hv, _⟩ := (rawFiber_product_eval P X Y ξ υ a b p u).mp h
      exact ia v hv
  | sum a b ia ib =>
      rcases (rawFiber_sum_eval P X Y ξ υ a b p u).mp h with
        ⟨v, _, hv⟩ | ⟨w, _, hw⟩
      · exact ia v hv
      · exact ib w hw

theorem rawFiber_carrier (a : RawPolynomial) (p u : M)
    (h : (rawFiber P X Y ξ υ a).val.Evalb ![p, u]) :
    (rawCarrier X Y a).val.Evalb ![u] := by
  induction a generalizing u with
  | term => exact ((rawFiber_term_eval P X Y ξ υ p u).mp h).2.1
  | formula => exact ((rawFiber_formula_eval P X Y ξ υ p u).mp h).2.1
  | coefficient C => exact ((rawFiber_coefficient_eval P X Y ξ υ C p u).mp h).2
  | unit => simpa [rawCarrier] using ((rawFiber_unit_eval P X Y ξ υ p u).mp h).2
  | product a b ia ib =>
      obtain ⟨v, w, he, hv, hw⟩ := (rawFiber_product_eval P X Y ξ υ a b p u).mp h
      exact (rawCarrier_product_eval X Y a b u).mpr ⟨v, w, he, ia v hv, ib w hw⟩
  | sum a b ia ib =>
      rcases (rawFiber_sum_eval P X Y ξ υ a b p u).mp h with
        ⟨v, he, hv⟩ | ⟨w, he, hw⟩
      · exact (rawCarrier_sum_eval X Y a b u).mpr (Or.inl ⟨v, he, ia v hv⟩)
      · exact (rawCarrier_sum_eval X Y a b u).mpr (Or.inr ⟨w, he, ib w hw⟩)

@[simp] theorem mapRaw_product_eval (hT hF : TernaryGraph) (a b : RawPolynomial)
    (p u v : M) :
    (mapRaw P hT hF (.product a b)).val.Evalb ![p, u, v] ↔
      ∃ a₀ b₀ c₀ d₀ : M, u = Arithmetic.pair a₀ b₀ ∧ v = Arithmetic.pair c₀ d₀ ∧
        (mapRaw P hT hF a).val.Evalb ![p, a₀, c₀] ∧
          (mapRaw P hT hF b).val.Evalb ![p, b₀, d₀] := by simp [mapRaw]

@[simp] theorem mapRaw_sum_eval (hT hF : TernaryGraph) (a b : RawPolynomial)
    (p u v : M) :
    (mapRaw P hT hF (.sum a b)).val.Evalb ![p, u, v] ↔
      (∃ a₀ c₀ : M, u = Arithmetic.pair a₀ 0 ∧ v = Arithmetic.pair c₀ 0 ∧
        (mapRaw P hT hF a).val.Evalb ![p, a₀, c₀]) ∨
      (∃ b₀ d₀ : M, u = Arithmetic.pair b₀ 1 ∧ v = Arithmetic.pair d₀ 1 ∧
        (mapRaw P hT hF b).val.Evalb ![p, b₀, d₀]) := by simp [mapRaw]

end Models

/-- Totality and support of a root operation refer only to its given
fiber source. They contain no evaluator or initiality statement. -/
def operationSupportSentence (P X Y Z : Carrier) (ξ υ ζ : Graph)
    (a : RawPolynomial) (g : TernaryGraph) : ArithmeticSentence :=
  let F := rawFiber P X Y ξ υ a
  “∀ p u z, !g.val p u z → !F.val p u ∧ !Z.val z ∧ !ζ.val z p”

def operationTotalSentence (P X Y : Carrier) (ξ υ : Graph)
    (a : RawPolynomial) (g : TernaryGraph) : ArithmeticSentence :=
  let F := rawFiber P X Y ξ υ a
  “∀ p u, !F.val p u → ∃! z, !g.val p u z”

structure SliceAlgebra (T : ArithmeticTheory) (P X Y : Carrier) (a b : RawPolynomial) where
  termProjection : GraphMorphism T X P
  formulaProjection : GraphMorphism T Y P
  termOp : TernaryGraph
  formulaOp : TernaryGraph
  term_support : T ⊢ operationSupportSentence P X Y X
    termProjection.graph formulaProjection.graph termProjection.graph a termOp
  term_total : T ⊢ operationTotalSentence P X Y
    termProjection.graph formulaProjection.graph a termOp
  formula_support : T ⊢ operationSupportSentence P X Y Y
    termProjection.graph formulaProjection.graph formulaProjection.graph b formulaOp
  formula_total : T ⊢ operationTotalSentence P X Y
    termProjection.graph formulaProjection.graph b formulaOp

namespace SliceAlgebra
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

def TermFiber (p x : M) : Prop :=
  X.val.Evalb ![x] ∧ A.termProjection.graph.val.Evalb ![x, p]

def FormulaFiber (p y : M) : Prop :=
  Y.val.Evalb ![y] ∧ A.formulaProjection.graph.val.Evalb ![y, p]

theorem term_support_model (p u x : M) (h : A.termOp.val.Evalb ![p, u, x]) :
    (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph a).val.Evalb ![p, u] ∧
      A.TermFiber p x := by
  have hs := consequence_iff.mp (Theory.Proof.sound A.term_support) M inferInstance
  have hs' : ∀ p u x : M, A.termOp.val.Evalb ![p, u, x] →
      (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph a).val.Evalb ![p, u] ∧
        A.TermFiber p x := by
    simpa [models_iff, operationSupportSentence, TermFiber] using hs
  exact hs' p u x h

theorem formula_support_model (p u y : M) (h : A.formulaOp.val.Evalb ![p, u, y]) :
    (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph b).val.Evalb ![p, u] ∧
      A.FormulaFiber p y := by
  have hs := consequence_iff.mp (Theory.Proof.sound A.formula_support) M inferInstance
  have hs' : ∀ p u y : M, A.formulaOp.val.Evalb ![p, u, y] →
      (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph b).val.Evalb ![p, u] ∧
        A.FormulaFiber p y := by
    simpa [models_iff, operationSupportSentence, FormulaFiber] using hs
  exact hs' p u y h

theorem term_total_model (p u : M)
    (h : (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph a).val.Evalb ![p, u]) :
    ∃! x : M, A.termOp.val.Evalb ![p, u, x] := by
  have ht := consequence_iff.mp (Theory.Proof.sound A.term_total) M inferInstance
  have ht' : ∀ p u : M,
      (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph a).val.Evalb ![p, u] →
        ∃! x : M, A.termOp.val.Evalb ![p, u, x] := by
    simpa [models_iff, operationTotalSentence] using ht
  exact ht' p u h

theorem formula_total_model (p u : M)
    (h : (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph b).val.Evalb ![p, u]) :
    ∃! y : M, A.formulaOp.val.Evalb ![p, u, y] := by
  have ht := consequence_iff.mp (Theory.Proof.sound A.formula_total) M inferInstance
  have ht' : ∀ p u : M,
      (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph b).val.Evalb ![p, u] →
        ∃! y : M, A.formulaOp.val.Evalb ![p, u, y] := by
    simpa [models_iff, operationTotalSentence] using ht
  exact ht' p u h

theorem term_functional_model (p u x x' : M)
    (h : A.termOp.val.Evalb ![p, u, x]) (h' : A.termOp.val.Evalb ![p, u, x']) : x = x' :=
  (A.term_total_model p u (A.term_support_model p u x h).1).unique h h'

theorem formula_functional_model (p u y y' : M)
    (h : A.formulaOp.val.Evalb ![p, u, y]) (h' : A.formulaOp.val.Evalb ![p, u, y']) : y = y' :=
  (A.formula_total_model p u (A.formula_support_model p u y h).1).unique h h'

end Models
end SliceAlgebra
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
