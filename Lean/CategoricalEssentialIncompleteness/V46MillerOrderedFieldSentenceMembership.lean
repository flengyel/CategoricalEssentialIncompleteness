import CategoricalEssentialIncompleteness.V46MillerOrderedFieldSyntax
import Mathlib.Computability.Primrec.List

/-! # Primitive-recursive membership in the actual ordered-field sentence words

The parser runs on the original postfix records. Its label test uses the
explicit bounded field signature, and the empty free-variable test is the
existing primitive-recursive traversal. No decision certificate for the
sentence set is an input.
-/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSentenceMembership
open OrderedFieldSyntax SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.Postfix
open SyntacticSyntax.NatVectors

private def recursiveCoefficients : RawPolynomial → Prop
  | .term => True
  | .formula => True
  | .coefficient C => PrimrecPred (fun n : ℕ => C.val.Evalb ![n])
  | .unit => True
  | .product a b => recursiveCoefficients a ∧ recursiveCoefficients b
  | .sum a b => recursiveCoefficients a ∧ recursiveCoefficients b

private theorem raw_product_nat (a b : RawPolynomial) (n : ℕ) :
    (rawCarrier zeroCarrier zeroCarrier (.product a b)).val.Evalb ![n] ↔
      (rawCarrier zeroCarrier zeroCarrier a).val.Evalb ![π₁ n] ∧
        (rawCarrier zeroCarrier zeroCarrier b).val.Evalb ![π₂ n] := by
  rw [rawCarrier_product_eval]
  constructor
  · rintro ⟨u,v,he,hu,hv⟩
    subst n
    simpa using And.intro hu hv
  · rintro ⟨hu,hv⟩
    exact ⟨π₁ n,π₂ n,(pair_unpair n).symm,hu,hv⟩

private theorem raw_sum_nat (a b : RawPolynomial) (n : ℕ) :
    (rawCarrier zeroCarrier zeroCarrier (.sum a b)).val.Evalb ![n] ↔
      (π₂ n=0 ∧ (rawCarrier zeroCarrier zeroCarrier a).val.Evalb ![π₁ n]) ∨
        (π₂ n=1 ∧ (rawCarrier zeroCarrier zeroCarrier b).val.Evalb ![π₁ n]) := by
  rw [rawCarrier_sum_eval]
  constructor
  · rintro (⟨u,he,hu⟩ | ⟨v,he,hv⟩)
    · subst n
      apply Or.inl
      constructor
      · simp
      · simpa using hu
    · subst n
      apply Or.inr
      constructor
      · simp
      · simpa using hv
  · rintro (⟨hk,hu⟩ | ⟨hk,hv⟩)
    · exact Or.inl ⟨π₁ n,by simpa only [hk] using (pair_unpair n).symm,hu⟩
    · exact Or.inr ⟨π₁ n,by simpa only [hk] using (pair_unpair n).symm,hv⟩

private theorem raw_primrec (p : RawPolynomial) (hp : recursiveCoefficients p) :
    PrimrecPred (fun n : ℕ => (rawCarrier zeroCarrier zeroCarrier p).val.Evalb ![n]) := by
  revert hp
  induction p with
  | term => intro _; simpa [rawCarrier,zeroCarrier] using
      (Primrec.eq.comp (Primrec.id : Primrec (id : ℕ → ℕ)) (Primrec.const 0))
  | formula => intro _; simpa [rawCarrier,zeroCarrier] using
      (Primrec.eq.comp (Primrec.id : Primrec (id : ℕ → ℕ)) (Primrec.const 0))
  | coefficient C => intro hp; exact hp
  | unit => intro _; simpa [rawCarrier] using
      (Primrec.eq.comp (Primrec.id : Primrec (id : ℕ → ℕ)) (Primrec.const 0))
  | product a b ia ib =>
      intro hp
      exact ((ia hp.1).comp pi1_primrec |>.and ((ib hp.2).comp pi2_primrec)).of_eq
        (fun n => (raw_product_nat a b n).symm)
  | sum a b ia ib =>
      intro hp
      exact (((Primrec.eq.comp pi2_primrec (Primrec.const 0)).and
        ((ia hp.1).comp pi1_primrec)).or
        ((Primrec.eq.comp pi2_primrec (Primrec.const 1)).and
          ((ib hp.2).comp pi1_primrec))).of_eq (fun n => (raw_sum_nat a b n).symm)

private theorem variable_leaf : PrimrecPred
    (fun n : ℕ => variableSymbols.val.Evalb ![n]) := by
  simpa [variableSymbols,NamedPostfixEncoding.variableCarrier] using
    (Primrec.eq.comp (Primrec.const 0 : Primrec (fun _ : ℕ => (0 : ℕ))) (Primrec.const 0))

private theorem function_leaf (k : ℕ) : PrimrecPred
    (fun n : ℕ => (functionSymbols k).val.Evalb ![n]) :=
  functionSymbols_primrec.comp (Primrec.pair (Primrec.const k) Primrec.id)

private theorem relation_leaf (k : ℕ) : PrimrecPred
    (fun n : ℕ => (relationSymbols k).val.Evalb ![n]) :=
  relationSymbols_primrec.comp (Primrec.pair (Primrec.const k) Primrec.id)

private theorem term_coefficients : recursiveCoefficients
    (NamedPostfixEncoding.termPolynomial functionSymbols bound) := by
  simp only [NamedPostfixEncoding.termPolynomial,SyntaxPolynomial.termExpression,
    SyntaxPolynomial.constructors,SyntaxPolynomial.power,recursiveCoefficients,
    and_true]
  exact ⟨variable_leaf,⟨⟨function_leaf 0,function_leaf 1⟩,function_leaf 2⟩⟩

private theorem formula_coefficients : recursiveCoefficients
    (NamedPostfixEncoding.formulaPolynomial relationSymbols bound) := by
  simp only [NamedPostfixEncoding.formulaPolynomial,SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.constructors,SyntaxPolynomial.power,recursiveCoefficients,
    true_and,and_true]
  exact ⟨⟨⟨relation_leaf 0,relation_leaf 1⟩,relation_leaf 2⟩,variable_leaf⟩

private theorem record_primrec : PrimrecPred (fun n : ℕ =>
    (recordCarrier (NamedPostfixEncoding.termPolynomial functionSymbols bound)
      (NamedPostfixEncoding.formulaPolynomial relationSymbols bound)).val.Evalb ![n]) := by
  simpa only [rawCarrier,recordCarrier] using
    raw_primrec (.sum (NamedPostfixEncoding.termPolynomial functionSymbols bound)
      (NamedPostfixEncoding.formulaPolynomial relationSymbols bound))
        ⟨term_coefficients,formula_coefficients⟩

private theorem coefficients_primrec : PrimrecPred (fun word : ℕ =>
    (coefficients (NamedPostfixEncoding.termPolynomial functionSymbols bound)
      (NamedPostfixEncoding.formulaPolynomial relationSymbols bound)).val.Evalb ![word]) := by
  have hi : PrimrecRel (fun i word : ℕ =>
      (recordCarrier (NamedPostfixEncoding.termPolynomial functionSymbols bound)
        (NamedPostfixEncoding.formulaPolynomial relationSymbols bound)).val.Evalb ![nth word i]) :=
    record_primrec.comp (nth_primrec.comp Primrec.snd Primrec.fst)
  exact (hi.forall_lt.comp len_primrec Primrec.id).of_eq (fun word => by
    rw [coefficients,← FiniteSigmaOne.finite_membership_model,
      FiniteSigmaOne.allEntriesCondition_eval]
    rfl)

/-- The exact accepted formula-word set, including the stored-word check. -/
theorem formula_membership_primrec : PrimrecPred (fun word : ℕ =>
    (Postfix.plainCarrier true (NamedPostfixEncoding.termPolynomial functionSymbols bound)
      (NamedPostfixEncoding.formulaPolynomial relationSymbols bound)).val.Evalb ![word]) := by
  let a := NamedPostfixEncoding.termPolynomial functionSymbols bound
  let b := NamedPostfixEncoding.formulaPolynomial relationSymbols bound
  have hr : Primrec (fun word : ℕ => run a b word 1) :=
    (run_primrec a b).comp Primrec.id (Primrec.const 1)
  have hs : Primrec (fun word : ℕ => adjoin (Arithmetic.pair word 1) 0+1) :=
    Primrec.succ.comp (adjoin_primrec.comp
      (pair_primrec.comp Primrec.id (Primrec.const 1)) (Primrec.const 0))
  exact (coefficients_primrec.and (Primrec.eq.comp hr hs)).of_eq (fun word => by
    rw [← carrier_plain_model,carrier_eval]
    rfl)

/-- Primitive-recursive membership in the literal recursive sentence carrier. -/
theorem sentence_membership_primrec : PrimrecPred
    (fun word : ℕ => sentencePredicate.val.Evalb ![word]) :=
  (formula_membership_primrec.and (Primrec.eq.comp
    (ConcreteNamedSubstitution.freeVariables_primrec variableSymbols
      functionSymbols relationSymbols bound) (Primrec.const 0))).of_eq
        (fun word => (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
          variableSymbols functionSymbols relationSymbols bound ℕ word).symm)

/-- An ordinary total decision program for the full literal set, with no
restriction to already decoded syntax inputs. -/
theorem sentence_membership_computable : ∃ dec : ℕ → Bool,
    Computable dec ∧ ∀ word,dec word=true ↔ sentencePredicate.val.Evalb ![word] := by
  obtain ⟨inst,h⟩ := sentence_membership_primrec
  let := inst
  exact ⟨fun word => decide (sentencePredicate.val.Evalb ![word]),h.to_comp,by simp⟩

end CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSentenceMembership
