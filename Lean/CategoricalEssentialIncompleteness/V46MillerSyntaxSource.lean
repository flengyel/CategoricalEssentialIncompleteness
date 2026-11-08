/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxPresentation
import CategoricalEssentialIncompleteness.V46MillerSyntaxSimulation
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationParser

/-! # Original accepted words supply the actual evaluator hypotheses

This compares the positive coefficient guard and the full parser run,
including its stored-word check. It does not add an acceptance or a
correctness field to an algebra. Coefficient names and child order are
unchanged throughout the comparisons.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

theorem skeleton_mapped (Q : SyntacticSyntax.RawPolynomial)
    (F : SyntacticPredicates.Carrier → Total.TotalCategory P) :
    skeleton (Q.mapCoefficients F)=Q.mapCoefficients (fun _ => Coding.zeroCarrier) := by
  induction Q with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit => rfl
  | product a b ia ib => simp only [skeleton,SyntaxPolynomial.mapCoefficients] at *;rw [ia,ib]
  | sum a b ia ib => simp only [skeleton,SyntaxPolynomial.mapCoefficients] at *;rw [ia,ib]

theorem run_skeleton_mapped (a b : SyntacticSyntax.RawPolynomial)
    (F : SyntacticPredicates.Carrier → Total.TotalCategory P) (word initial : ℕ) :
    Postfix.run (skeleton (a.mapCoefficients F)) (skeleton (b.mapCoefficients F)) word initial=
      Postfix.run a b word initial := by
  rw [skeleton_mapped,skeleton_mapped]
  exact NumericalDerivationInterpretation.Parser.run_map (fun _ => Coding.zeroCarrier) a b word initial

theorem mapped_coefficient_support (C : SyntacticPredicates.Carrier) (u : ℕ) :
    u ∈ ((predicateFunctor P).obj C).obj.support ↔ C.val.Evalb (M := ℕ) ![u] := by
  rw [predicateFunctor_object]
  rfl

theorem mapped_shape_support (a : SyntacticSyntax.RawPolynomial) (s : ℕ) :
    s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P))
      (a.mapCoefficients (predicateFunctor P).obj)).support ↔
        (SyntacticSyntax.rawCarrier Coding.zeroCarrier Coding.zeroCarrier a).val.Evalb (M := ℕ) ![s] := by
  induction a generalizing s with
  | term => simp [SyntaxPolynomial.mapCoefficients,carrier,Total.terminalCarrier,SyntacticSyntax.rawCarrier,Coding.zeroCarrier]
  | formula => simp [SyntaxPolynomial.mapCoefficients,carrier,Total.terminalCarrier,SyntacticSyntax.rawCarrier,Coding.zeroCarrier]
  | coefficient C => exact mapped_coefficient_support C s
  | unit => simp [SyntaxPolynomial.mapCoefficients,carrier,Total.terminalCarrier,SyntacticSyntax.rawCarrier]
  | product a b ia ib =>
      rw [SyntacticSyntax.rawCarrier_product_eval]
      constructor
      · intro hs
        exact ⟨(Nat.unpair s).1,(Nat.unpair s).2,by simp [nat_pair_eq],(ia _).mp hs.1,(ib _).mp hs.2⟩
      · rintro ⟨u,v,he,hu,hv⟩
        rw [he]
        simpa only [SyntaxPolynomial.mapCoefficients,carrier,Total.product,Set.mem_ofPred_eq,nat_pair_eq,Nat.unpair_pair] using
          And.intro ((ia u).mpr hu) ((ib v).mpr hv)
  | sum a b ia ib =>
      rw [SyntacticSyntax.rawCarrier_sum_eval]
      constructor
      · rintro (⟨hk,hu⟩ | ⟨hk,hv⟩)
        · exact Or.inl ⟨(Nat.unpair s).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair s).symm,(ia _).mp hu⟩
        · exact Or.inr ⟨(Nat.unpair s).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair s).symm,(ib _).mp hv⟩
      · rintro (⟨u,he,hu⟩ | ⟨v,he,hv⟩)
        · rw [he]
          change (_ ∧ _) ∨ (_ ∧ _)
          apply Or.inl
          constructor
          · simp only [nat_pair_eq,Nat.unpair_pair]
          · simpa only [nat_pair_eq,Nat.unpair_pair] using (ia u).mpr hu
        · rw [he]
          change (_ ∧ _) ∨ (_ ∧ _)
          apply Or.inr
          constructor
          · simp only [nat_pair_eq,Nat.unpair_pair]
          · simpa only [nat_pair_eq,Nat.unpair_pair] using (ib v).mpr hv

theorem mapped_record (a b : SyntacticSyntax.RawPolynomial) (record : ℕ) :
    recordValid (a.mapCoefficients (predicateFunctor P).obj) (b.mapCoefficients (predicateFunctor P).obj) record ↔
      (Coding.recordCarrier a b).val.Evalb (M := ℕ) ![record] := by
  rw [Coding.recordCarrier_eval]
  simp only [recordValid,mapped_shape_support,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq]

theorem source_coefficientWord {R : Total.TotalCategory P} (a b : SyntacticSyntax.RawPolynomial)
    (formula : Bool) (r word : ℕ) (hr : r ∈ R.obj.support)
    (hw : word ∈ (words P formula a b).support) :
    coefficientWord (R := R) (p := a.mapCoefficients (predicateFunctor P).obj)
      (q := b.mapCoefficients (predicateFunctor P).obj) (Nat.pair r word) := by
  have hc := ((Postfix.plainCarrier_eval formula a b word).mp hw).1
  have hnodes : ∀ i<len word,(Coding.recordCarrier a b).val.Evalb (M := ℕ) ![nth word i] :=
    (FiniteSigmaOne.allEntriesCondition_eval (Coding.recordCarrier a b) word).mp
      ((FiniteSigmaOne.finite_membership_model (Coding.recordCarrier a b) word).mpr hc)
  refine ⟨by simpa only [Nat.unpair_pair] using hr,?_⟩
  simp only [Nat.unpair_pair]
  intro record hrecord
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hrecord
  have hiw : i.val<len word := by simpa only [NatVectors.len_eq_decode] using i.isLt
  have hn := hnodes i.val hiw
  have he : nth word i.val=record := by rw [NatVectors.nth_eq_decode,List.getD_eq_get];exact hi
  exact (mapped_record a b record).mpr (he ▸ hn)

theorem source_parser_success (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) (word : ℕ)
    (hw : word ∈ (words P formula a b).support) :
    Postfix.run (skeleton (a.mapCoefficients (predicateFunctor P).obj))
      (skeleton (b.mapCoefficients (predicateFunctor P).obj)) word 1=
        adjoin (Nat.pair word (if formula then 1 else 0)) 0+1 := by
  rw [run_skeleton_mapped]
  have hs := (Postfix.carrier_plain_model formula a b word).mpr hw
  simpa only [nat_pair_eq] using ((Postfix.carrier_eval formula a b word).mp hs).2

theorem source_evaluation_singleton {R : Total.TotalCategory P} {X Y : Over R}
    (a b : SyntacticSyntax.RawPolynomial)
    (hT : object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
    (hF : object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)
    (formula : Bool) {r word new : ℕ}
    (hw : word ∈ (words P formula a b).support)
    (hn : new ∈ evaluation hT hF (Nat.pair r word)) :
    ∃ value,new=adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 :=
  evaluation_singleton hT hF formula hn (source_parser_success a b formula word hw)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
