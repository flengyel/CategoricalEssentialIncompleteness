/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxCarriers
import CategoricalEssentialIncompleteness.V46MillerSyntaxChildren
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # Literal constructor membership for arbitrary uniform coefficients

Coefficient guards are forgotten only in the auxiliary ordinary parser
used to prove a structural computation equation. Actual word membership
retains the original arbitrary uniform coefficient predicates.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

def erased (p : SyntaxPolynomial (Total.TotalCategory P)) : SyntacticSyntax.RawPolynomial :=
  (skeleton p).mapCoefficients (fun _ => topCarrier)

theorem erased_constructor (p : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) (u : ℕ) :
    constructor formula (erased p) u=constructor formula (skeleton p) u :=
  NumericalDerivationInterpretation.Parser.constructor_map (fun _ => topCarrier) (skeleton p) formula u

theorem erased_run (p q : SyntaxPolynomial (Total.TotalCategory P)) (word initial : ℕ) :
    Postfix.run (erased p) (erased q) word initial=Postfix.run (skeleton p) (skeleton q) word initial :=
  NumericalDerivationInterpretation.Parser.run_map (fun _ => topCarrier) (skeleton p) (skeleton q) word initial

theorem shape_carrier (X Y : Total.Carrier P) (p : SyntaxPolynomial (Total.TotalCategory P)) {u : ℕ}
    (hu : u ∈ (carrier X Y p).support) :
    shape (skeleton p) u ∈
      (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support := by
  induction p generalizing u with
  | term => simp [skeleton,SyntaxPolynomial.mapCoefficients,shape,carrier,Total.terminalCarrier]
  | formula => simp [skeleton,SyntaxPolynomial.mapCoefficients,shape,carrier,Total.terminalCarrier]
  | coefficient _ => exact hu
  | unit => simp [skeleton,SyntaxPolynomial.mapCoefficients,shape,carrier,Total.terminalCarrier]
  | product c d ic id =>
      simpa only [skeleton,SyntaxPolynomial.mapCoefficients,shape,carrier,Total.product,Set.mem_ofPred_eq,
        nat_pair_eq,Nat.unpair_pair,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using
        And.intro (ic hu.1) (id hu.2)
  | sum c d ic id =>
      rcases hu with ⟨hk,hv⟩ | ⟨hk,hv⟩
      · change (_ ∧ _) ∨ (_ ∧ _)
        apply Or.inl
        simpa [skeleton,SyntaxPolynomial.mapCoefficients,shape,nat_pair_eq,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hk] using And.intro (rfl : (0 : ℕ)=0) (ic hv)
      · change (_ ∧ _) ∨ (_ ∧ _)
        apply Or.inr
        simpa [skeleton,SyntaxPolynomial.mapCoefficients,shape,nat_pair_eq,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hk] using And.intro (rfl : (1 : ℕ)=1) (id hv)

theorem shape_support_erased (p : SyntaxPolynomial (Total.TotalCategory P)) {s : ℕ}
    (hs : s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support) :
    (SyntacticSyntax.rawCarrier Coding.zeroCarrier Coding.zeroCarrier (erased p)).val.Evalb (M := ℕ) ![s] := by
  induction p generalizing s with
  | term => simpa [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,
      Coding.zeroCarrier,carrier,Total.terminalCarrier] using hs
  | formula => simpa [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,
      Coding.zeroCarrier,carrier,Total.terminalCarrier] using hs
  | coefficient _ => simp [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,topCarrier]
  | unit => simpa [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,
      carrier,Total.terminalCarrier] using hs
  | product c d ic id =>
      exact (SyntacticSyntax.rawCarrier_product_eval _ _ (erased c) (erased d) s).mpr
        ⟨(Nat.unpair s).1,(Nat.unpair s).2,by simp [nat_pair_eq],ic hs.1,id hs.2⟩
  | sum c d ic id =>
      rcases hs with ⟨hk,hv⟩ | ⟨hk,hv⟩
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased c) (erased d) s).mpr
          (Or.inl ⟨(Nat.unpair s).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair s).symm,ic hv⟩)
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased c) (erased d) s).mpr
          (Or.inr ⟨(Nat.unpair s).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair s).symm,id hv⟩)

theorem recordValid_erased (p q : SyntaxPolynomial (Total.TotalCategory P)) {record : ℕ}
    (h : recordValid p q record) : (Coding.recordCarrier (erased p) (erased q)).val.Evalb (M := ℕ) ![record] := by
  apply (Coding.recordCarrier_eval (erased p) (erased q) record).mpr
  simpa only [FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using
    h.elim (fun h => Or.inl ⟨h.1,shape_support_erased p h.2⟩)
      (fun h => Or.inr ⟨h.1,shape_support_erased q h.2⟩)

theorem uniformWords_erased (formula : Bool) (p q : SyntaxPolynomial (Total.TotalCategory P)) {word : ℕ}
    (hw : word ∈ (uniformWords formula p q).support) :
    (Postfix.carrier formula (erased p) (erased q)).val.Evalb (M := ℕ) ![word] := by
  have hnodes : ∀ i<len word,(Coding.recordCarrier (erased p) (erased q)).val.Evalb (M := ℕ) ![nth word i] := by
    intro i hi
    have hil : i<(Nat.natToList word).length := by simpa only [len_eq_decode] using hi
    have hm : nth word i ∈ Nat.natToList word := by
      rw [nth_eq_decode,List.getD_eq_getElem (Nat.natToList word) 0 hil]
      exact List.getElem_mem hil
    exact recordValid_erased p q (hw.1 _ hm)
  have hcoeff := (FiniteSigmaOne.finite_membership_model (Coding.recordCarrier (erased p) (erased q)) word).mp
    ((FiniteSigmaOne.allEntriesCondition_eval (Coding.recordCarrier (erased p) (erased q)) word).mpr hnodes)
  apply (Postfix.carrier_eval formula (erased p) (erased q) word).mpr
  exact ⟨hcoeff,by simpa only [erased_run,nat_pair_eq] using hw.2⟩

theorem rawInput_erased (p q Q : SyntaxPolynomial (Total.TotalCategory P)) {u : ℕ}
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) Q).support) :
    (SyntacticSyntax.rawCarrier (Postfix.carrier false (erased p) (erased q))
      (Postfix.carrier true (erased p) (erased q)) (erased Q)).val.Evalb (M := ℕ) ![u] := by
  induction Q generalizing u with
  | term => exact uniformWords_erased false p q hu
  | formula => exact uniformWords_erased true p q hu
  | coefficient _ => simp [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,topCarrier]
  | unit => simpa [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,
      carrier,Total.terminalCarrier] using hu
  | product c d ic id =>
      exact (SyntacticSyntax.rawCarrier_product_eval _ _ (erased c) (erased d) u).mpr
        ⟨(Nat.unpair u).1,(Nat.unpair u).2,by simp [nat_pair_eq],ic hu.1,id hu.2⟩
  | sum c d ic id =>
      rcases hu with ⟨hk,hv⟩ | ⟨hk,hv⟩
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased c) (erased d) u).mpr
          (Or.inl ⟨(Nat.unpair u).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair u).symm,ic hv⟩)
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased c) (erased d) u).mpr
          (Or.inr ⟨(Nat.unpair u).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair u).symm,id hv⟩)

theorem wordGuard_append (p q : SyntaxPolynomial (Total.TotalCategory P)) (left right : ℕ) :
    wordGuard p q (Words.append left right) ↔ wordGuard p q left ∧ wordGuard p q right := by
  simp only [wordGuard,natToList_append,List.forall_mem_append]

theorem wordGuard_children (p q Q : SyntaxPolynomial (Total.TotalCategory P)) {u : ℕ}
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) Q).support) :
    wordGuard p q (childrenWord (skeleton Q) u) := by
  induction Q generalizing u with
  | term => exact hu.1
  | formula => exact hu.1
  | coefficient _ => simp [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,wordGuard,Nat.natToList]
  | unit => simp [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,wordGuard,Nat.natToList]
  | product c d ic id =>
      simpa only [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,wordGuard_append,
        FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using And.intro (ic hu.1) (id hu.2)
  | sum c d ic id =>
      rcases hu with ⟨hk,hv⟩ | ⟨hk,hv⟩
      · simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,FiniteSigmaOne.nat_pi₁_eq,
          NatVectors.nat_pi₂_eq,hk] using ic hv
      · simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,FiniteSigmaOne.nat_pi₁_eq,
          NatVectors.nat_pi₂_eq,hk] using id hv

theorem wordGuard_constructor (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) {u : ℕ}
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support) :
    wordGuard p q (constructor formula (skeleton (if formula then q else p)) u) := by
  have hc := wordGuard_children p q (if formula then q else p) hu
  have hs := shape_carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p) hu
  have hr : recordValid p q (Nat.pair (shape (skeleton (if formula then q else p)) u) (if formula then 1 else 0)) := by
    cases formula
    · exact Or.inl ⟨by simp,by simpa using hs⟩
    · exact Or.inr ⟨by simp,by simpa using hs⟩
  simpa only [constructor,wordGuard,natToList_concat,List.forall_mem_append,List.mem_singleton,
    forall_eq,nat_pair_eq] using And.intro hc hr

theorem uniformWords_constructor (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) {u : ℕ}
    (hu : u ∈ (carrier (uniformWords false p q) (uniformWords true p q) (if formula then q else p)).support) :
    constructor formula (skeleton (if formula then q else p)) u ∈ (uniformWords formula p q).support := by
  have he := rawInput_erased p q (if formula then q else p) hu
  have hs : (Postfix.carrier formula (erased p) (erased q)).val.Evalb (M := ℕ)
      ![constructor formula (erased (if formula then q else p)) u] := by
    cases formula
    · exact Postfix.term_constructor_carrier (erased p) (erased q) u he
    · exact Postfix.formula_constructor_carrier (erased p) (erased q) u he
  have hp := ((Postfix.carrier_eval formula (erased p) (erased q) _).mp hs).2
  refine ⟨wordGuard_constructor p q formula hu,?_⟩
  simpa only [erased_run,erased_constructor,nat_pair_eq] using hp

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
