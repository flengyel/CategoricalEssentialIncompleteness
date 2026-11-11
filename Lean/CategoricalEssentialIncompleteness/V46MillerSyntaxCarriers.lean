/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxSource

/-! # Original postfix words with arbitrary uniformly enumerable coefficients

The carrier uses the original numerical parser and a positive finite
record of actual coefficient predicates. Coefficient objects need not
come from ordinary arithmetic predicates. Successful-word coordinates
contain no membership or computation witnesses.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

def wordGuard (p q : SyntaxPolynomial (Total.TotalCategory P)) (word : ℕ) : Prop :=
  ∀ record ∈ Nat.natToList word,recordValid p q record

theorem wordGuard_enumerable (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    Uniform.Enumerable P (wordGuard p q) :=
  Uniform.Enumerable.comp (f := Nat.natToList) Primrec.nat_natToList.to_comp (recordValid_enumerable p q).listAll

def uniformWords (formula : Bool) (p q : SyntaxPolynomial (Total.TotalCategory P)) : Total.Carrier P where
  support := {word | wordGuard p q word ∧
    Postfix.run (skeleton p) (skeleton q) word 1=adjoin (Nat.pair word (if formula then 1 else 0)) 0+1}
  enumerable := by
    have hr : Primrec (fun word : ℕ => Postfix.run (skeleton p) (skeleton q) word 1) :=
      (NatVectors.run_primrec (skeleton p) (skeleton q)).comp Primrec.id (.const 1)
    have hs : Primrec (fun word : ℕ => adjoin (Nat.pair word (if formula then 1 else 0)) 0+1) :=
      Primrec.succ.comp (NatVectors.adjoin_primrec.comp
        (Primrec₂.natPair.comp Primrec.id (.const (if formula then 1 else 0))) (.const 0))
    exact (wordGuard_enumerable p q).and
      (Uniform.Enumerable.of_re ((Primrec.eq.comp hr hs).computablePred.to_re))

@[simp] theorem uniformWords_mem (formula : Bool) (p q : SyntaxPolynomial (Total.TotalCategory P)) (word : ℕ) :
    word ∈ (uniformWords formula p q).support ↔ wordGuard p q word ∧
      Postfix.run (skeleton p) (skeleton q) word 1=adjoin (Nat.pair word (if formula then 1 else 0)) 0+1 := Iff.rfl

def uniformWordFamily (R : Total.TotalCategory P) (formula : Bool) (p q : SyntaxPolynomial (Total.TotalCategory P)) : Over R :=
  Over.mk (Total.totalFst R (⟨uniformWords formula p q⟩ : Total.TotalCategory P))

theorem uniformWords_coefficientWord {R : Total.TotalCategory P} (formula : Bool)
    (p q : SyntaxPolynomial (Total.TotalCategory P)) (r word : ℕ)
    (hr : r ∈ R.obj.support) (hw : word ∈ (uniformWords formula p q).support) :
    coefficientWord (R := R) (p := p) (q := q) (Nat.pair r word) := by
  simpa only [coefficientWord,wordGuard,Nat.unpair_pair] using And.intro hr hw.1

theorem uniformWords_singleton {R : Total.TotalCategory P} {X Y : Over R}
    {p q : SyntaxPolynomial (Total.TotalCategory P)}
    (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)
    (formula : Bool) {r word new : ℕ}
    (hw : word ∈ (uniformWords formula p q).support)
    (hn : new ∈ evaluation hT hF (Nat.pair r word)) :
    ∃ value,new=adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 :=
  evaluation_singleton hT hF formula hn hw.2

theorem uniformWords_mapped (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) (word : ℕ) :
    word ∈ (uniformWords formula (a.mapCoefficients (predicateFunctor P).obj)
      (b.mapCoefficients (predicateFunctor P).obj)).support ↔ word ∈ (words P formula a b).support := by
  constructor
  · rintro ⟨hguard,hparser⟩
    have hnodes : ∀ i<len word,(Coding.recordCarrier a b).val.Evalb (M := ℕ) ![nth word i] := by
      intro i hi
      have hil : i<(Nat.natToList word).length := by simpa only [NatVectors.len_eq_decode] using hi
      have hm : nth word i ∈ Nat.natToList word := by
        rw [NatVectors.nth_eq_decode,List.getD_eq_getElem (Nat.natToList word) 0 hil]
        exact List.getElem_mem hil
      exact (mapped_record a b (nth word i)).mp (hguard _ hm)
    have hcoeff := (FiniteSigmaOne.finite_membership_model (Coding.recordCarrier a b) word).mp
      ((FiniteSigmaOne.allEntriesCondition_eval (Coding.recordCarrier a b) word).mpr hnodes)
    have hrun : Postfix.run a b word 1=adjoin (Nat.pair word (if formula then 1 else 0)) 0+1 := by
      exact (run_skeleton_mapped a b (predicateFunctor P).obj word 1).symm.trans hparser
    apply (Postfix.carrier_plain_model formula a b word).mp
    exact (Postfix.carrier_eval formula a b word).mpr ⟨hcoeff,by simpa only [nat_pair_eq] using hrun⟩
  · intro hw
    have hg := source_coefficientWord (R := (⟨Total.terminalCarrier (P := P)⟩ : Total.TotalCategory P))
      a b formula 0 word (by simp [Total.terminalCarrier]) hw
    exact ⟨by simpa only [wordGuard,Nat.unpair_pair] using hg.2,
      source_parser_success a b formula word hw⟩

theorem uniformWords_mapped_support (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) :
    (uniformWords formula (a.mapCoefficients (predicateFunctor P).obj)
      (b.mapCoefficients (predicateFunctor P).obj)).support=(words P formula a b).support := by
  ext word
  exact uniformWords_mapped a b formula word

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
