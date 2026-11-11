/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxFold

/-! # The actual ordered child computations of a uniform syntax constructor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable (a b : SyntacticSyntax.RawPolynomial)
variable (hT : object R X Y (a.mapCoefficients (predicateFunctor P).obj) ⟶ X)
variable (hF : object R X Y (b.mapCoefficients (predicateFunctor P).obj) ⟶ Y)

def MapValues : SyntacticSyntax.RawPolynomial → ℕ → ℕ → ℕ → Prop
  | .term,r,u,v => r ∈ R.obj.support ∧ u ∈ (words P false a b).support ∧
      adjoin (Nat.pair v 0) 0+1 ∈ evaluation hT hF (Nat.pair r u)
  | .formula,r,u,v => r ∈ R.obj.support ∧ u ∈ (words P true a b).support ∧
      adjoin (Nat.pair v 1) 0+1 ∈ evaluation hT hF (Nat.pair r u)
  | .coefficient C,r,u,v => r ∈ R.obj.support ∧ C.val.Evalb (M := ℕ) ![u] ∧ v=u
  | .unit,r,u,v => r ∈ R.obj.support ∧ u=0 ∧ v=0
  | .product c d,r,u,v =>
      MapValues c r (Nat.unpair u).1 (Nat.unpair v).1 ∧
      MapValues d r (Nat.unpair u).2 (Nat.unpair v).2
  | .sum c d,r,u,v =>
      ((Nat.unpair u).2=0 ∧ (Nat.unpair v).2=0 ∧ MapValues c r (Nat.unpair u).1 (Nat.unpair v).1) ∨
      ((Nat.unpair u).2=1 ∧ (Nat.unpair v).2=1 ∧ MapValues d r (Nat.unpair u).1 (Nat.unpair v).1)

theorem mapValues_parameter (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (h : MapValues a b hT hF Q r u v) : r ∈ R.obj.support := by
  induction Q generalizing u v with
  | term => exact h.1
  | formula => exact h.1
  | coefficient _ => exact h.1
  | unit => exact h.1
  | product _ _ ih _ => exact ih h.1
  | sum _ _ il ir => exact h.elim (fun h => il h.2.2) (fun h => ir h.2.2)

theorem mapValues_shape (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (h : MapValues a b hT hF Q r u v) : shape Q u=shape Q v := by
  induction Q generalizing u v with
  | term => rfl
  | formula => rfl
  | coefficient _ => simpa [shape] using h.2.2.symm
  | unit => rfl
  | product c d ic id =>
      simpa only [shape,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using
        congrArg₂ (fun x y : ℕ => Arithmetic.pair x y) (ic h.1) (id h.2)
  | sum c d ic id =>
      rcases h with ⟨hu,hv,hm⟩ | ⟨hu,hv,hm⟩
      · simpa [shape,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using
          congrArg (fun x : ℕ => Arithmetic.pair x 0) (ic hm)
      · simpa [shape,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using
          congrArg (fun x : ℕ => Arithmetic.pair x 1) (id hm)

theorem mapValues_source (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (h : MapValues a b hT hF Q r u v) :
    (SyntacticSyntax.rawCarrier (Postfix.plainCarrier false a b) (Postfix.plainCarrier true a b) Q).val.Evalb
      (M := ℕ) ![u] := by
  induction Q generalizing u v with
  | term => exact h.2.1
  | formula => exact h.2.1
  | coefficient _ => exact h.2.1
  | unit => simpa [SyntacticSyntax.rawCarrier] using h.2.1
  | product c d ic id =>
      exact (SyntacticSyntax.rawCarrier_product_eval _ _ c d u).mpr
        ⟨(Nat.unpair u).1,(Nat.unpair u).2,by simp [nat_pair_eq],ic h.1,id h.2⟩
  | sum c d ic id =>
      rcases h with ⟨hk,_,hm⟩ | ⟨hk,_,hm⟩
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ c d u).mpr
          (Or.inl ⟨(Nat.unpair u).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair u).symm,ic hm⟩)
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ c d u).mpr
          (Or.inr ⟨(Nat.unpair u).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair u).symm,id hm⟩)

theorem mapValues_fiber (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (h : MapValues a b hT hF Q r u v) : fiber R X Y (Q.mapCoefficients (predicateFunctor P).obj) (r,v) := by
  induction Q generalizing u v with
  | term =>
      exact selectedValue_fiber a b hT hF false h.1 h.2.1
        ((Part.mem_map_iff _).mpr ⟨_,h.2.2,extract_singleton false v⟩)
  | formula =>
      exact selectedValue_fiber a b hT hF true h.1 h.2.1
        ((Part.mem_map_iff _).mpr ⟨_,h.2.2,extract_singleton true v⟩)
  | coefficient C =>
      exact ⟨h.1,(mapped_coefficient_support C v).mpr (h.2.2.symm ▸ h.2.1)⟩
  | unit => exact ⟨h.1,h.2.2⟩
  | product c d ic id => exact ⟨ic h.1,id h.2⟩
  | sum c d ic id =>
      exact h.elim (fun h => Or.inl ⟨h.2.1,ic h.2.2⟩) (fun h => Or.inr ⟨h.2.1,id h.2.2⟩)

def topCarrier : SyntacticPredicates.Carrier := .mkSigma “x. x=x”

/-- Only the temporary recursive-value positions use the full numerical
carrier. The original coefficient guards, names, units and tags remain. -/
theorem mapValues_target_raw (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (h : MapValues a b hT hF Q r u v) :
    (SyntacticSyntax.rawCarrier topCarrier topCarrier Q).val.Evalb (M := ℕ) ![v] := by
  induction Q generalizing u v with
  | term => simp [SyntacticSyntax.rawCarrier,topCarrier]
  | formula => simp [SyntacticSyntax.rawCarrier,topCarrier]
  | coefficient _ => exact h.2.2.symm ▸ h.2.1
  | unit => simpa [SyntacticSyntax.rawCarrier] using h.2.2
  | product c d ic id =>
      exact (SyntacticSyntax.rawCarrier_product_eval _ _ c d v).mpr
        ⟨(Nat.unpair v).1,(Nat.unpair v).2,by simp [nat_pair_eq],ic h.1,id h.2⟩
  | sum c d ic id =>
      rcases h with ⟨_,hk,hm⟩ | ⟨_,hk,hm⟩
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ c d v).mpr
          (Or.inl ⟨(Nat.unpair v).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair v).symm,ic hm⟩)
      · exact (SyntacticSyntax.rawCarrier_sum_eval _ _ c d v).mpr
          (Or.inr ⟨(Nat.unpair v).1,by simpa only [nat_pair_eq,hk] using (Nat.pair_unpair v).symm,id hm⟩)

theorem mapValues_exists (Q : SyntacticSyntax.RawPolynomial) {r u : ℕ}
    (hr : r ∈ R.obj.support)
    (hu : (SyntacticSyntax.rawCarrier (Postfix.plainCarrier false a b) (Postfix.plainCarrier true a b) Q).val.Evalb
      (M := ℕ) ![u]) : ∃ v,MapValues a b hT hF Q r u v := by
  induction Q generalizing u with
  | term =>
      obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp
        (evaluation_total hT hF (source_coefficientWord a b false r u hr hu))
      obtain ⟨v,hv⟩ := source_evaluation_singleton a b hT hF false hu hs
      exact ⟨v,hr,hu,hv ▸ hs⟩
  | formula =>
      obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp
        (evaluation_total hT hF (source_coefficientWord a b true r u hr hu))
      obtain ⟨v,hv⟩ := source_evaluation_singleton a b hT hF true hu hs
      exact ⟨v,hr,hu,hv ▸ hs⟩
  | coefficient _ => exact ⟨u,hr,hu,rfl⟩
  | unit => exact ⟨0,hr,by simpa [SyntacticSyntax.rawCarrier] using hu,rfl⟩
  | product c d ic id =>
      obtain ⟨x,y,rfl,hx,hy⟩ := (SyntacticSyntax.rawCarrier_product_eval _ _ c d u).mp hu
      obtain ⟨v,hv⟩ := ic hx
      obtain ⟨w,hw⟩ := id hy
      exact ⟨Nat.pair v w,by simpa [MapValues,nat_pair_eq] using And.intro hv hw⟩
  | sum c d ic id =>
      rcases (SyntacticSyntax.rawCarrier_sum_eval _ _ c d u).mp hu with ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · obtain ⟨v,hv⟩ := ic hx
        refine ⟨Nat.pair v 0,?_⟩
        change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
        apply Or.inl
        refine ⟨?_,?_,?_⟩
        · simp only [nat_pair_eq,Nat.unpair_pair]
        · simp only [Nat.unpair_pair]
        · simpa only [nat_pair_eq,Nat.unpair_pair] using hv
      · obtain ⟨v,hv⟩ := id hy
        refine ⟨Nat.pair v 1,?_⟩
        change (_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)
        apply Or.inr
        refine ⟨?_,?_,?_⟩
        · simp only [nat_pair_eq,Nat.unpair_pair]
        · simp only [Nat.unpair_pair]
        · simpa only [nat_pair_eq,Nat.unpair_pair] using hv

theorem natToList_append (left right : ℕ) :
    Nat.natToList (Words.append left right)=Nat.natToList left++Nat.natToList right := by
  induction left using Nat.strong_induction_on with
  | h left ih =>
      cases left with
      | zero => simp [Nat.natToList]
      | succ n =>
          have he : n+1=adjoin (Nat.unpair n).1 (Nat.unpair n).2 := by
            simp [FiniteSigmaOne.canonical_adjoin,nat_pair_eq]
          rw [he,Words.append_adjoin,natToList_adjoin,natToList_adjoin]
          simp only [ih _ (Nat.lt_succ_of_le (Nat.unpair_right_le n)),List.cons_append]

theorem natToList_concat (word record : ℕ) :
    Nat.natToList (concat word record)=Nat.natToList word++[record] := by
  rw [← Words.append_singleton,natToList_append,natToList_adjoin]
  simp [Nat.natToList]

theorem children_trace (Q : SyntacticSyntax.RawPolynomial) {r u v : ℕ}
    (hm : MapValues a b hT hF Q r u v) (tail : ℕ) :
    Trace hT hF r (Nat.natToList (childrenWord Q u)) (tail+1) (childStack Q v tail+1) := by
  induction Q generalizing u v tail with
  | term =>
      have ht := (evaluation_trace hT hF r u _).mp hm.2.2
      have hf := Trace.frame hT hF ht (by simp) tail
      simpa [childrenWord,childStack,frameStatus_succ,frameStatus,nat_pair_eq] using hf
  | formula =>
      have ht := (evaluation_trace hT hF r u _).mp hm.2.2
      have hf := Trace.frame hT hF ht (by simp) tail
      simpa [childrenWord,childStack,frameStatus_succ,frameStatus,nat_pair_eq] using hf
  | coefficient _ => simpa [childrenWord,childStack,Nat.natToList] using (Trace.nil (hT := hT) (hF := hF) (r := r) (tail+1))
  | unit => simpa [childrenWord,childStack,Nat.natToList] using (Trace.nil (hT := hT) (hF := hF) (r := r) (tail+1))
  | product c d ic id =>
      have ht := Trace.append hT hF (ic hm.1 tail)
        (id hm.2 (childStack c (Nat.unpair v).1 tail))
      simpa only [childrenWord,childStack,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,natToList_append] using ht
  | sum c d ic id =>
      rcases hm with ⟨hu,hv,hm⟩ | ⟨hu,hv,hm⟩
      · simpa [childrenWord,childStack,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using ic hm tail
      · simpa [childrenWord,childStack,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,hu,hv] using id hm tail

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
