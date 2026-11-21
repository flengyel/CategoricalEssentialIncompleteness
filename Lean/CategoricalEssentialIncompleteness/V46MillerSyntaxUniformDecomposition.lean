/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxCarrierConstructors
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition

/-! # Decomposition with arbitrary uniform coefficient guards

Erasing guards is used only for the proved ordinary parser decomposition. Every
coefficient guard is recovered from the root record, and all child guards are
inherited from their subwords. The carrier keeps exactly the original numerical word
coordinate.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

theorem guard_constructor_split (p q Q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) (u : ℕ) :
    wordGuard p q (constructor formula (skeleton Q) u) ↔
      wordGuard p q (childrenWord (skeleton Q) u) ∧
        recordValid p q (Nat.pair (shape (skeleton Q) u) (if formula then 1 else 0)) := by
  simp only [constructor,wordGuard,natToList_concat,List.forall_mem_append,
    List.mem_singleton,forall_eq,nat_pair_eq]

/-- Guards and structural parser membership reconstruct the full polynomial input,
including all nonrecursive coefficient predicates. -/
theorem rawInput_of_erased (p q Q : SyntaxPolynomial (Total.TotalCategory P)) {u : ℕ}
    (hu : (SyntacticSyntax.rawCarrier (Postfix.carrier false (erased p) (erased q))
      (Postfix.carrier true (erased p) (erased q)) (erased Q)).val.Evalb (M := ℕ) ![u])
    (hg : wordGuard p q (childrenWord (skeleton Q) u))
    (hs : shape (skeleton Q) u ∈
      (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) Q).support) :
    u ∈ (carrier (uniformWords false p q) (uniformWords true p q) Q).support := by
  induction Q generalizing u with
  | term =>
      have hr := ((Postfix.carrier_eval false (erased p) (erased q) u).mp hu).2
      exact ⟨hg,by simpa only [erased_run,nat_pair_eq] using hr⟩
  | formula =>
      have hr := ((Postfix.carrier_eval true (erased p) (erased q) u).mp hu).2
      exact ⟨hg,by simpa only [erased_run,nat_pair_eq] using hr⟩
  | coefficient _ => simpa [skeleton,SyntaxPolynomial.mapCoefficients,shape,carrier] using hs
  | unit =>
      simpa [erased,skeleton,SyntaxPolynomial.mapCoefficients,SyntacticSyntax.rawCarrier,
        carrier,Total.terminalCarrier] using hu
  | product c d ic id =>
      obtain ⟨x,y,rfl,hx,hy⟩ := (SyntacticSyntax.rawCarrier_product_eval _ _ (erased c) (erased d) u).mp hu
      have hgc : wordGuard p q (childrenWord (skeleton c) x) ∧
          wordGuard p q (childrenWord (skeleton d) y) := by
        simpa only [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,nat_pair_eq,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq,wordGuard_append,Nat.unpair_pair] using hg
      have hsc : shape (skeleton c) x ∈
          (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) c).support ∧
          shape (skeleton d) y ∈
          (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) d).support := by
        simpa [carrier,Total.product,skeleton,SyntaxPolynomial.mapCoefficients,shape,nat_pair_eq,
          FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hs
      simpa [carrier,Total.product,nat_pair_eq] using
        And.intro (ic hx hgc.1 hsc.1) (id hy hgc.2 hsc.2)
  | sum c d ic id =>
      rcases (SyntacticSyntax.rawCarrier_sum_eval _ _ (erased c) (erased d) u).mp hu with
        ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · have hgc : wordGuard p q (childrenWord (skeleton c) x) := by
          simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,nat_pair_eq,
            FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hg
        have hsc : shape (skeleton c) x ∈
            (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) c).support := by
          simpa [carrier,taggedSum,skeleton,SyntaxPolynomial.mapCoefficients,shape,nat_pair_eq,
            FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hs
        simpa [carrier,taggedSum,nat_pair_eq] using ic hx hgc hsc
      · have hgc : wordGuard p q (childrenWord (skeleton d) y) := by
          simpa [skeleton,SyntaxPolynomial.mapCoefficients,childrenWord,nat_pair_eq,
            FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hg
        have hsc : shape (skeleton d) y ∈
            (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) d).support := by
          simpa [carrier,taggedSum,skeleton,SyntaxPolynomial.mapCoefficients,shape,nat_pair_eq,
            FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hs
        simpa [carrier,taggedSum,nat_pair_eq] using id hy hgc hsc

theorem uniformWords_decomposition (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) {word : ℕ}
    (hw : word ∈ (uniformWords formula p q).support) :
    ∃ u : ℕ,u ∈ (carrier (uniformWords false p q) (uniformWords true p q)
      (if formula then q else p)).support ∧
      word=constructor formula (skeleton (if formula then q else p)) u := by
  have he := uniformWords_erased formula p q hw
  obtain ⟨u,hu,hword⟩ := Postfix.carrier_decomposition formula (erased p) (erased q) word he
  have hctor : constructor formula (if formula then erased q else erased p) u=
      constructor formula (skeleton (if formula then q else p)) u := by
    cases formula
    · exact erased_constructor p false u
    · exact erased_constructor q true u
  have hw' := hword.trans hctor
  have hguard : wordGuard p q (constructor formula (skeleton (if formula then q else p)) u) :=
    hw' ▸ hw.1
  obtain ⟨hg,hr⟩ := (guard_constructor_split p q (if formula then q else p) formula u).mp hguard
  have hs : shape (skeleton (if formula then q else p)) u ∈
      (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P))
        (if formula then q else p)).support := by
    cases formula <;> simpa [recordValid,Nat.unpair_pair] using hr
  have hu' : (SyntacticSyntax.rawCarrier (Postfix.carrier false (erased p) (erased q))
      (Postfix.carrier true (erased p) (erased q)) (erased (if formula then q else p))).val.Evalb (M := ℕ) ![u] := by
    cases formula <;> simpa using hu
  exact ⟨u,rawInput_of_erased p q (if formula then q else p) hu' hg hs,hw'⟩

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
