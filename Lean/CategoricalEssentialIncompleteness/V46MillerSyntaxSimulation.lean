/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxTrace
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSimulation

/-! # The actual uniform evaluator preserves the original parser skeleton

The simulation is numerical and uses no definability condition on algebra
operations. A literal successful parser output forces exactly one value
of the same sort; it cannot be an error or an unrelated value stack.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)

theorem outcome_sorts {a : SyntaxPolynomial (Total.TotalCategory P)} {Z : Over R}
    (h : object R X Y a ⟶ Z) (formula : Bool) (r s parserStack valueStack new : ℕ)
    (hs : sorts parserStack=sorts valueStack)
    (hn : new ∈ outcome h formula (r,(s,valueStack))) :
    statusSort (Postfix.step (skeleton a) (skeleton a)
      (Nat.pair s (if formula then 1 else 0)) (parserStack+1))=statusSort new := by
  have he := Coding.refill_sorts (skeleton a) s parserStack valueStack hs
  rcases (outcome_graph h formula r s valueStack new).mp hn with ⟨hf,rfl⟩ | ⟨u,rest,value,hf,_,rfl⟩
  · dsimp [refill] at hf
    rcases nil_or_adjoin (refill a s parserStack) with hp | ⟨v,tail,hp⟩
    · dsimp [refill] at hp
      cases formula <;> simp_all [Postfix.step,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq]
    · dsimp [refill] at hp
      simp [hp,hf] at he
  · dsimp [refill] at hf
    rcases nil_or_adjoin (refill a s parserStack) with hp | ⟨v,tail,hp⟩
    · dsimp [refill] at hp
      simp [hp,hf] at he
    · dsimp [refill] at hp
      have ht : sorts tail=sorts rest := by simpa [hp,hf] using he
      cases formula <;> simp_all [Postfix.step,nat_pair_eq,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq]

theorem valueStep_sorts (r record parsed old new : ℕ)
    (hs : statusSort parsed=statusSort old)
    (hn : new ∈ valueStep hT hF (r,(record,old))) :
    statusSort (Postfix.step (skeleton p) (skeleton q) record parsed)=statusSort new := by
  by_cases hz : old=0
  · have hnew : new=0 := by simpa [hz,valueStep] using hn
    have hp : parsed=0 := (statusSort_eq_zero parsed).mp (by simpa [hz] using hs)
    simp [hp,hnew]
  · obtain ⟨stack,hstack⟩ := Nat.exists_eq_succ_of_ne_zero hz
    subst old
    rcases Nat.eq_zero_or_pos parsed with hpz | hpp
    · simp [hpz] at hs
    · obtain ⟨parserStack,hparser⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpp)
      subst parsed
      have hsort : sorts parserStack=sorts stack := by simpa using hs
      by_cases hk0 : (Nat.unpair record).2=0
      · have ho : new ∈ outcome hT false (r,((Nat.unpair record).1,stack)) := by
          simpa [valueStep,hk0] using hn
        have hrec : record=Nat.pair (Nat.unpair record).1 0 := by
          simpa only [hk0] using (Nat.pair_unpair record).symm
        have h := outcome_sorts hT false r (Nat.unpair record).1 parserStack stack new hsort ho
        rw [hrec]
        simpa [Postfix.step,nat_pair_eq,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using h
      · by_cases hk1 : (Nat.unpair record).2=1
        · have ho : new ∈ outcome hF true (r,((Nat.unpair record).1,stack)) := by
            simpa [valueStep,hk0,hk1] using hn
          have hrec : record=Nat.pair (Nat.unpair record).1 1 := by
            simpa only [hk1] using (Nat.pair_unpair record).symm
          have h := outcome_sorts hF true r (Nat.unpair record).1 parserStack stack new hsort ho
          rw [hrec]
          simpa [Postfix.step,nat_pair_eq,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using h
        · have hnew : new=0 := by simpa [valueStep,hk0,hk1] using hn
          have h0 : π₂ record≠0 := by simpa only [NatVectors.nat_pi₂_eq] using hk0
          have h1 : π₂ record≠1 := by simpa only [NatVectors.nat_pi₂_eq] using hk1
          simp [Postfix.step,h0,h1,hnew]

theorem valueRecord_sorts {x n : ℕ} {states : List ℕ}
    (h : UniformTrees.Record (loopStep hT hF) (fun _ => 1) x n states) :
    statusSort (Postfix.runPrefix (skeleton p) (skeleton q) (Nat.unpair x).2 n 1)=
      statusSort (states.getD n 0) := by
  have hh : ∀ i,i≤n →
      statusSort (Postfix.runPrefix (skeleton p) (skeleton q) (Nat.unpair x).2 i 1)=
        statusSort (states.getD i 0) := by
    intro i
    induction i with
    | zero =>
        intro _
        simp only [Postfix.prefix_zero]
        rw [h.2.1]
    | succ i ih =>
        intro hi
        have hil : i<n := by omega
        have hs := h.2.2 i hil
        change states.getD (i+1) 0 ∈ valueStep hT hF
          ((Nat.unpair x).1,(nth (Nat.unpair x).2 i,states.getD i 0)) at hs
        simpa only [Postfix.prefix_succ] using valueStep_sorts hT hF (Nat.unpair x).1
          (nth (Nat.unpair x).2 i)
          (Postfix.runPrefix (skeleton p) (skeleton q) (Nat.unpair x).2 i 1)
          (states.getD i 0) (states.getD (i+1) 0) (ih (by omega)) hs
  exact hh n le_rfl

theorem evaluation_sorts {r word new : ℕ}
    (hn : new ∈ evaluation hT hF (Nat.pair r word)) :
    statusSort (Postfix.run (skeleton p) (skeleton q) word 1)=statusSort new := by
  obtain ⟨states,hs,hnew⟩ := (evaluation_graph hT hF (Nat.pair r word) new).mp hn
  have he := valueRecord_sorts hT hF hs
  simp only [loopLength,Nat.unpair_pair] at he hnew
  rw [hnew] at he
  exact he

theorem evaluation_singleton (formula : Bool) {r word new : ℕ}
    (hn : new ∈ evaluation hT hF (Nat.pair r word))
    (hword : Postfix.run (skeleton p) (skeleton q) word 1=
      adjoin (Nat.pair word (if formula then 1 else 0)) 0+1) :
    ∃ value,new=adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 := by
  have he := evaluation_sorts hT hF hn
  rw [hword] at he
  rcases Nat.eq_zero_or_pos new with hz | hpos
  · simp [hz] at he
  · obtain ⟨stack,hstack⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hs : adjoin (if formula then 1 else 0) 0=sorts stack := by
      simpa [hstack,nat_pair_eq,NatVectors.nat_pi₂_eq] using he
    rcases nil_or_adjoin stack with hz | ⟨block,tail,ht⟩
    · simp [hz] at hs
    · have hb : (if formula then 1 else 0)=π₂ block ∧ (0 : ℕ)=sorts tail := by
        exact (adjoin_inj _ _ _ _).mp (by simpa [ht] using hs)
      have htail : tail=0 := (sorts_eq_zero tail).mp hb.2.symm
      refine ⟨π₁ block,?_⟩
      simpa [ht,htail,hb.1,FiniteSigmaOne.nat_pi₁_eq,NatVectors.nat_pi₂_eq] using hstack

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
