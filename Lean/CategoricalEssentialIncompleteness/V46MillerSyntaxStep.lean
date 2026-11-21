/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxState

/-! # A uniformly represented postfix step for arbitrary slice operations

Zero is a structural error status; one plus a stack is a successful
status. Every successful constructor, including a nullary one, invokes
the supplied algebra morphism. Its values are not built into an ordinary
recursive initial state or an ordinary recursive transition function.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}

private theorem represented_ite {A B : OracleComputation.Ty}
    (Q : A.carrier → Prop) [DecidablePred Q] (hQ : ComputablePred Q)
    {f g : A.carrier → Part B.carrier}
    (hf : Uniform.Represented P A B f) (hg : Uniform.Represented P A B g) :
    Uniform.Represented P A B (fun a => if Q a then f a else g a) := by
  apply (Uniform.represented_iff_graph_enumerable P A B _).mpr
  have hl := ((Uniform.Enumerable.of_re hQ.to_re).comp Computable.fst).and
    ((Uniform.represented_iff_graph_enumerable P A B _).mp hf)
  have hr := ((Uniform.Enumerable.of_re hQ.not.to_re).comp Computable.fst).and
    ((Uniform.represented_iff_graph_enumerable P A B _).mp hg)
  exact (hl.or hr).of_eq (fun a => by by_cases h : Q a.1 <;> simp [h])

abbrev StepInput := ℕ × (ℕ × ℕ)

def outcome {p : SyntaxPolynomial (Total.TotalCategory P)} {Z : Over R}
    (h : object R X Y p ⟶ Z) (formula : Bool) (a : StepInput) : Part ℕ :=
  let l := refill p a.2.1 a.2.2
  if l=0 then Part.some (0 : ℕ) else
    (operation h (a.1,(fstIdx (V := ℕ)) l)).map
      (fun value => adjoin (Nat.pair value (if formula then 1 else 0)) ((sndIdx (V := ℕ)) l)+1)

theorem outcome_represented {p : SyntaxPolynomial (Total.TotalCategory P)} {Z : Over R}
    (h : object R X Y p ⟶ Z) (formula : Bool) :
    Uniform.Represented P (.product .nat (.product .nat .nat)) .nat (outcome h formula) := by
  have hl : Primrec (fun a : StepInput => refill p a.2.1 a.2.2) :=
    (refill_primrec p).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hc : Computable (fun a : StepInput => (a.1,(fstIdx (V := ℕ)) (refill p a.2.1 a.2.2))) :=
    (Primrec.pair Primrec.fst (fstIdx_primrec.comp hl)).to_comp
  have hr : Computable (fun a : StepInput => (sndIdx (V := ℕ)) (refill p a.2.1 a.2.2)) :=
    (sndIdx_primrec.comp hl).to_comp
  have hc' : Uniform.Represented P (.product .nat (.product .nat .nat)) (.product .nat .nat)
      (fun a : StepInput => Part.some (a.1,(fstIdx (V := ℕ)) (refill p a.2.1 a.2.2))) :=
    Uniform.Represented.of_partrec hc.partrec
  have hv : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat
      (fun a : StepInput => operation h (a.1,(fstIdx (V := ℕ)) (refill p a.2.1 a.2.2))) :=
    (Uniform.Represented.comp hc' (operation_represented h)).of_eq
      (fun _ => Part.bind_some ..)
  have hr' : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat
      (fun a : StepInput => Part.some ((sndIdx (V := ℕ)) (refill p a.2.1 a.2.2))) :=
    Uniform.Represented.of_partrec hr.partrec
  have hp := Uniform.Represented.pair hv hr'
  have hb : Computable (fun a : ℕ × ℕ =>
      adjoin (Nat.pair a.1 (if formula then 1 else 0)) a.2+1) :=
    (Primrec.succ.comp (adjoin_primrec.comp
      (Primrec₂.natPair.comp Primrec.fst (.const (if formula then 1 else 0))) Primrec.snd)).to_comp
  have hb' : Uniform.Represented P (.product .nat .nat) .nat
      (fun a : ℕ × ℕ => Part.some (adjoin (Nat.pair a.1 (if formula then 1 else 0)) a.2+1)) :=
    Uniform.Represented.of_partrec hb.partrec
  have hsuccess := Uniform.Represented.comp hp hb'
  have hz : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat
      (fun _ : StepInput => Part.some (0 : ℕ)) :=
    Uniform.Represented.of_partrec (Computable.const (0 : ℕ)).partrec
  apply represented_ite (P := P) (A := .product .nat (.product .nat .nat)) (B := .nat)
    (fun a : StepInput => refill p a.2.1 a.2.2=0)
    ((Primrec.eq.comp hl (.const 0)).computablePred) hz
  exact hsuccess.of_eq (fun _ => by
    simp only [Part.map_some,Part.bind_some_eq_map,Part.bind_map]
    rfl)

theorem outcome_graph {p : SyntaxPolynomial (Total.TotalCategory P)} {Z : Over R}
    (h : object R X Y p ⟶ Z) (formula : Bool) (r s stack new : ℕ) :
    new ∈ outcome h formula (r,(s,stack)) ↔
      (refill p s stack=0 ∧ new=0) ∨ ∃ u rest value,
        refill p s stack=adjoin u rest ∧ value ∈ operation h (r,u) ∧
          new=adjoin (Nat.pair value (if formula then 1 else 0)) rest+1 := by
  rcases nil_or_adjoin (refill p s stack) with hz | ⟨u,rest,hl⟩
  · simp [outcome,hz]
  · simp [outcome,hl,Part.mem_map_iff,eq_comm]

theorem outcome_exists {p : SyntaxPolynomial (Total.TotalCategory P)}
    (h : object R X Y p ⟶ X) (r s stack : ℕ)
    (hr : r ∈ R.obj.support)
    (hs : s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support)
    (hst : fiberStack R X Y (r,stack)) :
    ∃ new,new ∈ outcome h false (r,(s,stack)) ∧ status R X Y (r,new) := by
  rcases nil_or_adjoin (refill p s stack) with hz | ⟨u,rest,hl⟩
  · exact ⟨0,(outcome_graph h false r s stack 0).mpr (Or.inl ⟨hz,rfl⟩),
      (status_zero R X Y r).mpr hr⟩
  · obtain ⟨hu,hrest⟩ := refill_fiber R X Y p r s stack u rest hr hs hst hl
    obtain ⟨v,hv⟩ := operation_exists h hu
    refine ⟨adjoin (Nat.pair v 0) rest+1,
      (outcome_graph h false r s stack _).mpr (Or.inr ⟨u,rest,v,hl,hv,rfl⟩),?_⟩
    apply (status_succ R X Y r _).mpr
    exact ⟨hr,(fiberStack_adjoin R X Y r _ rest).mpr
      ⟨(fiberBlock_term R X Y r v).mpr (operation_parameter h hv),hrest⟩⟩

theorem formulaOutcome_exists {p : SyntaxPolynomial (Total.TotalCategory P)}
    (h : object R X Y p ⟶ Y) (r s stack : ℕ)
    (hr : r ∈ R.obj.support)
    (hs : s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support)
    (hst : fiberStack R X Y (r,stack)) :
    ∃ new,new ∈ outcome h true (r,(s,stack)) ∧ status R X Y (r,new) := by
  rcases nil_or_adjoin (refill p s stack) with hz | ⟨u,rest,hl⟩
  · exact ⟨0,(outcome_graph h true r s stack 0).mpr (Or.inl ⟨hz,rfl⟩),
      (status_zero R X Y r).mpr hr⟩
  · obtain ⟨hu,hrest⟩ := refill_fiber R X Y p r s stack u rest hr hs hst hl
    obtain ⟨v,hv⟩ := operation_exists h hu
    refine ⟨adjoin (Nat.pair v 1) rest+1,
      (outcome_graph h true r s stack _).mpr (Or.inr ⟨u,rest,v,hl,hv,rfl⟩),?_⟩
    apply (status_succ R X Y r _).mpr
    exact ⟨hr,(fiberStack_adjoin R X Y r _ rest).mpr
      ⟨(fiberBlock_formula R X Y r v).mpr (operation_parameter h hv),hrest⟩⟩

variable {p q : SyntaxPolynomial (Total.TotalCategory P)}

def recordValid (p q : SyntaxPolynomial (Total.TotalCategory P)) (record : ℕ) : Prop :=
  ((Nat.unpair record).2=0 ∧ (Nat.unpair record).1 ∈
    (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support) ∨
  ((Nat.unpair record).2=1 ∧ (Nat.unpair record).1 ∈
    (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) q).support)

theorem recordValid_enumerable (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    Uniform.Enumerable P (recordValid p q) :=
  ((Uniform.Enumerable.of_re ((Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 0)).computablePred.to_re)).and
    (Uniform.Enumerable.comp (Computable.fst.comp Computable.unpair)
      (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).enumerable)).or
  ((Uniform.Enumerable.of_re ((Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (.const 1)).computablePred.to_re)).and
    (Uniform.Enumerable.comp (Computable.fst.comp Computable.unpair)
      (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) q).enumerable))

def valueStep (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)
    (a : StepInput) : Part ℕ :=
  if a.2.2=0 then Part.some (0 : ℕ) else
    if (Nat.unpair a.2.1).2=0 then
      outcome hT false (a.1,((Nat.unpair a.2.1).1,a.2.2-1))
    else if (Nat.unpair a.2.1).2=1 then
      outcome hF true (a.1,((Nat.unpair a.2.1).1,a.2.2-1))
    else Part.some (0 : ℕ)

theorem valueStep_represented (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y) :
    Uniform.Represented P (.product .nat (.product .nat .nat)) .nat (valueStep hT hF) := by
  have hin : Computable (fun a : StepInput => (a.1,((Nat.unpair a.2.1).1,a.2.2-1))) :=
    (Primrec.pair Primrec.fst (Primrec.pair
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.snd) (.const 1)))).to_comp
  have hin' : Uniform.Represented P (.product .nat (.product .nat .nat))
      (.product .nat (.product .nat .nat))
      (fun a : StepInput => Part.some (a.1,((Nat.unpair a.2.1).1,a.2.2-1))) :=
    Uniform.Represented.of_partrec hin.partrec
  have hT' : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat
      (fun a : StepInput => outcome hT false (a.1,((Nat.unpair a.2.1).1,a.2.2-1))) :=
    (Uniform.Represented.comp hin' (outcome_represented hT false)).of_eq
      (fun _ => Part.bind_some ..)
  have hF' : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat
      (fun a : StepInput => outcome hF true (a.1,((Nat.unpair a.2.1).1,a.2.2-1))) :=
    (Uniform.Represented.comp hin' (outcome_represented hF true)).of_eq
      (fun _ => Part.bind_some ..)
  have hz : Uniform.Represented P (.product .nat (.product .nat .nat)) .nat
      (fun _ : StepInput => Part.some (0 : ℕ)) :=
    Uniform.Represented.of_partrec (Computable.const (0 : ℕ)).partrec
  have ht : Primrec (fun a : StepInput => (Nat.unpair a.2.1).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
  have hF'' := represented_ite (P := P) (A := .product .nat (.product .nat .nat)) (B := .nat)
    (fun a : StepInput => (Nat.unpair a.2.1).2=1)
    ((Primrec.eq.comp ht (.const 1)).computablePred) hF' hz
  have hTF := represented_ite (P := P) (A := .product .nat (.product .nat .nat)) (B := .nat)
    (fun a : StepInput => (Nat.unpair a.2.1).2=0)
    ((Primrec.eq.comp ht (.const 0)).computablePred) hT' hF''
  exact represented_ite (P := P) (A := .product .nat (.product .nat .nat)) (B := .nat)
    (fun a : StepInput => a.2.2=0)
    ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (.const 0)).computablePred) hz hTF

theorem valueStep_exists (hT : object R X Y p ⟶ X) (hF : object R X Y q ⟶ Y)
    (r record old : ℕ) (hrc : recordValid p q record) (hold : status R X Y (r,old)) :
    ∃ new,new ∈ valueStep hT hF (r,(record,old)) ∧ status R X Y (r,new) := by
  have hr := hold.1
  by_cases hz : old=0
  · exact ⟨0,by simp [valueStep,hz],(status_zero R X Y r).mpr hr⟩
  · have hst : fiberStack R X Y (r,old-1) := hold.2.resolve_left hz
    rcases hrc with ⟨hk,hs⟩ | ⟨hk,hs⟩
    · obtain ⟨new,hn,hns⟩ := outcome_exists hT r (Nat.unpair record).1 (old-1) hr hs hst
      exact ⟨new,by simpa [valueStep,hz,hk] using hn,hns⟩
    · obtain ⟨new,hn,hns⟩ := formulaOutcome_exists hF r (Nat.unpair record).1 (old-1) hr hs hst
      exact ⟨new,by simpa [valueStep,hz,hk] using hn,hns⟩

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
