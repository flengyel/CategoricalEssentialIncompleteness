/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ForkProofTreeRecursion
import CategoricalEssentialIncompleteness.ForkSyntaxObjects

/-! # Computable proof conclusions and finite signed-leaf lists -/

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

namespace Formula

theorem atom_computable : Computable atom := by
  have h := decode_computable.comp atomCode_computable
  exact h.of_eq (fun x => decode_encode (.atom x))

theorem neg_computable : Computable neg := by
  have h := decode_computable.comp (negCode_computable.comp encode_computable)
  exact h.of_eq (fun x => decode_encode (.neg x))

theorem imp_computable : Computable (fun p : Formula × Formula => imp p.1 p.2) := by
  have hp : Computable (fun p : Formula × Formula => Nat.pair p.1.encode p.2.encode) :=
    Primrec₂.natPair.to_comp.comp (encode_computable.comp Computable.fst)
      (encode_computable.comp Computable.snd)
  have h := decode_computable.comp (impCode_computable.comp hp)
  exact h.of_eq (fun p => decode_encode (.imp p.1 p.2))

theorem imp_comp {α : Type} [Primcodable α] {f g : α → Formula}
    (hf : Computable f) (hg : Computable g) : Computable (fun a => imp (f a) (g a)) :=
  imp_computable.comp (Computable.pair hf hg)

end Formula

theorem H1_computable : Computable (fun p : Formula × Formula => H1 p.1 p.2) :=
  Formula.imp_comp Computable.fst (Formula.imp_comp Computable.snd Computable.fst)

theorem H2_computable : Computable (fun p : Formula × Formula × Formula => H2 p.1 p.2.1 p.2.2) :=
  Formula.imp_comp
    (Formula.imp_comp Computable.fst (Formula.imp_comp
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
    (Formula.imp_comp
      (Formula.imp_comp Computable.fst (Computable.fst.comp Computable.snd))
      (Formula.imp_comp Computable.fst (Computable.snd.comp Computable.snd)))

theorem H3_computable : Computable (fun p : Formula × Formula => H3 p.1 p.2) :=
  Formula.imp_comp
    (Formula.imp_comp (Formula.neg_computable.comp Computable.snd)
      (Formula.neg_computable.comp Computable.fst))
    (Formula.imp_comp Computable.fst Computable.snd)

def mpResult (p q : Formula) : Option Formula :=
  if q.encode%3=2 ∧ p.encode=(Nat.unpair (q.encode/3)).1
  then some (Formula.decode (Nat.unpair (q.encode/3)).2) else none

theorem mpResult_eq (p q : Formula) : mpResult p q=
    match q with
    | .imp a b => if a=p then some b else none
    | _ => none := by
  cases q with
  | atom x => simp [mpResult,Formula.encode]
  | neg a => simp [mpResult,Formula.encode,Nat.add_mod]
  | imp a b =>
    have hd : (3*Nat.pair a.encode b.encode+2)/3=Nat.pair a.encode b.encode := by omega
    unfold mpResult
    simp only [Formula.encode,hd,Nat.unpair_pair,Nat.add_mod,Nat.mul_mod_right,
      Nat.zero_add,Nat.reduceMod,eq_self,true_and,Formula.decode_encode]
    have he : p.encode=a.encode ↔ a=p := by
      constructor
      · intro h
        exact (Formula.codingEquiv.injective h).symm
      · intro h; rw [h]
    simp only [he]

theorem mpResult_computable : Computable (fun p : Formula × Formula => mpResult p.1 p.2) := by
  have he : Primrec Formula.encode := Primrec.of_equiv (e := Formula.codingEquiv)
  have hd : Primrec (fun p : Formula × Formula => p.2.encode/3) :=
    Primrec.nat_div.comp (he.comp Primrec.snd) (.const 3)
  have hp : PrimrecPred (fun p : Formula × Formula => p.2.encode%3=2 ∧
      p.1.encode=(Nat.unpair (p.2.encode/3)).1) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp (he.comp Primrec.snd) (.const 3)) (.const 2)).and
      (Primrec.eq.comp (he.comp Primrec.fst) (Primrec.fst.comp (Primrec.unpair.comp hd)))
  exact Formula.computable_ite hp
    (Primrec.option_some.to_comp.comp (Formula.decode_computable.comp
      ((Primrec.snd.comp (Primrec.unpair.comp hd)).to_comp))) (Computable.const none)

def mpStep (p : Option Formula × Option Formula) : Option Formula := do
  let a ← p.1
  let b ← p.2
  mpResult a b

theorem mpStep_computable : Computable mpStep := by
  have hi : Computable (fun p : (Option Formula × Option Formula) × Formula =>
      p.1.2.bind (fun q => mpResult p.2 q)) :=
    Computable.option_bind (Computable.snd.comp Computable.fst)
      (mpResult_computable.comp
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)).to₂
  exact Computable.option_bind Computable.fst hi.to₂

namespace ProofTree

theorem conclusion_computable : Computable conclusion := by
  let f := fold (fun p => some (H1 p.1 p.2)) (fun p => some (H2 p.1 p.2.1 p.2.2))
    (fun p => some (H3 p.1 p.2)) (fun x => some (.atom x))
    (fun x => some (.neg (.atom x))) mpStep
  have hf : Computable f := fold_computable
    (Primrec.option_some.to_comp.comp H1_computable)
    (Primrec.option_some.to_comp.comp H2_computable)
    (Primrec.option_some.to_comp.comp H3_computable)
    (Primrec.option_some.to_comp.comp Formula.atom_computable)
    (Primrec.option_some.to_comp.comp (Formula.neg_computable.comp Formula.atom_computable))
    mpStep_computable
  apply hf.of_eq
  intro t
  induction t with
  | logical1 | logical2 | logical3 | positive | negative => rfl
  | mp t u iht ihu =>
    change mpStep (f t,f u)=conclusion (.mp t u)
    rw [iht,ihu]
    change (conclusion t).bind (fun a => (conclusion u).bind (mpResult a))=
      (conclusion t).bind (fun a => (conclusion u).bind (fun b =>
        match b with
        | .imp c d => if c=a then some d else none
        | _ => none))
    cases conclusion t <;> cases conclusion u <;> simp only [Option.bind_none,Option.bind_some,mpResult_eq]

def positiveList : ProofTree → List ℕ :=
  fold (fun _ => []) (fun _ => []) (fun _ => []) List.singleton (fun _ => []) (fun p => p.1++p.2)

def negativeList : ProofTree → List ℕ :=
  fold (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => []) List.singleton (fun p => p.1++p.2)

theorem positiveList_computable : Computable positiveList :=
  fold_computable (Computable.const []) (Computable.const []) (Computable.const [])
    ((Primrec.list_cons.comp Primrec.id (Primrec.const [])).to_comp) (Computable.const [])
    Primrec.list_append.to_comp

theorem negativeList_computable : Computable negativeList :=
  fold_computable (Computable.const []) (Computable.const []) (Computable.const [])
    (Computable.const []) ((Primrec.list_cons.comp Primrec.id (Primrec.const [])).to_comp)
    Primrec.list_append.to_comp

theorem mem_positiveList (t : ProofTree) (x : ℕ) : x ∈ positiveList t ↔ x ∈ t.positiveLabels := by
  induction t with
  | logical1 | logical2 | logical3 | negative => simp [positiveList,fold,positiveLabels]
  | positive a => simp [positiveList,fold,positiveLabels,List.singleton]
  | mp t u iht ihu =>
    change x ∈ positiveList t++positiveList u ↔ x ∈ t.positiveLabels ∪ u.positiveLabels
    simp only [List.mem_append,Finset.mem_union,iht,ihu]

theorem mem_negativeList (t : ProofTree) (x : ℕ) : x ∈ negativeList t ↔ x ∈ t.negativeLabels := by
  induction t with
  | logical1 | logical2 | logical3 | positive => simp [negativeList,fold,negativeLabels]
  | negative a => simp [negativeList,fold,negativeLabels,List.singleton]
  | mp t u iht ihu =>
    change x ∈ negativeList t++negativeList u ↔ x ∈ t.negativeLabels ∪ u.negativeLabels
    simp only [List.mem_append,Finset.mem_union,iht,ihu]

end ProofTree
end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
