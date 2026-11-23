/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakReduction
public import CategoricalEssentialIncompleteness.V46JaniczakClosure
public import Mathlib.Tactic.FinCases
public import Foundation.FirstOrder.SetTheory.Basic.Misc
public import Foundation.FirstOrder.LK.Completeness.CounterModel

/-! # First-order provability for Janiczak's named formulas

Foundation's relational language with equality and one further binary symbol has
the required signature. We interpret the second symbol as the given relation.
The equality axioms belong to the logical base of the translated theory.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.Entailment
namespace Janiczak.FOL

abbrev L := Language.set

/-- Each name is interpreted by a de Bruijn variable in the current context. -/
abbrev Names (n : ℕ) := ℕ → Fin n

def underBinder {n : ℕ} (ρ : Names n) (x : ℕ) : Names (n+1) :=
  fun y => if y = x then 0 else (ρ y).succ

def initialNames (bound : ℕ) : Names (bound+1) :=
  fun i => ⟨i % (bound+1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def translate : (p : Janiczak.Formula) → {n : ℕ} → Names n → Semisentence L n
  | .equal x y, _, ρ => .rel Language.Set.Rel.eq ![.bvar (ρ x),.bvar (ρ y)]
  | .related x y, _, ρ => .rel Language.Set.Rel.mem ![.bvar (ρ x),.bvar (ρ y)]
  | .top, _, _ => ⊤
  | .neg p, _, ρ => ∼(translate p ρ)
  | .conj p q, _, ρ => translate p ρ ⋏ translate q ρ
  | .ex x p, _, ρ => ∃¹ (translate p (underBinder ρ x))

/-- Universally quantify the name context, which contains every variable of p. -/
def sentence (p : Janiczak.Formula) : Sentence L := ∀¹* (translate p (initialNames p.code))

def theory (T : Set Janiczak.Formula) : Theory L := 𝗘𝗤 L ∪ sentence '' T

def relation {M : Type} [s : Tarski.Structure L M] (x y : M) : Prop :=
  s.rel Language.Set.Rel.mem ![x,y]

private theorem values_underBinder {M : Type} {n : ℕ} (ρ : Names n) (x : ℕ)
    (b : Fin n → M) (a : M) :
    (a :> b) ∘ underBinder ρ x = Function.update (b ∘ ρ) x a := by
  funext y
  by_cases h : y = x
  · simp [underBinder, h]
  · simp [underBinder, h]

theorem translate_eval {M : Type} [s : Tarski.Structure L M] [Tarski.Structure.Eq L M]
    (p : Janiczak.Formula) {n : ℕ} (ρ : Names n) (b : Fin n → M) :
    (translate p ρ).Evalb b ↔ p.Holds relation (b ∘ ρ) := by
  induction p generalizing n with
  | equal x y =>
    change s.rel Language.Eq.eq (Semiterm.val b Empty.elim ∘ ![.bvar (ρ x),.bvar (ρ y)]) ↔ _
    rw [Tarski.Structure.eq_lang]
    rfl
  | related x y =>
    change s.rel Language.Set.Rel.mem (Semiterm.val b Empty.elim ∘ ![.bvar (ρ x),.bvar (ρ y)]) ↔ _
    have h : (Semiterm.val (L := L) b Empty.elim ∘ ![.bvar (ρ x),.bvar (ρ y)]) =
        ![b (ρ x), b (ρ y)] := by funext i; fin_cases i <;> rfl
    rw [h]
    rfl
  | top => simp [translate, Janiczak.Formula.Holds]
  | neg p ih => simp [translate, Janiczak.Formula.Holds, ih]
  | conj p q ih jh => simp [translate, Janiczak.Formula.Holds, ih, jh]
  | ex x p ih =>
    simp only [translate, Semiformula.eval_ex, Janiczak.Formula.Holds, ih, values_underBinder]

theorem sentence_models {M : Type} [Nonempty M] [Tarski.Structure L M] [Tarski.Structure.Eq L M]
    (p : Janiczak.Formula) : M↓[L] ⊧ sentence p ↔ ∀ v : ℕ → M, p.Holds relation v := by
  rw [sentence, models_iff, Semiformula.eval_allClosure]
  constructor
  · intro h v
    have ht := (translate_eval p (initialNames p.code) (fun i => v i)).mp (h _)
    apply (Janiczak.Formula.holds_congr_below relation p
      (p.below_of_code_lt _ (Nat.lt_succ_self _)) ?_).mp ht
    intro i hi
    simp [initialNames, Nat.mod_eq_of_lt hi]
  · exact fun h b => (translate_eval p _ b).mpr (h _)

/-- Interpret the first-order signature on the carrier of a named structure. -/
@[instance_reducible] def model (M : Janiczak.Structure) : Tarski.Structure L M.Carrier where
  func := fun {_} h => Empty.elim h
  rel := fun {_} r => match r with
    | Language.Set.Rel.eq => fun v => v 0 = v 1
    | Language.Set.Rel.mem => fun v => M.rel (v 0) (v 1)

theorem equality_in_model (M : Janiczak.Structure) :
    let _ :=  model M
    Tarski.Structure.Eq L M.Carrier := by
  let _ :=  model M
  constructor
  intro a b
  rfl

theorem translated_models (M : Janiczak.Structure) (T : Set Janiczak.Formula) (hM : M.Models T) :
    let _ :=  M.inhabited
    let _ :=  model M
    M.Carrier↓[L] ⊧* theory T := by
  let _ :=  M.inhabited
  let _ :=  model M
  let _ :=  equality_in_model M
  constructor
  rintro _ (h | ⟨p, hp, rfl⟩)
  · exact (inferInstance : M.Carrier↓[L] ⊧* 𝗘𝗤 L).models _ h
  · exact (sentence_models p).mpr (hM p hp)

theorem consequence_iff_provable (T : Set Janiczak.Formula) (p : Janiczak.Formula) :
    Consequence T p ↔ theory T ⊢ sentence p := by
  constructor
  · intro hp
    let _ : 𝗘𝗤 L ⪯ theory T := inferInstanceAs (𝗘𝗤 L ⪯ (𝗘𝗤 L ∪ sentence '' T))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    let A : Janiczak.Structure := ⟨M, inferInstance, relation⟩
    apply (sentence_models p).mpr
    apply hp A
    intro q hq
    exact (sentence_models q).mp (hM.models _ (Or.inr ⟨q,hq,rfl⟩))
  · intro hp M hM
    let _ :=  M.inhabited
    let _ :=  model M
    let _ :=  equality_in_model M
    exact (sentence_models p).mp (consequence_iff.mp (Theory.Proof.sound hp) M.Carrier
      (translated_models M T hM))

theorem consistent_iff (T : Set Janiczak.Formula) :
    Janiczak.Consistent T ↔ Entailment.Consistent (theory T) := by
  constructor
  · rintro ⟨M, hM⟩
    let _ :=  M.inhabited
    let _ :=  model M
    exact consistent_iff_unprovable_bot.mpr fun hp =>
      (consequence_iff.mp (Theory.Proof.sound hp) M.Carrier (translated_models M T hM)).elim
  · intro hc
    by_contra h
    apply consistent_iff_unprovable_bot.mp hc
    let _ : 𝗘𝗤 L ⪯ theory T := inferInstanceAs (𝗘𝗤 L ⪯ (𝗘𝗤 L ∪ sentence '' T))
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    apply False.elim (h ⟨⟨M,inferInstance,relation⟩,?_⟩)
    intro q hq
    exact (sentence_models q).mp (hM.models _ (Or.inr ⟨q,hq,rfl⟩))

/-- A recursive test on named formula codes decides native first-order proofs of their universal closures. -/
def DecidableProofs (T : Set Janiczak.Formula) : Prop :=
  ∃ d : ℕ → Bool, Computable d ∧ ∀ p : Janiczak.Formula, d p.code = true ↔ theory T ⊢ sentence p

theorem decidable_theorems_iff (T : Set Janiczak.Formula) :
    DecidableTheorems T ↔ DecidableProofs T := by
  constructor
  · rintro ⟨d,hd,h⟩
    exact ⟨d,hd,fun p => (h p).trans (consequence_iff_provable T p)⟩
  · rintro ⟨d,hd,h⟩
    exact ⟨d,hd,fun p => (h p).trans (consequence_iff_provable T p).symm⟩

end Janiczak.FOL
