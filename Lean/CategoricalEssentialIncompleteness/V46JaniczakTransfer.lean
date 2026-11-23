/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakLanguage

/-!
# Finite-variable comparison of equivalence structures

A partial assignment records equality, equality of class labels and the specified small classes. Reservoirs supply a new member or a new class whenever the next variable requires one.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak

private theorem exists_outside {Y : Type*} {b : ℕ} {f : Fin (b+1) → Y}
    (hf : Function.Injective f) (v : Fin b → Y) :
    ∃ j, ∀ i, f j ≠ v i := by
  classical
  by_contra! h
  choose g hg using h
  have hi : Function.Injective g := fun i j hij ↦ hf ((hg i).trans ((congrArg v hij).trans (hg j).symm))
  have := Fintype.card_le_of_injective g hi
  simp at this

namespace Transfer

variable {X K : Type*} (key : X → K) (small : K → Prop) (b : ℕ)

structure Reservoir (D : X → Prop) : Prop where
  small_mem : ∀ x, small (key x) → D x
  members : ∀ x, D x → ¬ small (key x) →
    ∃ f : Fin (b+1) → X, Function.Injective f ∧ ∀ j, D (f j) ∧ key (f j) = key x
  classes : ∃ f : Fin (b+1) → X, Function.Injective (key ∘ f) ∧
    ∀ j, D (f j) ∧ ¬ small (key (f j))

structure Matches (v w : ℕ → X) : Prop where
  elems : ∀ i j : Fin b, v i = v j ↔ w i = w j
  labels : ∀ i j : Fin b, key (v i) = key (v j) ↔ key (w i) = key (w j)
  keep : ∀ i : Fin b, small (key (v i)) ∨ small (key (w i)) → v i = w i

structure Move (v w : ℕ → X) (a c : X) : Prop where
  elems : ∀ i : Fin b, a = v i ↔ c = w i
  labels : ∀ i : Fin b, key a = key (v i) ↔ key c = key (w i)
  keep : small (key a) ∨ small (key c) → a = c

variable {key small b}

theorem Matches.symm {v w : ℕ → X} (h : Matches key small b v w) : Matches key small b w v :=
  ⟨fun i j ↦ (h.elems i j).symm, fun i j ↦ (h.labels i j).symm,
    fun i hi ↦ (h.keep i hi.symm).symm⟩

theorem Matches.ident (v : ℕ → X) : Matches key small b v v :=
  ⟨fun _ _ ↦ Iff.rfl, fun _ _ ↦ Iff.rfl, fun _ _ ↦ rfl⟩

theorem choose_move {D : X → Prop} {v w : ℕ → X}
    (h : Matches key small b v w) (r : Reservoir key small b D)
    (hw : ∀ i : Fin b, D (w i)) (a : X) :
    ∃ c, D c ∧ Move key small b v w a c := by
  classical
  by_cases same : ∃ j : Fin b, a = v j
  · obtain ⟨j,rfl⟩ := same
    exact ⟨w j, hw j, h.elems j, h.labels j, h.keep j⟩
  by_cases sa : small (key a)
  · refine ⟨a, r.small_mem _ sa, ?_, ?_, fun _ ↦ rfl⟩
    · intro i
      constructor
      · intro e
        exact e.trans (h.keep i (Or.inl (e ▸ sa)))
      · intro e
        exact e.trans (h.keep i (Or.inr (e ▸ sa))).symm
    · intro i
      constructor
      · intro e
        exact e.trans (congrArg key (h.keep i (Or.inl (e ▸ sa))))
      · intro e
        exact e.trans (congrArg key (h.keep i (Or.inr (e ▸ sa)))).symm
  by_cases sameClass : ∃ j : Fin b, key a = key (v j)
  · obtain ⟨j,e⟩ := sameClass
    have large : ¬small (key (w j)) := fun hs ↦
      sa ((e.trans (congrArg key (h.keep j (Or.inr hs)))).symm ▸ hs)
    obtain ⟨f,hf,hp⟩ := r.members (w j) (hw j) large
    obtain ⟨t,ht⟩ := exists_outside hf (fun i ↦ w i)
    refine ⟨f t, (hp t).1, ?_, ?_, ?_⟩
    · exact fun i ↦ iff_of_false (fun hi ↦ same ⟨i,hi⟩) (ht i)
    · intro i
      rw [e, (hp t).2]
      exact h.labels j i
    · exact fun hs ↦ (hs.elim sa (fun h' ↦ large ((hp t).2 ▸ h'))).elim
  · obtain ⟨f,hf,hp⟩ := r.classes
    obtain ⟨t,ht⟩ := exists_outside hf (fun i ↦ key (w i))
    refine ⟨f t, (hp t).1, ?_, ?_, ?_⟩
    · exact fun i ↦ iff_of_false (fun hi ↦ same ⟨i,hi⟩) (fun hi ↦ ht i (congrArg key hi))
    · exact fun i ↦ iff_of_false (fun hi ↦ sameClass ⟨i,hi⟩) (ht i)
    · exact fun hs ↦ (hs.elim sa (hp t).2).elim

theorem Matches.update {v w : ℕ → X} {a c : X} (h : Matches key small b v w)
    (m : Move key small b v w a c) (x : ℕ) :
    Matches key small b (Function.update v x a) (Function.update w x c) := by
  constructor
  · intro i j
    by_cases hi : i.val = x <;> by_cases hj : j.val = x
    · simp [hi,hj]
    · simpa [hi,hj,Function.update_of_ne] using m.elems j
    · simpa [hi,hj,eq_comm,Function.update_of_ne] using m.elems i
    · simpa [hi,hj,Function.update_of_ne] using h.elems i j
  · intro i j
    by_cases hi : i.val = x <;> by_cases hj : j.val = x
    · simp [hi,hj]
    · simpa [hi,hj,Function.update_of_ne] using m.labels j
    · simpa [hi,hj,eq_comm,Function.update_of_ne] using m.labels i
    · simpa [hi,hj,Function.update_of_ne] using h.labels i j
  · intro i
    by_cases hi : i.val = x
    · simpa [hi] using m.keep
    · simpa [hi,Function.update_of_ne] using h.keep i

end Transfer

namespace Formula

/-- Every variable in the formula, free or bound, has index below `b`. -/
def Below (b : ℕ) : Formula → Prop
  | equal x y | related x y => x < b ∧ y < b
  | top => True
  | neg p => Below b p
  | conj p q => Below b p ∧ Below b q
  | ex x p => x < b ∧ Below b p

/-- Satisfaction when quantifiers range over `D`. -/
def Restricted {X : Type*} (E : X → X → Prop) (D : X → Prop) (v : ℕ → X) : Formula → Prop
  | equal x y => v x = v y
  | related x y => E (v x) (v y)
  | top => True
  | neg p => ¬ p.Restricted E D v
  | conj p q => p.Restricted E D v ∧ q.Restricted E D v
  | ex x p => ∃ a, D a ∧ p.Restricted E D (Function.update v x a)

theorem restricted_univ {X : Type*} (E : X → X → Prop) (v : ℕ → X) (p : Formula) :
    p.Restricted E (fun _ ↦ True) v ↔ p.Holds E v := by
  induction p generalizing v with
  | equal | related | top => rfl
  | neg p ih => exact not_congr (ih v)
  | conj p q ih jh => exact and_congr (ih v) (jh v)
  | ex x p ih => simp [Restricted, Holds, ih]

theorem restricted_transfer {X K : Type*} {key : X → K} {small : K → Prop} {b : ℕ}
    {D F : X → Prop} (rd : Transfer.Reservoir key small b D)
    (rf : Transfer.Reservoir key small b F) (p : Formula) (hb : Below b p)
    {v w : ℕ → X} (h : Transfer.Matches key small b v w)
    (hv : ∀ i : Fin b, D (v i)) (hw : ∀ i : Fin b, F (w i)) :
    p.Restricted (fun x y ↦ key x = key y) D v ↔
      p.Restricted (fun x y ↦ key x = key y) F w := by
  induction p generalizing v w with
  | equal x y => exact h.elems ⟨x,hb.1⟩ ⟨y,hb.2⟩
  | related x y => exact h.labels ⟨x,hb.1⟩ ⟨y,hb.2⟩
  | top => rfl
  | neg p ih => exact not_congr (ih hb h hv hw)
  | conj p q ih jh => exact and_congr (ih hb.1 h hv hw) (jh hb.2 h hv hw)
  | ex x p ih =>
    have upd {T : X → Prop} {u : ℕ → X} {a : X} (hu : ∀ i : Fin b, T (u i)) (ha : T a) :
        ∀ i : Fin b, T (Function.update u x a i) := by
      intro i
      by_cases e : i.val = x
      · simpa [e] using ha
      · simpa [Function.update_of_ne e] using hu i
    constructor
    · rintro ⟨a,ha,hp⟩
      obtain ⟨c,hc,m⟩ := Transfer.choose_move h rf hw a
      exact ⟨c,hc,(ih hb.2 (h.update m x) (upd hv ha) (upd hw hc)).mp hp⟩
    · rintro ⟨c,hc,hp⟩
      obtain ⟨a,ha,m⟩ := Transfer.choose_move h.symm rd hv c
      exact ⟨a,ha,(ih hb.2 ((h.symm.update m x).symm) (upd hv ha) (upd hw hc)).mpr hp⟩

end Formula
end Janiczak
