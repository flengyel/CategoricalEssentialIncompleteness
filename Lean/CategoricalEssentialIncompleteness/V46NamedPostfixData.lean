/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixEncoding
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSize

/-! # Ordered decomposition of standard polynomial payloads -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding

def RawData (X Y : ℕ → Prop) : RawPolynomial → ℕ → Prop
  | .term, u => X u
  | .formula, u => Y u
  | .coefficient C, u => C.val.Evalb ![u]
  | .unit, u => u = 0
  | .product p q, u => ∃ x y, u = Arithmetic.pair x y ∧ RawData X Y p x ∧ RawData X Y q y
  | .sum p q, u => (∃ x, u = Arithmetic.pair x 0 ∧ RawData X Y p x) ∨
      (∃ y, u = Arithmetic.pair y 1 ∧ RawData X Y q y)

theorem rawCarrier_iff_data (X Y : Carrier) (q : RawPolynomial) (u : ℕ) :
    (rawCarrier X Y q).val.Evalb ![u] ↔
      RawData (fun x => X.val.Evalb ![x]) (fun y => Y.val.Evalb ![y]) q u := by
  induction q generalizing u with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => simp [rawCarrier, RawData]
  | product p q ip iq => simp [rawCarrier_product_eval, RawData, ip, iq]
  | sum p q ip iq => simp [rawCarrier_sum_eval, RawData, ip, iq]

/-- The existing all-model size theorem refines every recursive leaf,
without changing any coefficient label or sum tag. -/
theorem refine_children {X Y : ℕ → Prop} (q : RawPolynomial) (n u : ℕ)
    (h : RawData X Y q u) (hs : ChildSize q n u) :
    RawData (fun x => X x ∧ len x < n) (fun y => Y y ∧ len y < n) q u := by
  induction q generalizing u with
  | term => exact ⟨h, hs⟩
  | formula => exact ⟨h, hs⟩
  | coefficient C => exact h
  | unit => exact h
  | product p q ip iq =>
      obtain ⟨x, y, rfl, hx, hy⟩ := h
      have hb : ChildSize p n x ∧ ChildSize q n y := by simpa [ChildSize] using hs
      exact ⟨x, y, rfl, ip x hx hb.1, iq y hy hb.2⟩
  | sum p q ip iq =>
      rcases h with ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · exact Or.inl ⟨x, rfl, ip x hx (by simpa [ChildSize] using hs)⟩
      · exact Or.inr ⟨y, rfl, iq y hy (by simpa [ChildSize] using hs)⟩

theorem childTuple_decomposition {X Y : ℕ → Prop} (n payload : ℕ)
    (h : RawData X Y (SyntaxPolynomial.power .term n) payload) :
    ∃ f : Fin n → ℕ, payload = childTuple n f ∧ ∀ i, X (f i) := by
  induction n generalizing payload with
  | zero => exact ⟨Fin.elim0, h, fun i => i.elim0⟩
  | succ n ih =>
      cases n with
      | zero => exact ⟨fun _ => payload, rfl, fun _ => h⟩
      | succ n =>
          obtain ⟨front, last, hp, hf, hl⟩ := h
          obtain ⟨f, hfront, hall⟩ := ih front hf
          refine ⟨Fin.lastCases last f, ?_, ?_⟩
          · simpa only [childTuple, Fin.lastCases_castSucc, Fin.lastCases_last,
              ← hfront] using hp
          · intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simpa only [Fin.lastCases_last] using (show X last from hl)
            · simpa only [Fin.lastCases_castSucc] using hall j

theorem arityInput_decomposition {X Y : ℕ → Prop} (σ : ℕ → Carrier) (d payload : ℕ)
    (h : RawData X Y (SyntaxPolynomial.constructors σ d) payload) :
    ∃ (k : Fin (d + 1)) (s : Symbols σ k.val) (children : Fin k.val → ℕ),
      payload = arityInput d k (Arithmetic.pair s.val (childTuple k.val children)) ∧
      ∀ i, X (children i) := by
  induction d generalizing payload with
  | zero =>
      obtain ⟨c, args, hp, hc, ha⟩ := h
      obtain ⟨children, he, hall⟩ := childTuple_decomposition 0 args ha
      refine ⟨0, ⟨c, hc⟩, children, ?_, hall⟩
      simpa only [arityInput, Fin.val_zero, ← he] using hp
  | succ d ih =>
      rcases h with ⟨front, hp, hf⟩ | ⟨last, hp, hl⟩
      · obtain ⟨k, s, children, he, hall⟩ := ih front hf
        refine ⟨k.castSucc, s, children, ?_, hall⟩
        simpa only [arityInput, Fin.lastCases_castSucc, Fin.val_castSucc, ← he] using hp
      · obtain ⟨c, args, hr, hc, ha⟩ := hl
        obtain ⟨children, he, hall⟩ := childTuple_decomposition (d + 1) args ha
        refine ⟨Fin.last (d + 1), ⟨c, hc⟩, children, ?_, hall⟩
        simp only [arityInput, Fin.lastCases_last, Fin.val_last]
        rw [← he, ← hr]
        exact hp

theorem childTuple_injective (n : ℕ) (f g : Fin n → ℕ)
    (h : childTuple n f = childTuple n g) : f = g := by
  induction n with
  | zero =>
      funext i
      exact i.elim0
  | succ n ih =>
      cases n with
      | zero =>
          funext i
          have hi : i = 0 := Fin.eq_zero i
          subst i
          exact h
      | succ n =>
          have hp : childTuple (n + 1) (fun i => f i.castSucc) =
              childTuple (n + 1) (fun i => g i.castSucc) ∧
              f (Fin.last (n + 1)) = g (Fin.last (n + 1)) :=
            (pair_eq_pair_iff _ _ _ _).mp h
          have hf := ih _ _ hp.1
          funext i
          exact Fin.lastCases hp.2 (fun j => congrFun hf j) i

/-- The arity tag is part of the code; neither a branch nor an ordered
payload is identified by this numerical coproduct encoding. -/
theorem arityInput_injective (d : ℕ) (i j : Fin (d + 1)) (u v : ℕ)
    (h : arityInput d i u = arityInput d j v) : i = j ∧ u = v := by
  induction d with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      have hj : j = 0 := Fin.eq_zero j
      subst i
      subst j
      exact ⟨rfl, h⟩
  | succ d ih =>
      revert h
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h
          have hv : u = v := by
            simpa only [arityInput, Fin.lastCases_last, pair_eq_pair_iff, and_true] using h
          exact ⟨rfl, hv⟩
        · intro h
          simp only [arityInput, Fin.lastCases_last, Fin.lastCases_castSucc,
            pair_eq_pair_iff, _root_.one_ne_zero, and_false] at h
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro h
          simp only [arityInput, Fin.lastCases_last, Fin.lastCases_castSucc,
            pair_eq_pair_iff, _root_.zero_ne_one, and_false] at h
        · intro h
          have hp : arityInput d i u = arityInput d j v := by
            simpa only [arityInput, Fin.lastCases_castSucc, pair_eq_pair_iff, and_true] using h
          obtain ⟨hij, huv⟩ := ih i j hp
          exact ⟨congrArg Fin.castSucc hij, huv⟩

theorem formulaData_cases {X Y : ℕ → Prop} (π : ℕ → Carrier) (d u : ℕ)
    (h : RawData X Y (formulaPolynomial π d) u) :
    (∃ r t, u = equalInput r t ∧ X r ∧ X t) ∨
    (∃ (k : Fin (d + 1)) (s : Symbols π k.val) (children : Fin k.val → ℕ),
      u = relationInput d k s.val children ∧ ∀ i, X (children i)) ∨
    (∃ body, u = negInput body ∧ Y body) ∨
    (∃ left right, u = impInput left right ∧ Y left ∧ Y right) ∨
    (∃ name body, u = allInput name body ∧ Y body) := by
  rcases h with ⟨v₃, h₃, rest₃⟩ | ⟨args, h₃, rest⟩
  · rcases rest₃ with ⟨v₂, h₂, rest₂⟩ | ⟨args, h₂, rest⟩
    · rcases rest₂ with ⟨v₁, h₁, rest₁⟩ | ⟨body, h₁, hb⟩
      · rcases rest₁ with ⟨args, h₀, rest⟩ | ⟨args, h₀, rest⟩
        · obtain ⟨r, t, ha, hr, ht⟩ := rest
          refine Or.inl ⟨r, t, ?_, hr, ht⟩
          simp only [equalInput, h₃, h₂, h₁, h₀, ha]
        · obtain ⟨k, s, children, ha, hc⟩ := arityInput_decomposition π d args rest
          refine Or.inr (Or.inl ⟨k, s, children, ?_, hc⟩)
          simp only [relationInput, h₃, h₂, h₁, h₀, ha]
      · refine Or.inr (Or.inr (Or.inl ⟨body, ?_, hb⟩))
        simp only [negInput, h₃, h₂, h₁]
    · obtain ⟨left, right, ha, hl, hr⟩ := rest
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨left, right, ?_, hl, hr⟩)))
      simp only [impInput, h₃, h₂, ha]
  · obtain ⟨name, body, ha, _, hb⟩ := rest
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨name, body, ?_, hb⟩)))
    simp only [allInput, h₃, ha]

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
