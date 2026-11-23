/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46BooleanSquare
public import CategoricalEssentialIncompleteness.V46Inference
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Boolean vectors index the coproduct presentation of every finite power -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoricalEssentialIncompleteness.V46.BooleanPowers

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

/-- Insert the specified last truth value, retaining all preceding coordinates. -/
def append (X : D) (b : Bool) : X ⟶ X ⨯ Two D := prod.lift (𝟙 X) (Two.constant X b)

private theorem last_ext {X Y : D} {g h : X ⨯ Two D ⟶ Y}
    (H : ∀ b, append X b ≫ g = append X b ≫ h) : g = h := by
  have eqn (b : Bool) : Two.fiberι (prod.snd : X ⨯ Two D ⟶ _) b ≫ prod.fst ≫ append X b =
      Two.fiberι prod.snd b := by
    apply prod.hom_ext
    · simp [append]
    · simp [append]
  apply Two.hom_ext (prod.snd : X ⨯ Two D ⟶ _)
  all_goals
    apply (congrArg (fun k => k ≫ g) (eqn _)).symm.trans
    simpa only [Category.assoc, H] using congrArg (fun k => k ≫ h) (eqn _)

/-- The tuple of the `n` chosen coproduct injections. -/
def vertex : (n : ℕ) → (Fin n → Bool) → (⊤_ D ⟶ finitePower (Two D) n)
  | 0, _ => 𝟙 _
  | 1, a => Two.point (a 0)
  | n + 2, a => vertex (n+1) (Fin.init a) ≫ append _ (a (Fin.last (n+1)))

def descend {Y : D} : (n : ℕ) → ((Fin n → Bool) → (⊤_ D ⟶ Y)) →
    (finitePower (Two D) n ⟶ Y)
  | 0, f => f Fin.elim0
  | 1, f => coprod.desc (f (fun _ => false)) (f (fun _ => true))
  | n+2, f => Two.branch prod.snd
      (prod.fst ≫ descend (n+1) (fun a => f (Fin.snoc a false)))
      (prod.fst ≫ descend (n+1) (fun a => f (Fin.snoc a true)))

theorem appended_descend {Y : D} (n : ℕ) (f : (Fin (n+2) → Bool) → (⊤_ D ⟶ Y))
    (b : Bool) : append _ b ≫ descend (n+2) f = descend (n+1) (fun a => f (Fin.snoc a b)) := by
  rw [descend, Two.comp_branch _ _ _ _ b (by simp [append])]
  cases b <;> simp [append]

theorem vertex_descend {Y : D} : ∀ n (f : (Fin n → Bool) → (⊤_ D ⟶ Y)) a,
    vertex n a ≫ descend n f = f a
  | 0, f, a => by
    rw [vertex, descend, Category.id_comp]
    exact congrArg f (Subsingleton.elim _ _)
  | 1, f, a => by
    have eqn : (fun _ : Fin 1 => a 0) = a := funext fun i => congrArg a (Subsingleton.elim _ _)
    rw [← eqn]
    cases a 0 <;> simp [vertex, descend, Two.point, finitePower, Two]
  | n+2, f, a => by
    rw [vertex, Category.assoc, appended_descend, vertex_descend, Fin.snoc_init_self]

theorem vertex_hom_ext {Y : D} : ∀ n (g h : finitePower (Two D) n ⟶ Y),
    (∀ a, vertex n a ≫ g = vertex n a ≫ h) → g = h
  | 0, g, h, H => by simpa [vertex, finitePower] using H Fin.elim0
  | 1, g, h, H => by
    apply coprod.hom_ext
    · exact H (fun _ => false)
    · exact H (fun _ => true)
  | n+2, g, h, H => by
    apply last_ext
    intro b
    apply vertex_hom_ext (n+1)
    intro a
    simpa [vertex, Category.assoc] using H (Fin.snoc a b)

/-- The coproduct cocone indexed by ordered Boolean vectors has vertex `Two^n`. -/
def isColimit (n : ℕ) :
    IsColimit (Cofan.mk (finitePower (Two D) n) (vertex n)) := by
  refine Cofan.IsColimit.mk _ (fun s => descend n s.inj) ?_ ?_
  · intro s a
    exact vertex_descend n s.inj a
  · intro s g h
    apply vertex_hom_ext
    intro a
    exact (h a).trans (vertex_descend n s.inj a).symm

end CategoricalEssentialIncompleteness.V46.BooleanPowers
