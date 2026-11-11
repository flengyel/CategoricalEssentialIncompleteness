/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalCategory
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# The category of numerical partial equivalence relations

Objects are arbitrary symmetric transitive relations on ℕ. Representatives are partial
recursive functions defined on the source support and respecting the relations.
Arrows identify representing functions whose values are related at every supported input.
No enumerability condition is imposed on a relation or its support.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness

structure NumericalPER where
  rel : ℕ → ℕ → Prop
  symm : ∀ {n m}, rel n m → rel m n
  trans : ∀ {n m k}, rel n m → rel m k → rel n k

namespace NumericalPER

def support (R : NumericalPER) : Set ℕ := {n | R.rel n n}

theorem supported_left {R : NumericalPER} {n m : ℕ} (h : R.rel n m) :
    n ∈ R.support := R.trans h (R.symm h)

theorem supported_right {R : NumericalPER} {n m : ℕ} (h : R.rel n m) :
    m ∈ R.support := R.trans (R.symm h) h

structure Representative (R S : NumericalPER) where
  val : ℕ → Part ℕ
  computable : Partrec val
  total : ∀ n ∈ R.support, (val n).Dom
  respects : ∀ {n m a b}, R.rel n m → a ∈ val n → b ∈ val m → S.rel a b

namespace Representative
variable {R S T W : NumericalPER}

theorem output_supported (f : Representative R S) {n a : ℕ} (hn : n ∈ R.support)
    (ha : a ∈ f.val n) : a ∈ S.support := f.respects hn ha ha

def Equiv (f g : Representative R S) : Prop :=
  ∀ n ∈ R.support, ∀ a ∈ f.val n, ∀ b ∈ g.val n, S.rel a b

instance : Setoid (Representative R S) where
  r := Equiv
  iseqv :=
    { refl := fun f n hn _ ha _ hb ↦ f.respects hn ha hb
      symm := fun h n hn _ ha _ hb ↦ S.symm (h n hn _ hb _ ha)
      trans := by
        intro f g h hfg hgh n hn a ha c hc
        let b := (g.val n).get (g.total n hn)
        exact S.trans (hfg n hn a ha b (Part.get_mem _))
          (hgh n hn b (Part.get_mem _) c hc) }

theorem equiv_of_val_eq (f g : Representative R S) (h : f.val = g.val) : Equiv f g := by
  intro n hn a ha b hb
  rw [h] at ha
  exact g.respects hn ha hb

def identity (R : NumericalPER) : Representative R R where
  val := Part.some
  computable := Partrec.some
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    simpa using h

def compose (f : Representative R S) (g : Representative S T) : Representative R T where
  val n := (f.val n).bind g.val
  computable := f.computable.bind (g.computable.comp Computable.snd).to₂
  total := by
    intro n hn
    have hf := f.total n hn
    exact Part.bind_defined hf (g.total _ (f.output_supported hn (Part.get_mem hf)))
  respects := by
    intro n m a b h ha hb
    obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
    obtain ⟨y, hy, hb⟩ := Part.mem_bind_iff.mp hb
    exact g.respects (f.respects h hx hy) ha hb

theorem compose_equiv {f f' : Representative R S} {g g' : Representative S T}
    (hf : Equiv f f') (hg : Equiv g g') : Equiv (compose f g) (compose f' g') := by
  intro n hn a ha b hb
  obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
  obtain ⟨y, hy, hb⟩ := Part.mem_bind_iff.mp hb
  have hyS := f'.output_supported hn hy
  let z := (g.val y).get (g.total y hyS)
  exact T.trans (g.respects (hf n hn x hx y hy) ha (Part.get_mem _))
    (hg y hyS z (Part.get_mem _) b hb)

end Representative

def Hom (R S : NumericalPER) := Quotient (inferInstance : Setoid (Representative R S))

instance perCategory : Category NumericalPER where
  Hom := Hom
  id R := Quotient.mk _ (Representative.identity R)
  comp f g := Quotient.liftOn₂ f g
    (fun f g ↦ Quotient.mk _ (Representative.compose f g))
    (fun _ _ _ _ hf hg ↦ Quotient.sound (Representative.compose_equiv hf hg))
  id_comp := by
    intro R S f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some n f.val)
  comp_id := by
    intro R S f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some_right (f.val n))
  assoc := by
    intro R S T W f g h
    induction f using Quotient.inductionOn with | _ f =>
      induction g using Quotient.inductionOn with | _ g =>
        induction h using Quotient.inductionOn with | _ h =>
          apply Quotient.sound
          exact Representative.equiv_of_val_eq _ _
            (funext fun n ↦ Part.bind_assoc (f.val n) g.val h.val)

/-- The morphism determined by a representing partial recursive function. -/
def ofRepresentative {R S : NumericalPER} (f : Representative R S) : R ⟶ S := Quotient.mk _ f

theorem ofRepresentative_eq_iff {R S : NumericalPER} (f g : Representative R S) :
    ofRepresentative f = ofRepresentative g ↔ Representative.Equiv f g := Quotient.eq

@[simp] theorem ofRepresentative_comp {R S T : NumericalPER}
    (f : Representative R S) (g : Representative S T) :
    ofRepresentative f ≫ ofRepresentative g = ofRepresentative (Representative.compose f g) := rfl

/-- Equality restricted to an arbitrary support. -/
def discrete (A : Set ℕ) : NumericalPER where
  rel n m := n ∈ A ∧ n = m
  symm := by rintro n m ⟨hn, rfl⟩; exact ⟨hn, rfl⟩
  trans := by rintro n m k ⟨hn, rfl⟩ ⟨_, rfl⟩; exact ⟨hn, rfl⟩

@[simp] theorem discrete_support (A : Set ℕ) : (discrete A).support = A := by
  ext n; simp [support, discrete]

/-- Equality of arrows into a discrete PER is equality of their supported values. -/
theorem discrete_arrow_eq_iff {R : NumericalPER} {A : Set ℕ}
    (f g : Representative R (discrete A)) :
    ofRepresentative f = ofRepresentative g ↔ ∀ n ∈ R.support, f.val n = g.val n := by
  rw [ofRepresentative_eq_iff]
  constructor
  · intro h n hn
    apply Part.ext
    intro a
    constructor
    · intro ha
      have hb := Part.get_mem (g.total n hn)
      have heq := (h n hn a ha _ hb).2
      exact heq.symm ▸ hb
    · intro ha
      have hb := Part.get_mem (f.total n hn)
      have heq := (h n hn _ hb a ha).2
      exact heq ▸ hb
  · intro h n hn a ha b hb
    rw [h n hn] at ha
    exact ⟨g.output_supported hn ha |>.1, Part.mem_unique ha hb⟩

end NumericalPER
end CategoricalEssentialIncompleteness
