/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERFiniteLimits

/-!
# Finite coproducts of numerical PERs

A coproduct uses natural-number pairs with first coordinate zero or one to
identify the summand. The second coordinates are compared in that summand's
PER. Recursive injections and case distinction give the coproduct universal
property. The empty PER is an initial object.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def coproduct (R S : NumericalPER) : NumericalPER where
  rel n m := ((Nat.unpair n).1 = 0 ∧ (Nat.unpair m).1 = 0 ∧
      R.rel (Nat.unpair n).2 (Nat.unpair m).2) ∨
    ((Nat.unpair n).1 = 1 ∧ (Nat.unpair m).1 = 1 ∧
      S.rel (Nat.unpair n).2 (Nat.unpair m).2)
  symm := by
    rintro n m (⟨hn, hm, h⟩ | ⟨hn, hm, h⟩)
    · exact Or.inl ⟨hm, hn, R.symm h⟩
    · exact Or.inr ⟨hm, hn, S.symm h⟩
  trans := by
    rintro n m k (⟨hn, hm, h⟩ | ⟨hn, hm, h⟩) (⟨hm', hk, h'⟩ | ⟨hm', hk, h'⟩)
    · exact Or.inl ⟨hn, hk, R.trans h h'⟩
    · omega
    · omega
    · exact Or.inr ⟨hn, hk, S.trans h h'⟩

@[simp] theorem coproduct_rel_inl (R S : NumericalPER) (n m : ℕ) :
    (coproduct R S).rel (Nat.pair 0 n) (Nat.pair 0 m) ↔ R.rel n m := by
  simp [coproduct]

@[simp] theorem coproduct_rel_inr (R S : NumericalPER) (n m : ℕ) :
    (coproduct R S).rel (Nat.pair 1 n) (Nat.pair 1 m) ↔ S.rel n m := by
  simp [coproduct]

@[simp] theorem coproduct_rel_inl_inr (R S : NumericalPER) (n m : ℕ) :
    ¬ (coproduct R S).rel (Nat.pair 0 n) (Nat.pair 1 m) := by
  simp [coproduct]

def inlRepresentative (R S : NumericalPER) : Representative R (coproduct R S) where
  val n := Part.some (Nat.pair 0 n)
  computable := (Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact (coproduct_rel_inl R S n m).mpr h

def inrRepresentative (R S : NumericalPER) : Representative S (coproduct R S) where
  val n := Part.some (Nat.pair 1 n)
  computable := (Primrec₂.natPair.to_comp.comp (Computable.const 1) Computable.id).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact (coproduct_rel_inr R S n m).mpr h

def inl (R S : NumericalPER) : R ⟶ coproduct R S := ofRepresentative (inlRepresentative R S)
def inr (R S : NumericalPER) : S ⟶ coproduct R S := ofRepresentative (inrRepresentative R S)

instance inl_mono (R S : NumericalPER) : Mono (inl R S) where
  right_cancellation f g he := by
    revert he
    induction f using Quotient.inductionOn with | _ f =>
      induction g using Quotient.inductionOn with | _ g =>
        intro he
        apply Quotient.sound
        intro n hn a ha b hb
        apply (coproduct_rel_inl R S a b).mp
        exact (ofRepresentative_eq_iff _ _).mp he n hn (Nat.pair 0 a)
          (Part.mem_bind ha (Part.mem_some _)) (Nat.pair 0 b)
          (Part.mem_bind hb (Part.mem_some _))

instance inr_mono (R S : NumericalPER) : Mono (inr R S) where
  right_cancellation f g he := by
    revert he
    induction f using Quotient.inductionOn with | _ f =>
      induction g using Quotient.inductionOn with | _ g =>
        intro he
        apply Quotient.sound
        intro n hn a ha b hb
        apply (coproduct_rel_inr R S a b).mp
        exact (ofRepresentative_eq_iff _ _).mp he n hn (Nat.pair 1 a)
          (Part.mem_bind ha (Part.mem_some _)) (Nat.pair 1 b)
          (Part.mem_bind hb (Part.mem_some _))

def copairRepresentative {R S T : NumericalPER} (f : Representative R T)
    (g : Representative S T) : Representative (coproduct R S) T where
  val n := if (Nat.unpair n).1 = 0 then f.val (Nat.unpair n).2 else g.val (Nat.unpair n).2
  computable := by
    simpa only [Bool.cond_decide] using Partrec.cond
      (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0)).to_comp
      (f.computable.comp (Computable.snd.comp Computable.unpair))
      (g.computable.comp (Computable.snd.comp Computable.unpair))
  total := by
    rintro n (⟨hn, _, h⟩ | ⟨hn, _, h⟩)
    · simpa only [hn, ite_true] using f.total _ h
    · simpa only [hn, Nat.one_ne_zero, ite_false] using g.total _ h
  respects := by
    rintro n m a b (⟨hn, hm, h⟩ | ⟨hn, hm, h⟩) ha hb
    · simp only [hn, hm, ite_true] at ha hb
      exact f.respects h ha hb
    · simp only [hn, hm, Nat.one_ne_zero, ite_false] at ha hb
      exact g.respects h ha hb

@[simp] theorem copairRepresentative_inl {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (n : ℕ) :
    (copairRepresentative f g).val (Nat.pair 0 n) = f.val n := by
  simp [copairRepresentative]

@[simp] theorem copairRepresentative_inr {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (n : ℕ) :
    (copairRepresentative f g).val (Nat.pair 1 n) = g.val n := by
  simp [copairRepresentative]

theorem copairRepresentative_equiv {R S T : NumericalPER}
    {f f' : Representative R T} {g g' : Representative S T}
    (hf : Representative.Equiv f f') (hg : Representative.Equiv g g') :
    Representative.Equiv (copairRepresentative f g) (copairRepresentative f' g') := by
  rintro n (⟨hn, _, h⟩ | ⟨hn, _, h⟩) a ha b hb
  · simp only [copairRepresentative, hn, ite_true] at ha hb
    exact hf _ h a ha b hb
  · simp only [copairRepresentative, hn, Nat.one_ne_zero, ite_false] at ha hb
    exact hg _ h a ha b hb

def copair {R S T : NumericalPER} (f : R ⟶ T) (g : S ⟶ T) : coproduct R S ⟶ T :=
  Quotient.liftOn₂ f g (fun f g ↦ ofRepresentative (copairRepresentative f g))
    (fun _ _ _ _ hf hg ↦ Quotient.sound (copairRepresentative_equiv hf hg))

@[simp] theorem inl_copair {R S T : NumericalPER} (f : R ⟶ T) (g : S ⟶ T) :
    inl R S ≫ copair f g = f := by
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      apply Quotient.sound
      apply Representative.equiv_of_val_eq
      funext n
      simp [Representative.compose, inlRepresentative, copairRepresentative]

@[simp] theorem inr_copair {R S T : NumericalPER} (f : R ⟶ T) (g : S ⟶ T) :
    inr R S ≫ copair f g = g := by
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      apply Quotient.sound
      apply Representative.equiv_of_val_eq
      funext n
      simp [Representative.compose, inrRepresentative, copairRepresentative]

theorem coproduct_hom_ext {R S T : NumericalPER} {f g : coproduct R S ⟶ T}
    (hl : inl R S ≫ f = inl R S ≫ g) (hr : inr R S ≫ f = inr R S ≫ g) : f = g := by
  revert hl hr
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      intro hl hr
      apply Quotient.sound
      rintro n (⟨hn, _, h⟩ | ⟨hn, _, h⟩) a ha b hb
      · have he : Nat.pair 0 (Nat.unpair n).2 = n := by
          rw [← hn]; exact Nat.pair_unpair n
        apply (ofRepresentative_eq_iff _ _).mp hl (Nat.unpair n).2 h a _ b _
        · simpa [Representative.compose, inlRepresentative, he] using ha
        · simpa [Representative.compose, inlRepresentative, he] using hb
      · have he : Nat.pair 1 (Nat.unpair n).2 = n := by
          rw [← hn]; exact Nat.pair_unpair n
        apply (ofRepresentative_eq_iff _ _).mp hr (Nat.unpair n).2 h a _ b _
        · simpa [Representative.compose, inrRepresentative, he] using ha
        · simpa [Representative.compose, inrRepresentative, he] using hb

def coproductIsColimit (R S : NumericalPER) :
    IsColimit (BinaryCofan.mk (inl R S) (inr R S)) :=
  BinaryCofan.isColimitMk (fun s ↦ copair s.inl s.inr)
    (fun _ ↦ inl_copair _ _) (fun _ ↦ inr_copair _ _)
    (fun s _ hl hr ↦ coproduct_hom_ext (hl.trans (inl_copair s.inl s.inr).symm)
      (hr.trans (inr_copair s.inl s.inr).symm))

instance coproductHasColimit (R S : NumericalPER) : HasColimit (Limits.pair R S) :=
  ⟨⟨_, coproductIsColimit R S⟩⟩

instance perHasBinaryCoproducts : HasBinaryCoproducts NumericalPER :=
  hasBinaryCoproducts_of_hasColimit_pair NumericalPER

def emptyPER : NumericalPER where
  rel _ _ := False
  symm := False.elim
  trans := False.elim

def emptyRepresentative (R : NumericalPER) : Representative emptyPER R where
  val _ := Part.none
  computable := Partrec.none
  total := fun _ h ↦ False.elim h
  respects := fun h ↦ False.elim h

def emptyIsInitial : IsInitial emptyPER :=
  IsInitial.ofUniqueHom (fun R ↦ ofRepresentative (emptyRepresentative R)) (by
    intro R f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      exact fun _ h ↦ False.elim h)

instance perHasInitial : HasInitial NumericalPER := emptyIsInitial.hasInitial

instance perHasFiniteCoproducts : HasFiniteCoproducts NumericalPER :=
  hasFiniteCoproducts_of_has_binary_and_initial

end NumericalPER
end CategoricalEssentialIncompleteness
