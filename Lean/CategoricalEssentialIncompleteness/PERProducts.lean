/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalPER
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Binary products of numerical PERs

Pairs are encoded with Mathlib's recursive pairing function on ℕ. The product
relation compares the two decoded coordinates. Recursive projection and pairing
functions establish the product universal property for every PER source.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def product (R S : NumericalPER) : NumericalPER where
  rel n m := R.rel (Nat.unpair n).1 (Nat.unpair m).1 ∧
    S.rel (Nat.unpair n).2 (Nat.unpair m).2
  symm := fun h ↦ ⟨R.symm h.1, S.symm h.2⟩
  trans := fun h k ↦ ⟨R.trans h.1 k.1, S.trans h.2 k.2⟩

def fstRepresentative (R S : NumericalPER) : Representative (product R S) R where
  val n := Part.some (Nat.unpair n).1
  computable := (Computable.fst.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h.1

def sndRepresentative (R S : NumericalPER) : Representative (product R S) S where
  val n := Part.some (Nat.unpair n).2
  computable := (Computable.snd.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h.2

def fst (R S : NumericalPER) : product R S ⟶ R := ofRepresentative (fstRepresentative R S)
def snd (R S : NumericalPER) : product R S ⟶ S := ofRepresentative (sndRepresentative R S)

def pairRepresentative {T R S : NumericalPER} (f : Representative T R) (g : Representative T S) :
    Representative T (product R S) where
  val n := (f.val n).bind fun a ↦ (g.val n).map (Nat.pair a)
  computable := f.computable.bind
    ((g.computable.comp Computable.fst).map
      (Primrec₂.natPair.to_comp.comp
        (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂
  total := by
    intro n hn
    exact Part.bind_defined (f.total n hn) (g.total n hn)
  respects := by
    intro n m a b h ha hb
    obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
    obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).mp ha
    obtain ⟨x', hx', hb⟩ := Part.mem_bind_iff.mp hb
    obtain ⟨y', hy', rfl⟩ := (Part.mem_map_iff _).mp hb
    exact ⟨by simpa using f.respects h hx hx', by simpa using g.respects h hy hy'⟩

@[simp] theorem mem_pairRepresentative {T R S : NumericalPER}
    (f : Representative T R) (g : Representative T S) (n k : ℕ) :
    k ∈ (pairRepresentative f g).val n ↔
      ∃ a ∈ f.val n, ∃ b ∈ g.val n, Nat.pair a b = k := by
  simp [pairRepresentative, Part.mem_bind_iff, Part.mem_map_iff]

theorem pairRepresentative_equiv {T R S : NumericalPER}
    {f f' : Representative T R} {g g' : Representative T S}
    (hf : Representative.Equiv f f') (hg : Representative.Equiv g g') :
    Representative.Equiv (pairRepresentative f g) (pairRepresentative f' g') := by
  intro n hn a ha b hb
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairRepresentative _ _ _ _).mp ha
  obtain ⟨x', hx', y', hy', rfl⟩ := (mem_pairRepresentative _ _ _ _).mp hb
  exact ⟨by simpa using hf n hn x hx x' hx', by simpa using hg n hn y hy y' hy'⟩

def pair {T R S : NumericalPER} (f : T ⟶ R) (g : T ⟶ S) : T ⟶ product R S :=
  Quotient.liftOn₂ f g (fun f g ↦ ofRepresentative (pairRepresentative f g))
    (fun _ _ _ _ hf hg ↦ Quotient.sound (pairRepresentative_equiv hf hg))

@[simp] theorem pair_fst {T R S : NumericalPER} (f : T ⟶ R) (g : T ⟶ S) :
    pair f g ≫ fst R S = f := by
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      apply Quotient.sound
      intro n hn a ha b hb
      obtain ⟨p, hp, ha⟩ := Part.mem_bind_iff.mp ha
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairRepresentative _ _ _ _).mp hp
      have hax : a = x := by simpa [fstRepresentative] using ha
      subst a
      exact f.respects hn hx hb

@[simp] theorem pair_snd {T R S : NumericalPER} (f : T ⟶ R) (g : T ⟶ S) :
    pair f g ≫ snd R S = g := by
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      apply Quotient.sound
      intro n hn a ha b hb
      obtain ⟨p, hp, ha⟩ := Part.mem_bind_iff.mp ha
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairRepresentative _ _ _ _).mp hp
      have hay : a = y := by simpa [sndRepresentative] using ha
      subst a
      exact g.respects hn hy hb

theorem product_hom_ext {T R S : NumericalPER} {f g : T ⟶ product R S}
    (hfst : f ≫ fst R S = g ≫ fst R S)
    (hsnd : f ≫ snd R S = g ≫ snd R S) : f = g := by
  revert hfst hsnd
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      intro hfst hsnd
      have hf := (ofRepresentative_eq_iff _ _).mp hfst
      have hg := (ofRepresentative_eq_iff _ _).mp hsnd
      apply Quotient.sound
      intro n hn a ha b hb
      exact ⟨hf n hn _ (Part.mem_bind ha (Part.mem_some _))
          _ (Part.mem_bind hb (Part.mem_some _)),
        hg n hn _ (Part.mem_bind ha (Part.mem_some _))
          _ (Part.mem_bind hb (Part.mem_some _))⟩

def productIsLimit (R S : NumericalPER) :
    IsLimit (BinaryFan.mk (fst R S) (snd R S)) :=
  BinaryFan.isLimitMk (fun s ↦ pair s.fst s.snd)
    (fun _ ↦ pair_fst _ _) (fun _ ↦ pair_snd _ _)
    (fun s _ hm₁ hm₂ ↦ product_hom_ext (hm₁.trans (pair_fst s.fst s.snd).symm)
      (hm₂.trans (pair_snd s.fst s.snd).symm))

instance productHasLimit (R S : NumericalPER) : HasLimit (Limits.pair R S) :=
  ⟨⟨_, productIsLimit R S⟩⟩

instance perHasBinaryProducts : HasBinaryProducts NumericalPER :=
  hasBinaryProducts_of_hasLimit_pair NumericalPER


/-- The identity program represents every inclusion of PER relations. -/
def relationRepresentative {R S : NumericalPER} (h : ∀ n m, R.rel n m → S.rel n m) :
    Representative R S where
  val := Part.some
  computable := Partrec.some
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b hn ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h _ _ hn

/-- Equivalent relations give an isomorphism represented by the identity in both directions. -/
def relationIso (R S : NumericalPER) (h : ∀ n m, R.rel n m ↔ S.rel n m) : R ≅ S where
  hom := ofRepresentative (relationRepresentative (fun n m ↦ (h n m).mp))
  inv := ofRepresentative (relationRepresentative (fun n m ↦ (h n m).mpr))
  hom_inv_id := by
    apply Quotient.sound
    exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some n Part.some)
  inv_hom_id := by
    apply Quotient.sound
    exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some n Part.some)

end NumericalPER
end CategoricalEssentialIncompleteness
