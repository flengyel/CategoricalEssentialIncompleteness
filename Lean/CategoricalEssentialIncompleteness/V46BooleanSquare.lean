/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.TwoBoolean

/-! # The four-summand presentation of the Boolean square -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.BooleanSquare
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

abbrev Four : D := (Two D) ⨿ (Two D)

def point (a b : Bool) : ⊤_ D ⟶ Four :=
  Two.point b ≫ if a then coprod.inr else coprod.inl

def pairPoint (a b : Bool) : ⊤_ D ⟶ (Two D) ⨯ (Two D) :=
  prod.lift (Two.point a) (Two.point b)

def encode : Four (D := D) ⟶ (Two D) ⨯ (Two D) :=
  coprod.desc (coprod.desc (pairPoint false false) (pairPoint false true))
    (coprod.desc (pairPoint true false) (pairPoint true true))

def decode : (Two D) ⨯ (Two D) ⟶ Four :=
  Two.branch prod.fst
    (Two.branch prod.snd (terminal.from _ ≫ point false false)
      (terminal.from _ ≫ point false true))
    (Two.branch prod.snd (terminal.from _ ≫ point true false)
      (terminal.from _ ≫ point true true))

@[reassoc] theorem point_encode (a b : Bool) :
    point (D := D) a b ≫ encode = pairPoint a b := by
  cases a <;> cases b <;> simp [point, encode, Two.point]

theorem constantPair_decode (X : D) (a b : Bool) :
    prod.lift (Two.constant X a) (Two.constant X b) ≫ decode =
      terminal.from X ≫ point a b := by
  rw [decode, Two.comp_branch _ _ _ _ a (by simp)]
  cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    rw [Two.comp_branch _ _ _ _ b (by simp)] <;> cases b <;> simp

@[reassoc] theorem pairPoint_decode (a b : Bool) :
    pairPoint (D := D) a b ≫ decode = point a b := by
  have ht : terminal.from (⊤_ D) = 𝟙 (⊤_ D) := terminal.hom_ext _ _
  simpa only [Two.constant, ht, Category.id_comp, pairPoint] using
    constantPair_decode (⊤_ D) a b

theorem encode_decode : encode (D := D) ≫ decode = 𝟙 _ := by
  have hp (a b : Bool) : point (D := D) a b ≫ (encode ≫ decode) = point a b := by
    rw [← Category.assoc, point_encode, pairPoint_decode]
  apply coprod.hom_ext
  · apply coprod.hom_ext
    · simpa [point, Two.point, Category.assoc] using hp false false
    · simpa [point, Two.point, Category.assoc] using hp false true
  · apply coprod.hom_ext
    · simpa [point, Two.point, Category.assoc] using hp true false
    · simpa [point, Two.point, Category.assoc] using hp true true

theorem decode_encode : decode (D := D) ≫ encode = 𝟙 _ := by
  have h := Two.check₂
    (fun X p q => prod.lift p q ≫ decode ≫ encode)
    (fun X p q => prod.lift p q)
    (by
      intro X Y k p q
      simpa only [Category.assoc] using
        congrArg (fun h => h ≫ decode ≫ encode) (prod.comp_lift k p q))
    (by intro X Y k p q; exact prod.comp_lift k p q)
    (by
      intro X a b
      rw [← Category.assoc, constantPair_decode, Category.assoc, point_encode]
      simp [pairPoint, Two.constant, prod.comp_lift])
    ((Two D) ⨯ (Two D)) prod.fst prod.snd
  simpa using h

/-- The product `2 × 2` is the coproduct of four terminal objects,
with the canonical four pairs as the comparison components. -/
def iso : Four (D := D) ≅ (Two D) ⨯ (Two D) where
  hom := encode
  inv := decode
  hom_inv_id := encode_decode
  inv_hom_id := decode_encode

end CategoricalEssentialIncompleteness.V46.BooleanSquare
