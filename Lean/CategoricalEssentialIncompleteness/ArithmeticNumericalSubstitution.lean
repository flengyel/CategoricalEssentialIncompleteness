/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ArithmeticSyntax
import CategoricalEssentialIncompleteness.ArithmeticFormulaSubstitution
import CategoricalEssentialIncompleteness.NumericalTotalProducts

/-!
# Numerical substitution of arithmetic formulas

The substitution function decodes a unary formula, substitutes a numeral, and
returns the index of the resulting sentence. Its numerical arrow is total.
Precomposing its first coordinate with a total numerical arrow gives the
two-variable substitution map used in the representation equations.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory Encodable FFL FFL.FirstOrder

namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

/-- The sentence index obtained by substituting a numeral into a decoded unary formula. -/
def substitutionFunction (a n : ℕ) : ℕ :=
  sentenceIndex ((unaryFormula a)/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)

theorem substitutionFunction_computable : Computable₂ substitutionFunction := by
  have h : Computable fun p : ℕ × ℕ =>
      ((unaryFormula p.1)/[(↑p.2 : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) :=
    computable_numeralSubstitution.comp
      (unaryFormula_computable.comp Computable.fst) Computable.snd
  exact (sentenceIndex_computable.comp h).to₂

@[simp] theorem sentenceEnumeration_substitutionFunction (a n : ℕ) :
    sentenceEnumeration (substitutionFunction a n) =
      ((unaryFormula a)/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) :=
  sentenceEnumeration_index _

@[simp] theorem substitutionFunction_encode (φ : ArithmeticSemisentence 1) (n : ℕ) :
    substitutionFunction (encode φ) n =
      sentenceIndex (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  simp only [substitutionFunction, unaryFormula_encode]

theorem substitutionFunction_of_invalid {a : ℕ}
    (ha : a ∉ Set.range (encode : ArithmeticSemisentence 1 → ℕ)) (n : ℕ) :
    substitutionFunction a n = sentenceIndex (⊥ : ArithmeticSentence) := by
  rw [substitutionFunction, unaryFormula_of_invalid ha]
  rfl

/-- The total numerical substitution arrow on coded pairs of natural numbers. -/
def substitutionArrow :
    Numerical.totalObject (Numerical.product Numerical.nat Numerical.nat) ⟶
      Numerical.totalObject Numerical.nat :=
  Numerical.totalFromFunction
    (fun z => substitutionFunction (Nat.unpair z).1 (Nat.unpair z).2)
    (substitutionFunction_computable.comp
      (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair))
    (fun _ _ => Set.mem_univ _)

@[simp] theorem substitutionArrow_val (z : ℕ) :
    substitutionArrow.hom.val z =
      Part.some (substitutionFunction (Nat.unpair z).1 (Nat.unpair z).2) := by
  change (supportIdentity (Numerical.product Numerical.nat Numerical.nat).carrier z).bind
    (fun k => Part.some (substitutionFunction (Nat.unpair k).1 (Nat.unpair k).2)) = _
  have hz : z ∈ (Numerical.product Numerical.nat Numerical.nat).carrier :=
    ⟨Set.mem_univ _, Set.mem_univ _⟩
  rw [supportIdentity, Part.assert_pos hz, Part.bind_some]

@[simp] theorem substitutionArrow_pair_val (a n : ℕ) :
    substitutionArrow.hom.val (Nat.pair a n) = Part.some (substitutionFunction a n) := by
  simp only [substitutionArrow_val, Nat.unpair_pair]

/-- Precompose the first coordinate of substitution by a total numerical arrow. -/
def substitutionRow (g : Numerical.totalObject Numerical.nat ⟶
    Numerical.totalObject Numerical.nat) :
    Numerical.totalObject (Numerical.product Numerical.nat Numerical.nat) ⟶
      Numerical.totalObject Numerical.nat :=
  Numerical.totalPair
    (Numerical.fst (Numerical.totalObject Numerical.nat) (Numerical.totalObject Numerical.nat) ≫ g)
    (Numerical.snd (Numerical.totalObject Numerical.nat) (Numerical.totalObject Numerical.nat)) ≫
      substitutionArrow

theorem substitutionRow_val (g : Numerical.totalObject Numerical.nat ⟶
    Numerical.totalObject Numerical.nat) (z : ℕ) :
    (substitutionRow g).hom.val z =
      Part.some (substitutionFunction (Numerical.natFunction g (Nat.unpair z).1)
        (Nat.unpair z).2) := by
  have hz : z ∈ (Numerical.product Numerical.nat Numerical.nat).carrier :=
    ⟨Set.mem_univ _, Set.mem_univ _⟩
  have hf : ((Numerical.fst (Numerical.totalObject Numerical.nat)
      (Numerical.totalObject Numerical.nat) ≫ g).hom).val z =
        Part.some (Numerical.natFunction g (Nat.unpair z).1) := by
    change ((supportIdentity (Numerical.product Numerical.nat Numerical.nat).carrier z).bind
      (fun k => Part.some (Nat.unpair k).1)).bind g.hom.val = _
    rw [supportIdentity, Part.assert_pos hz, Part.bind_some, Part.bind_some]
    exact (Part.some_get _).symm
  have hs : (Numerical.snd (Numerical.totalObject Numerical.nat)
      (Numerical.totalObject Numerical.nat)).hom.val z = Part.some (Nat.unpair z).2 := by
    change (supportIdentity (Numerical.product Numerical.nat Numerical.nat).carrier z).bind
      (fun k => Part.some (Nat.unpair k).2) = _
    rw [supportIdentity, Part.assert_pos hz, Part.bind_some]
  change ((((Numerical.fst (Numerical.totalObject Numerical.nat)
      (Numerical.totalObject Numerical.nat) ≫ g).hom).val z).bind fun a =>
      ((Numerical.snd (Numerical.totalObject Numerical.nat)
        (Numerical.totalObject Numerical.nat)).hom.val z).map (Nat.pair a)).bind
        substitutionArrow.hom.val = _
  rw [hf, hs, Part.bind_some, Part.map_some, Part.bind_some, substitutionArrow_val]
  simp only [Nat.unpair_pair]

@[simp] theorem substitutionRow_pair_val (g : Numerical.totalObject Numerical.nat ⟶
    Numerical.totalObject Numerical.nat) (x n : ℕ) :
    (substitutionRow g).hom.val (Nat.pair x n) =
      Part.some (substitutionFunction (Numerical.natFunction g x) n) := by
  simpa only [Nat.unpair_pair] using substitutionRow_val g (Nat.pair x n)

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
