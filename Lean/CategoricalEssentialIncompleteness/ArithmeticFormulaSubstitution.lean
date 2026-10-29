/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Joint computability of numeral substitution

The arithmetized substitution function agrees with Foundation's syntax
encoding. Its Σ₁ definition gives computability on codes, and decoding gives
computability of substitution jointly in the formula and the numeral.
-/

set_option autoImplicit false
noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

namespace CategoricalEssentialIncompleteness

/-- Arithmetized numeral substitution agrees with the formula encoding. -/
theorem numeralSubstitutionCode_encode (φ : ArithmeticSemisentence 1) (n : ℕ) :
    substNumeral (V := ℕ) (Encodable.encode φ) n =
      Encodable.encode (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  have h := substNumerals_app_quote (V := ℕ) φ (fun _ : Fin 1 => n)
  simpa [substNumerals, substNumeral, Matrix.fun_eq_vec_one,
    Sentence.quote_eq_encode_nat] using h

/-- The numerical substitution function is computable in both arguments. -/
theorem computable_numeralSubstitutionCode :
    Computable₂ (substNumeral (V := ℕ)) :=
  computable₂_iff_sigma1.mpr (inferInstance : 𝚺₁-Function₂ (substNumeral (V := ℕ)))

/-- Substitution is computable when both the one-place formula and numeral vary. -/
theorem computable_numeralSubstitution :
    Computable₂ (fun (φ : ArithmeticSemisentence 1) (n : ℕ) =>
      (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) := by
  have hCode : Computable fun p : ArithmeticSemisentence 1 × ℕ =>
      substNumeral (V := ℕ) (Encodable.encode p.1) p.2 :=
    computable_numeralSubstitutionCode.comp
      (Computable.encode.comp Computable.fst) Computable.snd
  have hDecode :=
    Computable.ofOption ((Computable.decode (α := ArithmeticSentence)).comp hCode)
  exact Computable₂.mk <| hDecode.of_eq_tot fun p => by
    simp [numeralSubstitutionCode_encode]

end CategoricalEssentialIncompleteness
