/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageDecoding


/-! # Inverse named decoding of every formula point -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d
example : Fm ≃ Total.underlying.obj (S).algebra.a.2 := NamedProofImage.formulaEquiv P σ π d
example (φ : Total.underlying.obj (S).algebra.a.2) :
    NamedPostfixEncoding.formulaCode (NamedProofImage.decodeFormula P σ π d φ)=φ.val :=
  NamedProofImage.decodeFormula_code P σ π d φ
example (z : Total.underlying.obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    NamedProofImage.decodeFormula P σ π d (Total.underlying.map (S).implicationConstructor z)=
      .imp (NamedProofImage.decodeFormula P σ π d (Total.underlying.map prod.fst z))
        (NamedProofImage.decodeFormula P σ π d (Total.underlying.map prod.snd z)) :=
  NamedProofImage.decode_implication P σ π d z

local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
example : Tm ≃ Total.underlying.obj (S).algebra.a.1 := NamedProofImage.termEquiv P σ π d
example (t : Total.underlying.obj (S).algebra.a.1) :
    NamedPostfixEncoding.termCode (NamedProofImage.decodeTerm P σ π d t) = t.val :=
  NamedProofImage.decodeTerm_code P σ π d t
example (z : Total.underlying.obj
    ((Syntax.predicateFunctor P).obj (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) ⨯
      (S).algebra.a.2)) :
    NamedProofImage.decodeFormula P σ π d (Total.underlying.map (S).quantifierConstructor z) =
      .all (Total.underlying.map prod.fst z).val
        (NamedProofImage.decodeFormula P σ π d (Total.underlying.map prod.snd z)) :=
  NamedProofImage.decode_quantifier P σ π d z
example (φ : Total.underlying.obj (S).algebra.a.2) :
    NamedProofImage.decodeFormula P σ π d (Total.underlying.map (S).negationConstructor φ) =
      .neg (NamedProofImage.decodeFormula P σ π d φ) :=
  NamedProofImage.decode_negation P σ π d φ
