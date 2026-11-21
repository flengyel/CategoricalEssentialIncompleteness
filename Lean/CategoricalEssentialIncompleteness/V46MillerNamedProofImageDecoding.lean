/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImagePoints

/-! # Inverse named decoding of every formula point

The bijections are the proved plain-word bijections followed by the uniform carrier
charts. Binder names and ordered children remain part of the literal word; no
binder-erasing translation is involved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => (Total.underlying (P := P))

def sourcePointEquiv (C : PredicateCategory 𝗣𝗔) :
    PredicateInterpretation.Obj ℕ C ≃ (U).obj ((F).obj C) where
  toFun := sourcePoint P C
  invFun q := ⟨q.val,(AxiomSubobjects.mapped_support P C q.val).mp q.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

def termEquiv : Tm ≃ (U).obj (S).algebra.a.1 :=
  (NamedPostfixPlainComparison.plainTermModelEquiv σ π d).trans
    ((sourcePointEquiv P (S₀).algebra.a.1).trans
      (((U).mapIso (NamedSyntaxComparison.termIso P (V) σ π d).symm).toEquiv))

def formulaEquiv : Fm ≃ (U).obj (S).algebra.a.2 :=
  (NamedPostfixPlainComparison.plainFormulaModelEquiv σ π d).trans
    ((sourcePointEquiv P (S₀).algebra.a.2).trans
      (((U).mapIso (NamedSyntaxComparison.formulaIso P (V) σ π d).symm).toEquiv))

@[simp] theorem termEquiv_apply (t : Tm) : termEquiv P σ π d t=termPoint P σ π d t := rfl
@[simp] theorem formulaEquiv_apply (φ : Fm) : formulaEquiv P σ π d φ=formulaPoint P σ π d φ := rfl

def decodeTerm : (U).obj (S).algebra.a.1 → Tm := (termEquiv P σ π d).symm
def decodeFormula : (U).obj (S).algebra.a.2 → Fm := (formulaEquiv P σ π d).symm

@[simp] theorem decode_termPoint (t : Tm) : decodeTerm P σ π d (termPoint P σ π d t)=t :=
  (termEquiv P σ π d).symm_apply_apply t
@[simp] theorem decode_formulaPoint (φ : Fm) : decodeFormula P σ π d (formulaPoint P σ π d φ)=φ :=
  (formulaEquiv P σ π d).symm_apply_apply φ
@[simp] theorem termPoint_decode (t : (U).obj (S).algebra.a.1) :
    termPoint P σ π d (decodeTerm P σ π d t)=t :=
  (termEquiv P σ π d).apply_symm_apply t
@[simp] theorem formulaPoint_decode (φ : (U).obj (S).algebra.a.2) :
    formulaPoint P σ π d (decodeFormula P σ π d φ)=φ :=
  (formulaEquiv P σ π d).apply_symm_apply φ

theorem termPoint_injective : Function.Injective (termPoint P σ π d) :=
  (termEquiv P σ π d).injective
theorem formulaPoint_injective : Function.Injective (formulaPoint P σ π d) :=
  (formulaEquiv P σ π d).injective

theorem decodeTerm_code (t : (U).obj (S).algebra.a.1) : termCode (decodeTerm P σ π d t)=t.val :=
  (termPoint_value P σ π d _).symm.trans (congrArg Subtype.val (termPoint_decode P σ π d t))
theorem decodeFormula_code (φ : (U).obj (S).algebra.a.2) : formulaCode (decodeFormula P σ π d φ)=φ.val :=
  (formulaPoint_value P σ π d _).symm.trans (congrArg Subtype.val (formulaPoint_decode P σ π d φ))

theorem pairPoint_eta {X Y : Total.TotalCategory P} (z : (U).obj (X ⨯ Y)) :
    Points.pairPoint ((U).map prod.fst z) ((U).map prod.snd z)=z :=
  Points.product_ext (Points.pairPoint_fst _ _) (Points.pairPoint_snd _ _)

theorem namePoint_eta (x : (U).obj ((F).obj (V))) : Points.namePoint P x.val=x := by
  apply Subtype.ext
  rfl

theorem decode_negation (φ : (U).obj (S).algebra.a.2) :
    decodeFormula P σ π d ((U).map (S).negationConstructor φ)=.neg (decodeFormula P σ π d φ) := by
  apply formulaPoint_injective P σ π d
  rw [formulaPoint_decode,← formulaPoint_negation,formulaPoint_decode]

theorem decode_implication (z : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    decodeFormula P σ π d ((U).map (S).implicationConstructor z)=
      .imp (decodeFormula P σ π d ((U).map prod.fst z))
        (decodeFormula P σ π d ((U).map prod.snd z)) := by
  apply formulaPoint_injective P σ π d
  rw [formulaPoint_decode,← Points.implication_point,
    formulaPoint_decode,formulaPoint_decode,pairPoint_eta]

theorem decode_equality (z : (U).obj ((S).algebra.a.1 ⨯ (S).algebra.a.1)) :
    decodeFormula P σ π d ((U).map (S).equalityConstructor z)=
      .equal (decodeTerm P σ π d ((U).map prod.fst z))
        (decodeTerm P σ π d ((U).map prod.snd z)) := by
  apply formulaPoint_injective P σ π d
  rw [formulaPoint_decode,← Points.equality_point,
    termPoint_decode,termPoint_decode,pairPoint_eta]

theorem decode_quantifier (z : (U).obj ((F).obj (V) ⨯ (S).algebra.a.2)) :
    decodeFormula P σ π d ((U).map (S).quantifierConstructor z)=
      .all ((U).map prod.fst z).val (decodeFormula P σ π d ((U).map prod.snd z)) := by
  apply formulaPoint_injective P σ π d
  rw [formulaPoint_decode,← Points.quantifier_point,
    namePoint_eta,formulaPoint_decode,pairPoint_eta]

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
