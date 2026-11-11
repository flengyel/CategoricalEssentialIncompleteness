/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSignatureRelabel
public import CategoricalEssentialIncompleteness.V46NumericalCoordinatesPresentation

/-! # The computable identity-on-word signature chart -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel
open NamedPostfixEncoding
variable {σ τ π ρ : ℕ → Carrier} {d : ℕ}
variable (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
  (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])

include h in
private theorem term_membership_forward (n : ℕ)
    (hn : (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![n]) :
    (Postfix.plainCarrier false (termPolynomial τ d) (formulaPolynomial ρ d)).val.Evalb ![n] := by
  obtain ⟨t,ht⟩ := (standard_codes_surjective σ π d).1 n
    ((Postfix.carrier_plain_model false _ _ n).mpr hn)
  have hm := (Postfix.carrier_plain_model false (termPolynomial τ d) (formulaPolynomial ρ d)
    (termCode (term h t))).mp (termCode_member ρ (term h t))
  simpa only [term_code,ht] using hm

include h j in
private theorem formula_membership_forward (n : ℕ)
    (hn : (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![n]) :
    (Postfix.plainCarrier true (termPolynomial τ d) (formulaPolynomial ρ d)).val.Evalb ![n] := by
  obtain ⟨φ,hφ⟩ := (standard_codes_surjective σ π d).2 n
    ((Postfix.carrier_plain_model true _ _ n).mpr hn)
  have hm := (Postfix.carrier_plain_model true (termPolynomial τ d) (formulaPolynomial ρ d)
    (formulaCode (formula h j φ))).mp (formulaCode_member (formula h j φ))
  simpa only [formula_code,hφ] using hm

include h in
theorem term_membership (n : ℕ) :
    (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![n] ↔
      (Postfix.plainCarrier false (termPolynomial τ d) (formulaPolynomial ρ d)).val.Evalb ![n] :=
  ⟨term_membership_forward h n,
    term_membership_forward (fun k m => (h k m).symm) n⟩

include h j in
theorem formula_membership (n : ℕ) :
    (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![n] ↔
      (Postfix.plainCarrier true (termPolynomial τ d) (formulaPolynomial ρ d)).val.Evalb ![n] :=
  ⟨formula_membership_forward h j n,
    formula_membership_forward (fun k m => (h k m).symm) (fun k m => (j k m).symm) n⟩

def wordObject (formula : Bool) (σ π : ℕ → Carrier) (d : ℕ) : NumericalTuples.Object :=
  NumericalCoordinates.predicateObject
    (Postfix.plainCarrier formula (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗧𝗔)

include h j in
theorem membership (b : Bool) (n : ℕ) :
    (Postfix.plainCarrier b (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![n] ↔
      (Postfix.plainCarrier b (termPolynomial τ d) (formulaPolynomial ρ d)).val.Evalb ![n] := by
  cases b
  · exact term_membership h n
  · exact formula_membership h j n

def predicateWordIso (C D : PredicateCategory 𝗧𝗔)
    (hm : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n]) :
    NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D where
  hom :=
    { toFun := fun x => ⟨x.val,(hm x.val).mp x.property⟩
      represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩ }
  inv :=
    { toFun := fun x => ⟨x.val,(hm x.val).mpr x.property⟩
      represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩ }
  hom_inv_id := NumericalTuples.Map.ext rfl
  inv_hom_id := NumericalTuples.Map.ext rfl

theorem predicateWordIso_hom_value (C D : PredicateCategory 𝗧𝗔)
    (hm : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n])
    (x : NumericalTuples.Point (NumericalCoordinates.predicateObject C)) :
    ((predicateWordIso C D hm).hom.toFun x).val = x.val := rfl

theorem predicateWordIso_inv_value (C D : PredicateCategory 𝗧𝗔)
    (hm : ∀ n : ℕ, C.val.Evalb ![n] ↔ D.val.Evalb ![n])
    (x : NumericalTuples.Point (NumericalCoordinates.predicateObject D)) :
    ((predicateWordIso C D hm).inv.toFun x).val = x.val := rfl

/-- Both directions are represented by the identity partial recursive
program. The original stored word and all binder names are preserved. -/
def wordIso (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
    (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])
    (b : Bool) : wordObject b σ π d ≅ wordObject b τ ρ d :=
  predicateWordIso
    (Postfix.plainCarrier b (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗧𝗔)
    (Postfix.plainCarrier b (termPolynomial τ d) (formulaPolynomial ρ d) : PredicateCategory 𝗧𝗔)
    (membership h j b)

abbrev wordIso_hom_value
    (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
    (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])
    (b : Bool) (x : NumericalTuples.Point (wordObject b σ π d)) :=
  predicateWordIso_hom_value
    (Postfix.plainCarrier b (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗧𝗔)
    (Postfix.plainCarrier b (termPolynomial τ d) (formulaPolynomial ρ d) : PredicateCategory 𝗧𝗔)
    (membership h j b) x

abbrev wordIso_inv_value
    (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
    (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])
    (b : Bool) (x : NumericalTuples.Point (wordObject b τ ρ d)) :=
  predicateWordIso_inv_value
    (Postfix.plainCarrier b (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗧𝗔)
    (Postfix.plainCarrier b (termPolynomial τ d) (formulaPolynomial ρ d) : PredicateCategory 𝗧𝗔)
    (membership h j b) x

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel
