/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticLogicalOperations
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationRules

/-! # Actual arithmetic axiom labels and unary/binary rule-label comparisons -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Rules
open NamedArithmeticSignature Coordinates

/-- The given c.e. Gamma predicate is filtered by the already compared
PA sentence carrier. Its label is still the original sentence word. -/
def axiomObject (Γ : Carrier) : NumericalTuples.Object :=
  numericalInterpretation.obj (ArithmeticLiteralModel.axiomObject Γ)

def axioms (Γ : Carrier) : axiomObject Γ ⟶ numericalSyntax.sentenceObject :=
  numericalInterpretation.map (ArithmeticLiteralModel.axioms Γ) ≫ sentenceIso.inv

instance axioms_mono (Γ : Carrier) : Mono (axioms Γ) := by
  dsimp only [axioms]
  infer_instance

theorem axiom_membership (Γ : Carrier) (n : ℕ) :
    (axiomObject Γ).support n ↔ Γ.val.Evalb ![n] ∧ ArithmeticLiteralModel.sentencePredicate.val.Evalb ![n] :=
  SyntacticAxiomPredicates.axiomCarrier_literal 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ Γ n

/-- The actual nonlogical nullary conclusion square uses the same
Gamma axiom inclusion and the proved sentence and formula charts. -/
theorem axioms_formula (Γ : Carrier) :
    axioms Γ ≫ numericalSyntax.sentenceInclusion ≫ formulaIso.hom =
      numericalInterpretation.map (ArithmeticLiteralModel.axioms Γ ≫ originalSyntax.sentenceInclusion) := by
  have hi : sentenceIso.inv ≫ numericalSyntax.sentenceInclusion ≫ formulaIso.hom =
      numericalInterpretation.map originalSyntax.sentenceInclusion := by
    rw [← sentence_inclusion,Iso.inv_hom_id_assoc]
  rw [axioms,Category.assoc,hi,← CategoryTheory.Functor.map_comp]

theorem axioms_word (Γ : Carrier) (a : NumericalTuples.Point (axiomObject Γ)) :
    (formulaIso.hom.toFun (numericalSyntax.sentenceInclusion.toFun ((axioms Γ).toFun a))).val = a.val := by
  exact (congrArg (fun k => (k.toFun a).val) (axioms_formula Γ)).trans
    ((congrArg Subtype.val (numericalInterpretation_value
      (ArithmeticLiteralModel.axioms Γ ≫ originalSyntax.sentenceInclusion) a)).trans
        (SyntacticAxiomPredicates.axioms_formula_value 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ℕ Γ a))

def rules (Γ : Carrier) : RulePresentation numericalSyntax.algebra.a.2 2 :=
  numericalSyntax.logicalRules (axioms Γ)

def originalRules (Γ : Carrier) : RulePresentation originalSyntax.algebra.a.2 2 :=
  originalSyntax.logicalRules (ArithmeticLiteralModel.axioms Γ)

/-- The finite-product comparison is applied to the actual variable and
formula charts. Its inverse is a numerical morphism on the whole label carrier. -/
def rho1 (Γ : Carrier) : (rules Γ).instances 1 ≅
    numericalInterpretation.obj ((originalRules Γ).instances 1) :=
  SubstitutionParameters.pairedIso variableIso formulaIso

def rho2 (Γ : Carrier) : (rules Γ).instances 2 ≅
    numericalInterpretation.obj ((originalRules Γ).instances 2) :=
  SubstitutionParameters.pairedIso formulaIso formulaIso

/-- The named generalization label retains the name and its own premise. -/
@[reassoc] theorem rho1_name (Γ : Carrier) :
    (rho1 Γ).hom ≫ numericalInterpretation.map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols originalSyntax.algebra.a.2) variableSymbols) =
      prod.fst ≫ variableIso.hom := by
  exact SubstitutionParameters.pairedIso_fst variableIso formulaIso

@[reassoc] theorem rho1_premise (Γ : Carrier) :
    (rho1 Γ).hom ≫ numericalInterpretation.map
        (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) =
      prod.snd ≫ formulaIso.hom := by
  exact SubstitutionParameters.pairedIso_snd variableIso formulaIso

/-- The modus-ponens parameter retains both formula entries in their
original order; the implication premise is supplied by its constructor. -/
@[reassoc] theorem rho2_left (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) =
      prod.fst ≫ formulaIso.hom := by
  exact SubstitutionParameters.pairedIso_fst formulaIso formulaIso

@[reassoc] theorem rho2_conclusion (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map
        (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) =
      prod.snd ≫ formulaIso.hom := by
  exact SubstitutionParameters.pairedIso_snd formulaIso formulaIso

@[reassoc] theorem rho1_inverse_name (Γ : Carrier) :
    (rho1 Γ).inv ≫ prod.fst ≫ variableIso.hom =
      numericalInterpretation.map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols originalSyntax.algebra.a.2) variableSymbols) := by
  have h := congrArg (fun f => (rho1 Γ).inv ≫ f) (rho1_name Γ)
  simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using h.symm

@[reassoc] theorem rho1_inverse_premise (Γ : Carrier) :
    (rho1 Γ).inv ≫ prod.snd ≫ formulaIso.hom =
      numericalInterpretation.map
        (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) := by
  have h := congrArg (fun f => (rho1 Γ).inv ≫ f) (rho1_premise Γ)
  simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using h.symm

@[reassoc] theorem rho2_inverse_left (Γ : Carrier) :
    (rho2 Γ).inv ≫ prod.fst ≫ formulaIso.hom =
      numericalInterpretation.map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) := by
  have h := congrArg (fun f => (rho2 Γ).inv ≫ f) (rho2_left Γ)
  simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using h.symm

@[reassoc] theorem rho2_inverse_conclusion (Γ : Carrier) :
    (rho2 Γ).inv ≫ prod.snd ≫ formulaIso.hom =
      numericalInterpretation.map
        (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) := by
  have h := congrArg (fun f => (rho2 Γ).inv ≫ f) (rho2_conclusion Γ)
  simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using h.symm

/-- The unary conclusion is the quantified body at the retained binder name. -/
theorem rho1_rule_conclusion (Γ : Carrier) :
    (rho1 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).conclusion 1) =
      (rules Γ).conclusion 1 ≫ formulaIso.hom :=
  LogicalOperations.quantifier_square.symm

/-- The unary premise is its own body, independent of the parent conclusion. -/
theorem rho1_rule_premises (Γ : Carrier) :
    (rho1 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).premises 1) ≫
      (NumericalDerivationInterpretation.finitePowerIso originalSyntax.algebra.a.2 1).hom =
      (rules Γ).premises 1 ≫ finitePowerMap formulaIso.hom 1 := by
  change (rho1 Γ).hom ≫ numericalInterpretation.map
      (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) ≫
      𝟙 _ = (prod.snd : NumericalNamed.variableObject ⨯ numericalSyntax.algebra.a.2 ⟶ _) ≫ formulaIso.hom
  simpa only [Category.comp_id] using rho1_premise Γ

/-- The binary conclusion is the second formula in the original ordered pair. -/
theorem rho2_rule_conclusion (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).conclusion 2) =
      (rules Γ).conclusion 2 ≫ formulaIso.hom :=
  rho2_conclusion Γ

private theorem binary_power_comparison (A : PredicateCategory 𝗣𝗔) :
    (NumericalDerivationInterpretation.finitePowerIso A 2).hom = (Geometry.productIso A A).hom := by
  simp only [NumericalDerivationInterpretation.finitePowerIso,Iso.trans_hom,
    prod.mapIso_hom,Iso.refl_hom,prod.map_id_id,Category.comp_id]
  rfl

private theorem mapped_pair_fst {A B C : PredicateCategory 𝗣𝗔} (f : A ⟶ B) (g : A ⟶ C) :
    numericalInterpretation.map (prod.lift f g) ≫ (Geometry.productIso B C).hom ≫ prod.fst =
      numericalInterpretation.map f := by
  calc
    _ = numericalInterpretation.map (prod.lift f g) ≫ numericalInterpretation.map
        (prod.fst : B ⨯ C ⟶ B) :=
      congrArg (fun k => numericalInterpretation.map (prod.lift f g) ≫ k) (Geometry.product_fst B C)
    _ = numericalInterpretation.map ((prod.lift f g) ≫ prod.fst) :=
      (numericalInterpretation.map_comp _ _).symm
    _ = _ := congrArg numericalInterpretation.map (prod.lift_fst f g)

private theorem mapped_pair_snd {A B C : PredicateCategory 𝗣𝗔} (f : A ⟶ B) (g : A ⟶ C) :
    numericalInterpretation.map (prod.lift f g) ≫ (Geometry.productIso B C).hom ≫ prod.snd =
      numericalInterpretation.map g := by
  calc
    _ = numericalInterpretation.map (prod.lift f g) ≫ numericalInterpretation.map
        (prod.snd : B ⨯ C ⟶ C) :=
      congrArg (fun k => numericalInterpretation.map (prod.lift f g) ≫ k) (Geometry.product_snd B C)
    _ = numericalInterpretation.map ((prod.lift f g) ≫ prod.snd) :=
      (numericalInterpretation.map_comp _ _).symm
    _ = _ := congrArg numericalInterpretation.map (prod.lift_snd f g)

private theorem binary_pair_fst {A B : PredicateCategory 𝗣𝗔} (f g : A ⟶ B) :
    numericalInterpretation.map (prod.lift f g) ≫
      (NumericalDerivationInterpretation.finitePowerIso B 2).hom ≫ prod.fst =
        numericalInterpretation.map f := by
  rw [binary_power_comparison B]
  exact mapped_pair_fst f g

private theorem binary_pair_snd {A B : PredicateCategory 𝗣𝗔} (f g : A ⟶ B) :
    numericalInterpretation.map (prod.lift f g) ≫
      (NumericalDerivationInterpretation.finitePowerIso B 2).hom ≫ prod.snd =
        numericalInterpretation.map g := by
  rw [binary_power_comparison B]
  exact mapped_pair_snd f g

private theorem numerical_pair_fst {A B C D E : NumericalTuples.Object}
    (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ E) :
    (prod.lift f g ≫ prod.map u v) ≫ prod.fst = f ≫ u := by simp

private theorem numerical_pair_snd {A B C D E : NumericalTuples.Object}
    (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ E) :
    (prod.lift f g ≫ prod.map u v) ≫ prod.snd = g ≫ v := by simp

private theorem binary_inputs_compare {A B : PredicateCategory 𝗣𝗔} {C D : NumericalTuples.Object}
    (r : C ⟶ numericalInterpretation.obj A) (f g : A ⟶ B)
    (f' g' : C ⟶ D) (c : D ⟶ numericalInterpretation.obj B)
    (hf : r ≫ numericalInterpretation.map f = f' ≫ c)
    (hg : r ≫ numericalInterpretation.map g = g' ≫ c) :
    r ≫ numericalInterpretation.map (prod.lift f g) ≫
        (NumericalDerivationInterpretation.finitePowerIso B 2).hom =
      prod.lift f' g' ≫ prod.map c c := by
  change (r ≫ numericalInterpretation.map (prod.lift f g) ≫
      (NumericalDerivationInterpretation.finitePowerIso B 2).hom :
      C ⟶ (numericalInterpretation.obj B ⨯ numericalInterpretation.obj B)) =
    prod.lift f' g' ≫ prod.map c c
  apply prod.hom_ext (C := NumericalTuples.Object) (W := C)
    (X := numericalInterpretation.obj B) (Y := numericalInterpretation.obj B)
  · calc
      _ = r ≫ ((numericalInterpretation.map (prod.lift f g) ≫
          (NumericalDerivationInterpretation.finitePowerIso B 2).hom) ≫ prod.fst) :=
        Category.assoc r _ _
      _ = r ≫ (numericalInterpretation.map (prod.lift f g) ≫
          (NumericalDerivationInterpretation.finitePowerIso B 2).hom ≫ prod.fst) :=
        congrArg (fun k => r ≫ k) (Category.assoc _ _ _)
      _ = r ≫ numericalInterpretation.map f :=
        congrArg (fun k => r ≫ k) (binary_pair_fst f g)
      _ = f' ≫ c := hf
      _ = _ := (numerical_pair_fst f' g' c c).symm
  · calc
      _ = r ≫ ((numericalInterpretation.map (prod.lift f g) ≫
          (NumericalDerivationInterpretation.finitePowerIso B 2).hom) ≫ prod.snd) :=
        Category.assoc r _ _
      _ = r ≫ (numericalInterpretation.map (prod.lift f g) ≫
          (NumericalDerivationInterpretation.finitePowerIso B 2).hom ≫ prod.snd) :=
        congrArg (fun k => r ≫ k) (Category.assoc _ _ _)
      _ = r ≫ numericalInterpretation.map g :=
        congrArg (fun k => r ≫ k) (binary_pair_snd f g)
      _ = g' ≫ c := hg
      _ = _ := (numerical_pair_snd f' g' c c).symm

/-- The first child proves φ and the second proves φ⇒ψ. They are kept in
that order and are compared to their own prescribed premise formula. -/
theorem rho2_rule_premises (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).premises 2) ≫
      (NumericalDerivationInterpretation.finitePowerIso originalSyntax.algebra.a.2 2).hom =
      (rules Γ).premises 2 ≫ finitePowerMap formulaIso.hom 2 := by
  change (rho2 Γ).hom ≫ numericalInterpretation.map
      (prod.lift (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
        (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2)
        originalSyntax.implicationConstructor) ≫
      (NumericalDerivationInterpretation.finitePowerIso originalSyntax.algebra.a.2 2).hom =
    prod.lift (prod.fst : numericalSyntax.algebra.a.2 ⨯ numericalSyntax.algebra.a.2 ⟶ _)
      numericalSyntax.implicationConstructor ≫ prod.map formulaIso.hom formulaIso.hom
  exact binary_inputs_compare (rho2 Γ).hom
    (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2)
      originalSyntax.algebra.a.2) originalSyntax.implicationConstructor
    (prod.fst : numericalSyntax.algebra.a.2 ⨯ numericalSyntax.algebra.a.2 ⟶ numericalSyntax.algebra.a.2)
    numericalSyntax.implicationConstructor formulaIso.hom (rho2_left Γ)
    LogicalOperations.implication_square.symm

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Rules
