/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationTupleCompatibility
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive

/-! Actual isomorphisms between chosen finite powers and literal ordered tuples. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The interpreted chosen terminal object has one point. -/
theorem modelTerminal_ext (x y : Obj T M (⊤_ (PredicateCategory T))) : x = y := by
  have ht := isLimitOfPreserves (PredicateInterpretation.functor T M)
    (Limits.terminalIsTerminal (C := PredicateCategory T))
  let a : PUnit ⟶ Obj T M (⊤_ (PredicateCategory T)) := ↾fun _ => x
  let b : PUnit ⟶ Obj T M (⊤_ (PredicateCategory T)) := ↾fun _ => y
  have he : a = b := ht.hom_ext (fun j => isEmptyElim j)
  exact ConcreteCategory.congr_hom he PUnit.unit

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Finite-power raw coordinates determine an actual categorical point;
this is proved only from the actual unit and product universal properties. -/
theorem powerRepresentation_point_unique (F : PredicateCategory T) (n : ℕ) (u : M)
    (x y : Obj T M ((SyntaxPolynomial.power .term n).eval.obj (F, F)))
    (hx : (baseRepresentation T F F (SyntaxPolynomial.power .term n)).val.Evalb ![u, x.val])
    (hy : (baseRepresentation T F F (SyntaxPolynomial.power .term n)).val.Evalb ![u, y.val]) :
    x = y := by
  induction n generalizing u with
  | zero => exact modelTerminal_ext T M x y
  | succ n ih =>
    cases n with
    | zero =>
      apply Subtype.ext
      exact ((baseRepresentation_term_eval T M F F u x.val).mp hx).2.trans
        ((baseRepresentation_term_eval T M F F u y.val).mp hy).2.symm
    | succ n =>
      obtain ⟨v, w, x₁, x₂, he, hx₁, hx₂, hxx₁, hxx₂⟩ :=
        (baseRepresentation_product_eval T M F F
          (SyntaxPolynomial.power .term (n + 1)) .term u x.val).mp hx
      obtain ⟨v', w', y₁, y₂, he', hy₁, hy₂, hyy₁, hyy₂⟩ :=
        (baseRepresentation_product_eval T M F F
          (SyntaxPolynomial.power .term (n + 1)) .term u y.val).mp hy
      have hv : v' = v := by simpa only [pi₁_pair] using congrArg pi₁ (he'.symm.trans he)
      have hw : w' = w := by simpa only [pi₂_pair] using congrArg pi₂ (he'.symm.trans he)
      subst v'
      subst w'
      let xx₁ : Obj T M ((SyntaxPolynomial.power .term (n + 1)).eval.obj (F, F)) :=
        ⟨x₁, ((chosenGraph T prod.fst).support_model M x.val x₁ hxx₁).2⟩
      let yy₁ : Obj T M ((SyntaxPolynomial.power .term (n + 1)).eval.obj (F, F)) :=
        ⟨y₁, ((chosenGraph T prod.fst).support_model M y.val y₁ hyy₁).2⟩
      let xx₂ : Obj T M F :=
        ⟨x₂, ((chosenGraph T prod.snd).support_model M x.val x₂ hxx₂).2⟩
      let yy₂ : Obj T M F :=
        ⟨y₂, ((chosenGraph T prod.snd).support_model M y.val y₂ hyy₂).2⟩
      have h₁ : xx₁ = yy₁ := ih v xx₁ yy₁ hx₁ hy₁
      have h₂ : xx₂ = yy₂ := Subtype.ext
        (((baseRepresentation_term_eval T M F F w x₂).mp hx₂).2.trans
          ((baseRepresentation_term_eval T M F F w y₂).mp hy₂).2.symm)
      exact modelProduct_ext T M
        (((chosenGraph_map_iff T M prod.fst x xx₁).mp hxx₁).trans
          (h₁.trans ((chosenGraph_map_iff T M prod.fst y yy₁).mp hyy₁).symm))
        (((chosenGraph_map_iff T M prod.snd x xx₂).mp hxx₂).trans
          (h₂.trans ((chosenGraph_map_iff T M prod.snd y yy₂).mp hyy₂).symm))

end Models

/-- The inverse is obtained from the existing all-model converse-graph
construction after proving bijectivity of these particular actual encoders. -/
theorem powerPolynomialEncoder_isIso (F : PredicateCategory T) (n : ℕ) :
    IsIso (representedArrow T (encodePolynomial T F F (SyntaxPolynomial.power .term n))) := by
  apply PredicateInterpretation.isIso_of_models_bijective T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  let e := encodePolynomial T F F (SyntaxPolynomial.power .term n)
  constructor
  · intro x y h
    let u := (PredicateInterpretation.functor T M).map (representedArrow T e) x
    have hxg := (PredicateInterpretation.map_class_eq_iff T M e x u).mp rfl
    have hyg := (PredicateInterpretation.map_class_eq_iff T M e y u).mp h.symm
    have hx : (baseRepresentation T F F (SyntaxPolynomial.power .term n)).val.Evalb
        ![u.val, x.val] := by simpa [e, encodePolynomial] using hxg
    have hy : (baseRepresentation T F F (SyntaxPolynomial.power .term n)).val.Evalb
        ![u.val, y.val] := by simpa [e, encodePolynomial] using hyg
    exact powerRepresentation_point_unique T M F n u.val x y hx hy
  · intro u
    obtain ⟨z, hz⟩ := baseRepresentation_exists T M F F
      (SyntaxPolynomial.power .term n) u.val u.property
    refine ⟨z, (PredicateInterpretation.map_class_eq_iff T M e z u).mpr ?_⟩
    simpa [e, encodePolynomial] using hz

theorem finitePowerEncoder_isIso (F : PredicateCategory T) (n : ℕ) :
    IsIso (representedArrow T (finitePowerEncoder T F n)) := by
  rw [finitePowerEncoder_arrow]
  have := powerPolynomialEncoder_isIso T F n
  infer_instance

def finitePowerIso (F : PredicateCategory T) (n : ℕ) :
    CategoryTheory.Iso (C := PredicateCategory T)
      (finitePower (D := PredicateCategory T) F n) (tupleCarrier F n) := by
  have := finitePowerEncoder_isIso T F n
  exact asIso (representedArrow T (finitePowerEncoder T F n))

@[simp] theorem finitePowerIso_hom (F : PredicateCategory T) (n : ℕ) :
    (finitePowerIso T F n).hom = representedArrow T (finitePowerEncoder T F n) := rfl

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation
