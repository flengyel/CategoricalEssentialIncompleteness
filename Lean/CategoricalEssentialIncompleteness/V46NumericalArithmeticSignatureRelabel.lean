/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixEncoding
public import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbert
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationParser

/-! # Identity-on-code signature comparisons preserve named finite syntax -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel
open NamedFiniteSyntax NamedPostfixEncoding

section Coding
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- These shared algorithm laws are proved in the generic parser bridge. -/
theorem shape_map (f : Carrier → Carrier) (p : RawPolynomial) (u : M) :
    shape (p.mapCoefficients f) u = shape p u :=
  NumericalDerivationInterpretation.Parser.shape_map f p u

theorem childrenWord_map (f : Carrier → Carrier) (p : RawPolynomial) (u : M) :
    childrenWord (p.mapCoefficients f) u = childrenWord p u :=
  NumericalDerivationInterpretation.Parser.childrenWord_map f p u

theorem constructor_map (f : Carrier → Carrier) (p : RawPolynomial) (formula : Bool) (u : M) :
    constructor formula (p.mapCoefficients f) u = constructor formula p u :=
  NumericalDerivationInterpretation.Parser.constructor_map f p formula u

private theorem erased_term (σ τ : ℕ → Carrier) (d : ℕ) :
    (termPolynomial σ d).mapCoefficients (fun _ => zeroCarrier) =
      (termPolynomial τ d).mapCoefficients (fun _ => zeroCarrier) := by
  simp only [termPolynomial,SyntaxOperationsTransport.mapCoefficients_termExpression]

private theorem erased_formula (π ρ : ℕ → Carrier) (d : ℕ) :
    (formulaPolynomial π d).mapCoefficients (fun _ => zeroCarrier) =
      (formulaPolynomial ρ d).mapCoefficients (fun _ => zeroCarrier) := by
  simp only [formulaPolynomial,SyntaxOperationsTransport.mapCoefficients_formulaExpression]

theorem constructor_term (σ τ : ℕ → Carrier) (d : ℕ) (formula : Bool) (u : M) :
    constructor formula (termPolynomial σ d) u = constructor formula (termPolynomial τ d) u := by
  rw [← constructor_map (fun _ => zeroCarrier) (termPolynomial σ d),
    erased_term σ τ,constructor_map]

theorem constructor_formula (π ρ : ℕ → Carrier) (d : ℕ) (formula : Bool) (u : M) :
    constructor formula (formulaPolynomial π d) u = constructor formula (formulaPolynomial ρ d) u := by
  rw [← constructor_map (fun _ => zeroCarrier) (formulaPolynomial π d),
    erased_formula π ρ,constructor_map]

end Coding

variable {σ τ π ρ : ℕ → Carrier} {d : ℕ}

/-- The underlying symbol number is retained exactly. -/
def symbols (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n]) (k : ℕ) :
    Symbols σ k ≃ Symbols τ k where
  toFun s := ⟨s.val,(h k s.val).mp s.property⟩
  invFun s := ⟨s.val,(h k s.val).mpr s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem symbols_value
    (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
    (k : ℕ) (s : Symbols σ k) : (symbols h k s).val = s.val := rfl

def term (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n]) :
    Term (Symbols σ) d → Term (Symbols τ) d
  | .var x => .var x
  | .app k f children => .app k (symbols h k.val f) (fun i => term h (children i))

def formula (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
    (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n]) :
    Formula (Symbols σ) (Symbols π) d → Formula (Symbols τ) (Symbols ρ) d
  | .equal r t => .equal (term h r) (term h t)
  | .relation k p children => .relation k (symbols j k.val p) (fun i => term h (children i))
  | .neg φ => .neg (formula h j φ)
  | .imp φ ψ => .imp (formula h j φ) (formula h j ψ)
  | .all x φ => .all x (formula h j φ)

variable (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
  (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])

@[simp] theorem term_inverse (r : Term (Symbols σ) d) :
    term (fun k n => (h k n).symm) (term h r) = r := by
  induction r with
  | var x => rfl
  | app k f children ih =>
      simp only [term]
      congr 1
      funext i
      exact ih i

@[simp] theorem formula_inverse (φ : Formula (Symbols σ) (Symbols π) d) :
    formula (fun k n => (h k n).symm) (fun k n => (j k n).symm) (formula h j φ) = φ := by
  induction φ with
  | equal r t => simp only [formula,term_inverse]
  | relation k p children =>
      simp only [formula]
      congr 1
      funext i
      exact term_inverse h (children i)
  | neg φ ih => simp only [formula,ih]
  | imp φ ψ ihφ ihψ => simp only [formula,ihφ,ihψ]
  | all x φ ih => simp only [formula,ih]

def termEquiv : Term (Symbols σ) d ≃ Term (Symbols τ) d where
  toFun := term h
  invFun := term (fun k n => (h k n).symm)
  left_inv := term_inverse h
  right_inv := term_inverse (fun k n => (h k n).symm)

def formulaEquiv : Formula (Symbols σ) (Symbols π) d ≃ Formula (Symbols τ) (Symbols ρ) d where
  toFun := formula h j
  invFun := formula (fun k n => (h k n).symm) (fun k n => (j k n).symm)
  left_inv := formula_inverse h j
  right_inv := formula_inverse (fun k n => (h k n).symm) (fun k n => (j k n).symm)

@[simp] theorem term_freeVariables (r : Term (Symbols σ) d) :
    (term h r).freeVariables = r.freeVariables := by
  induction r with
  | var x => rfl
  | app k f children ih => simp only [term,Term.freeVariables,ih]

@[simp] theorem formula_freeVariables (φ : Formula (Symbols σ) (Symbols π) d) :
    (formula h j φ).freeVariables = φ.freeVariables := by
  induction φ with
  | equal r t => simp only [formula,Formula.freeVariables,term_freeVariables]
  | relation k p children => simp only [formula,Formula.freeVariables,term_freeVariables]
  | neg φ ih => simp only [formula,Formula.freeVariables,ih]
  | imp φ ψ ihφ ihψ => simp only [formula,Formula.freeVariables,ihφ,ihψ]
  | all x φ ih => simp only [formula,Formula.freeVariables,ih]

@[simp] theorem term_substitute (r t : Term (Symbols σ) d) (x : ℕ) :
    term h (r.substitute x t) = (term h r).substitute x (term h t) := by
  induction r with
  | var y => by_cases hy : y = x <;> simp only [Term.substitute,term,hy,ite_true,ite_false]
  | app k f children ih =>
      simp only [Term.substitute,term]
      congr 1
      funext i
      exact ih i

@[simp] theorem formula_substitute (φ : Formula (Symbols σ) (Symbols π) d)
    (x : ℕ) (t : Term (Symbols σ) d) :
    Option.map (formula h j) (φ.substitute x t) =
      (formula h j φ).substitute x (term h t) := by
  induction φ with
  | equal r s => simp only [Formula.substitute,formula,term_substitute,Option.map_some]
  | relation k p children => simp only [Formula.substitute,formula,term_substitute,Option.map_some]
  | neg φ ih =>
      change Option.map (formula h j) ((φ.substitute x t).map Formula.neg) =
        ((formula h j φ).substitute x (term h t)).map Formula.neg
      rw [← ih,Option.map_map,Option.map_map]
      rfl
  | imp φ ψ ihφ ihψ =>
      change Option.map (formula h j)
          (do let l ← φ.substitute x t; let r ← ψ.substitute x t; pure (Formula.imp l r)) =
        (do let l ← (formula h j φ).substitute x (term h t)
            let r ← (formula h j ψ).substitute x (term h t)
            pure (Formula.imp l r))
      rw [← ihφ,← ihψ]
      cases he : φ.substitute x t <;> cases hf : ψ.substitute x t <;> rfl
  | all y φ ih =>
      by_cases hy : y = x
      · simp [Formula.substitute,formula,hy]
      · by_cases hc : x ∉ φ.freeVariables ∨ y ∉ t.freeVariables
        · simp only [Formula.substitute,formula,hy,ite_false,formula_freeVariables,
            term_freeVariables,hc,ite_true]
          rw [← ih,Option.map_map,Option.map_map]
          rfl
        · simp [Formula.substitute,formula,hy,hc]

@[simp] theorem formula_freeFor (φ : Formula (Symbols σ) (Symbols π) d)
    (x : ℕ) (t : Term (Symbols σ) d) :
    (formula h j φ).FreeFor x (term h t) ↔ φ.FreeFor x t := by
  induction φ with
  | equal r s => rfl
  | relation k p children => rfl
  | neg φ ih => exact ih
  | imp φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | all y φ ih =>
      simp only [formula,Formula.FreeFor,formula_freeVariables,term_freeVariables,ih]

/-- Named variables and ordered children have the same stored code. -/
@[simp] theorem term_code (r : Term (Symbols σ) d) : termCode (term h r) = termCode r := by
  induction r with
  | var x => exact constructor_term τ σ d false _
  | app k f children ih =>
      change constructor false (termPolynomial τ d) _ = _
      rw [constructor_term τ σ]
      simp only [termCode,symbols_value,ih]

@[simp] theorem formula_code (φ : Formula (Symbols σ) (Symbols π) d) :
    formulaCode (formula h j φ) = formulaCode φ := by
  induction φ with
  | equal r t =>
      change constructor true (formulaPolynomial ρ d) _ = _
      rw [constructor_formula ρ π]
      simp only [formulaCode,term_code]
  | relation k p children =>
      change constructor true (formulaPolynomial ρ d) _ = _
      rw [constructor_formula ρ π]
      simp only [formulaCode,symbols_value,term_code]
  | neg φ ih =>
      change constructor true (formulaPolynomial ρ d) _ = _
      rw [constructor_formula ρ π]
      simp only [formulaCode,ih]
  | imp φ ψ ihφ ihψ =>
      change constructor true (formulaPolynomial ρ d) _ = _
      rw [constructor_formula ρ π]
      simp only [formulaCode,ihφ,ihψ]
  | all x φ ih =>
      change constructor true (formulaPolynomial ρ d) _ = _
      rw [constructor_formula ρ π]
      simp only [formulaCode,ih]

/-- The seven schemes and both ordered rules are preserved with the same axiom
enumeration. -/
theorem derives (Γ : Carrier) {φ : Formula (Symbols σ) (Symbols π) d}
    (hp : SyntacticNamedHilbert.Derives σ π d Γ φ) :
    SyntacticNamedHilbert.Derives τ ρ d Γ (formula h j φ) := by
  induction hp with
  | «axiom» φ he hs =>
      exact .axiom _ (by simpa only [formula_code] using he)
        (by simpa only [formula_freeVariables] using hs)
  | one φ ψ => exact .one _ _
  | two φ ψ χ => exact .two _ _ _
  | three φ ψ => exact .three _ _
  | instantiation x φ t ψ hf hs =>
      apply SyntacticNamedHilbert.Derives.instantiation x (formula h j φ) (term h t) (formula h j ψ)
      · exact (formula_freeFor h j φ x t).mpr hf
      · rw [← formula_substitute,hs,Option.map_some]
  | distribution x φ ψ hx =>
      apply SyntacticNamedHilbert.Derives.distribution x (formula h j φ) (formula h j ψ)
      simpa only [formula_freeVariables] using hx
  | reflexivity t => exact .reflexivity _
  | equality x φ u t ψ χ hfu hft hsu hst =>
      apply SyntacticNamedHilbert.Derives.equality x (formula h j φ) (term h u) (term h t)
        (formula h j ψ) (formula h j χ)
      · exact (formula_freeFor h j φ x u).mpr hfu
      · exact (formula_freeFor h j φ x t).mpr hft
      · rw [← formula_substitute,hsu,Option.map_some]
      · rw [← formula_substitute,hst,Option.map_some]
  | generalization x hp ih => exact .generalization x ih
  | modusPonens hp hq ihp ihq => exact .modusPonens ihp ihq

theorem derives_iff (Γ : Carrier) (φ : Formula (Symbols σ) (Symbols π) d) :
    SyntacticNamedHilbert.Derives τ ρ d Γ (formula h j φ) ↔
      SyntacticNamedHilbert.Derives σ π d Γ φ := by
  constructor
  · intro hp
    simpa only [formula_inverse] using
      derives (fun k n => (h k n).symm) (fun k n => (j k n).symm) Γ hp
  · exact derives h j Γ

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel
