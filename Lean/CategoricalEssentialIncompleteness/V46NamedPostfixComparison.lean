/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixDecoding

/-! # Named finite syntax and standard accepted words -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
open CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
variable {σ π : ℕ → Carrier} {d : ℕ}

theorem termInputs_eq {r t : NamedFiniteSyntax.Term (Symbols σ) d}
    (h : termCode r = termCode t) : termInput r = termInput t := by
  let π : ℕ → Carrier := fun _ => variableCarrier
  apply constructor_injective false (termPolynomial σ d) (formulaPolynomial π d)
    (termPolynomial σ d) (termInput r) (termInput t)
  · exact termInput_member π r
  · exact termInput_member π t
  · simpa only [termCode_root] using h

theorem formulaInputs_eq {φ ψ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d}
    (h : formulaCode φ = formulaCode ψ) : formulaInput φ = formulaInput ψ := by
  apply constructor_injective true (termPolynomial σ d) (formulaPolynomial π d)
    (formulaPolynomial π d) (formulaInput φ) (formulaInput ψ)
  · exact formulaInput_member φ
  · exact formulaInput_member ψ
  · simpa only [formulaCode_root] using h

theorem termCode_injective : Function.Injective (termCode (σ := σ) (d := d)) := by
  intro r
  induction r with
  | var x =>
      intro t h
      have hi := termInputs_eq h
      cases t with
      | var y =>
          have he : x = y := by simpa only [termInput, pair_eq_pair_iff, and_true] using hi
          exact congrArg NamedFiniteSyntax.Term.var he
      | app k f children =>
          simp only [termInput, pair_eq_pair_iff, _root_.zero_ne_one, and_false] at hi
  | app k f children ih =>
      intro t h
      have hi := termInputs_eq h
      cases t with
      | var y =>
          simp only [termInput, pair_eq_pair_iff, _root_.one_ne_zero, and_false] at hi
      | app l g other =>
          have hs : arityInput d k (Arithmetic.pair f.val
                (childTuple k.val (fun i => termCode (children i)))) =
              arityInput d l (Arithmetic.pair g.val
                (childTuple l.val (fun i => termCode (other i)))) := by
            simpa only [termInput, pair_eq_pair_iff, and_true] using hi
          obtain ⟨hkl, hp⟩ := arityInput_injective d k l _ _ hs
          subst l
          obtain ⟨hf, hc⟩ := (pair_eq_pair_iff _ _ _ _).mp hp
          have hfg : f = g := Subtype.ext hf
          subst g
          have hcodes := childTuple_injective k.val _ _ hc
          have hchildren : children = other :=
            funext (fun i => ih i (congrFun hcodes i))
          rw [hchildren]

theorem formulaCode_injective : Function.Injective (formulaCode (σ := σ) (π := π) (d := d)) := by
  intro φ
  induction φ with
  | equal r t =>
      intro ψ h
      have hi := formulaInputs_eq h
      cases ψ <;> simp only [formulaInput, equalInput, relationInput, negInput, impInput,
        allInput, pair_eq_pair_iff, and_true, and_false, _root_.zero_ne_one] at hi
      rename_i u v
      exact congrArg₂ NamedFiniteSyntax.Formula.equal
        (termCode_injective hi.1) (termCode_injective hi.2)
  | relation k p children =>
      intro ψ h
      have hi := formulaInputs_eq h
      cases ψ <;> simp only [formulaInput, equalInput, relationInput, negInput, impInput,
        allInput, pair_eq_pair_iff, and_true, and_false, _root_.zero_ne_one, _root_.one_ne_zero] at hi
      rename_i l q other
      obtain ⟨hkl, hp⟩ := arityInput_injective d k l _ _ hi
      subst l
      obtain ⟨hs, hc⟩ := (pair_eq_pair_iff _ _ _ _).mp hp
      have hpq : p = q := Subtype.ext hs
      subst q
      have hcodes := childTuple_injective k.val _ _ hc
      have hchildren : children = other :=
        funext (fun i => termCode_injective (congrFun hcodes i))
      rw [hchildren]
  | neg body ih =>
      intro ψ h
      have hi := formulaInputs_eq h
      cases ψ <;> simp only [formulaInput, equalInput, relationInput, negInput, impInput,
        allInput, pair_eq_pair_iff, and_true, and_false, _root_.zero_ne_one, _root_.one_ne_zero] at hi
      rename_i other
      exact congrArg NamedFiniteSyntax.Formula.neg (ih hi)
  | imp left right il ir =>
      intro ψ h
      have hi := formulaInputs_eq h
      cases ψ <;> simp only [formulaInput, equalInput, relationInput, negInput, impInput,
        allInput, pair_eq_pair_iff, and_true, and_false, _root_.zero_ne_one, _root_.one_ne_zero] at hi
      rename_i left' right'
      exact congrArg₂ NamedFiniteSyntax.Formula.imp (il hi.1) (ir hi.2)
  | all name body ih =>
      intro ψ h
      have hi := formulaInputs_eq h
      cases ψ <;> simp only [formulaInput, equalInput, relationInput, negInput, impInput,
        allInput, pair_eq_pair_iff, and_true, and_false, _root_.one_ne_zero] at hi
      rename_i name' body'
      exact congrArg₂ NamedFiniteSyntax.Formula.all hi.1 (ih hi.2)

def termWords (σ π : ℕ → Carrier) (d : ℕ) :=
  {word : ℕ // (carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![word]}

def formulaWords (σ π : ℕ → Carrier) (d : ℕ) :=
  {word : ℕ // (carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![word]}

/-- The standard interpretation is compared by the word number. All variable, symbol and
binder labels are retained literally. -/
def termEquiv (σ π : ℕ → Carrier) (d : ℕ) :
    NamedFiniteSyntax.Term (Symbols σ) d ≃ termWords σ π d :=
  Equiv.ofBijective (fun r => ⟨termCode r, termCode_member π r⟩)
    ⟨fun r t h => termCode_injective (congrArg Subtype.val h), fun word => by
      obtain ⟨r, hr⟩ := (standard_codes_surjective σ π d).1 word.val word.property
      exact ⟨r, Subtype.ext hr⟩⟩

def formulaEquiv (σ π : ℕ → Carrier) (d : ℕ) :
    NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d ≃ formulaWords σ π d :=
  Equiv.ofBijective (fun φ => ⟨formulaCode φ, formulaCode_member φ⟩)
    ⟨fun φ ψ h => formulaCode_injective (congrArg Subtype.val h), fun word => by
      obtain ⟨φ, hφ⟩ := (standard_codes_surjective σ π d).2 word.val word.property
      exact ⟨φ, Subtype.ext hφ⟩⟩

@[simp] theorem termEquiv_val (r : NamedFiniteSyntax.Term (Symbols σ) d) :
    (termEquiv σ π d r).val = termCode r := rfl

@[simp] theorem formulaEquiv_val (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (formulaEquiv σ π d φ).val = formulaCode φ := rfl

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
