/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedPostfixData
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition

/-! # Every standard accepted word encodes a literal named finite tree

This standard-model statement does not assert that nonstandard model
words are encodings of external finite trees.
-/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
open CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding

theorem standard_codes_surjective (σ π : ℕ → Carrier) (d : ℕ) :
    (∀ word : ℕ, (carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![word] →
      ∃ r : NamedFiniteSyntax.Term (Symbols σ) d, termCode r = word) ∧
    (∀ word : ℕ, (carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![word] →
      ∃ φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d, formulaCode φ = word) := by
  classical
  let a := termPolynomial σ d
  let b := formulaPolynomial π d
  have hdecode : ∀ n : ℕ,
      (∀ word : ℕ, len word = n → (carrier false a b).val.Evalb ![word] →
        ∃ r : NamedFiniteSyntax.Term (Symbols σ) d, termCode r = word) ∧
      (∀ word : ℕ, len word = n → (carrier true a b).val.Evalb ![word] →
        ∃ φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d, formulaCode φ = word) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        constructor
        · intro word hlen hw
          obtain ⟨u, hu, he⟩ := carrier_decomposition false a b word hw
          change word = constructor false a u at he
          have hs := children_smaller false a u
          rw [childSizeGraph_eval, ← he, hlen] at hs
          have hd := refine_children a n u ((rawCarrier_iff_data _ _ a u).mp hu) hs
          rcases hd with ⟨x, hx, _⟩ | ⟨args, ha, hd⟩
          · refine ⟨.var x, ?_⟩
            change constructor false a (Arithmetic.pair x 0) = word
            rw [← hx]
            exact he.symm
          · obtain ⟨k, s, words, hargs, hchildren⟩ := arityInput_decomposition σ d args hd
            have hex (i : Fin k.val) : ∃ r : NamedFiniteSyntax.Term (Symbols σ) d, termCode r = words i :=
              (ih (len (words i)) (hchildren i).2).1 (words i) rfl (hchildren i).1
            let children (i : Fin k.val) : NamedFiniteSyntax.Term (Symbols σ) d := Classical.choose (hex i)
            have hc : (fun i => termCode (children i)) = words :=
              funext (fun i => Classical.choose_spec (hex i))
            refine ⟨.app k s children, ?_⟩
            change constructor false a (Arithmetic.pair (arityInput d k
              (Arithmetic.pair s.val (childTuple k.val (fun i => termCode (children i))))) 1) = word
            rw [hc, ← hargs, ← ha]
            exact he.symm
        · intro word hlen hw
          obtain ⟨u, hu, he⟩ := carrier_decomposition true a b word hw
          change word = constructor true b u at he
          have hs := children_smaller true b u
          rw [childSizeGraph_eval, ← he, hlen] at hs
          have hd := refine_children b n u ((rawCarrier_iff_data _ _ b u).mp hu) hs
          rcases formulaData_cases π d u hd with
            ⟨r, t, hr, hrm, htm⟩ | ⟨k, s, words, hr, hc⟩ |
            ⟨body, hr, hb⟩ | ⟨left, right, hr, hl, hh⟩ | ⟨name, body, hr, hb⟩
          · obtain ⟨r', er⟩ := (ih (len r) hrm.2).1 r rfl hrm.1
            obtain ⟨t', et⟩ := (ih (len t) htm.2).1 t rfl htm.1
            refine ⟨.equal r' t', ?_⟩
            change constructor true b (equalInput (termCode r') (termCode t')) = word
            rw [er, et, ← hr]
            exact he.symm
          · have hex (i : Fin k.val) : ∃ r : NamedFiniteSyntax.Term (Symbols σ) d, termCode r = words i :=
              (ih (len (words i)) (hc i).2).1 (words i) rfl (hc i).1
            let children (i : Fin k.val) : NamedFiniteSyntax.Term (Symbols σ) d := Classical.choose (hex i)
            have hcodes : (fun i => termCode (children i)) = words :=
              funext (fun i => Classical.choose_spec (hex i))
            refine ⟨.relation k s children, ?_⟩
            change constructor true b (relationInput d k s.val (fun i => termCode (children i))) = word
            rw [hcodes, ← hr]
            exact he.symm
          · obtain ⟨body', eb⟩ := (ih (len body) hb.2).2 body rfl hb.1
            refine ⟨.neg body', ?_⟩
            change constructor true b (negInput (formulaCode body')) = word
            rw [eb, ← hr]
            exact he.symm
          · obtain ⟨left', el⟩ := (ih (len left) hl.2).2 left rfl hl.1
            obtain ⟨right', er⟩ := (ih (len right) hh.2).2 right rfl hh.1
            refine ⟨.imp left' right', ?_⟩
            change constructor true b (impInput (formulaCode left') (formulaCode right')) = word
            rw [el, er, ← hr]
            exact he.symm
          · obtain ⟨body', eb⟩ := (ih (len body) hb.2).2 body rfl hb.1
            refine ⟨.all name body', ?_⟩
            change constructor true b (allInput name (formulaCode body')) = word
            rw [eb, ← hr]
            exact he.symm
  exact ⟨fun word hw => (hdecode (len word)).1 word rfl hw,
    fun word hw => (hdecode (len word)).2 word rfl hw⟩

end CategoricalEssentialIncompleteness.V46.NamedPostfixEncoding
