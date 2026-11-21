/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSentenceReflection
public import CategoricalEssentialIncompleteness.V46MillerDerivationWordFirstOrderInduction

/-! # Finite Gamma support under Gen and ordered MP

Generalization retains the child's finite support. Modus ponens joins the two finite
supports by the existing Hilbert axiom-replacement proof; the antecedent and
implication keep their original premise order.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "U" => (Total.underlying (P := P))
local notation "S" => syntaxData P σ π d
local notation "V" => CategoryTheory.Functor.obj (Syntax.predicateFunctor P)
  (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)

theorem generalization_finite (z : (U).obj ((V) ⨯ (S).algebra.a.2))
    (h : FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map prod.snd z))) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).quantifierConstructor z)) := by
  rw [decode_quantifier]
  exact FiniteAxiomProof.generalization σ π d ((U).map prod.fst z).val h

theorem modusPonens_finite (z : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2))
    (hφ : FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map prod.fst z)))
    (himp : FiniteAxiomProof σ π d Γ
      (decodeFormula P σ π d ((U).map (S).implicationConstructor z))) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map prod.snd z)) := by
  rw [decode_implication] at himp
  exact FiniteAxiomProof.modusPonens σ π d hφ himp

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
