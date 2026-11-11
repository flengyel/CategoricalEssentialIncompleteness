/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformPredicates


/-! # Statement checks in `V46ArithmeticUniformPredicatesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformPredicatesChecks
open ArithmeticUniformSearch NamedArithmeticSignature
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (P : 𝚺₁.Semisentence 2) (φ : Formula) (e x : M) :
    (positive P φ).val.Evalb ![e,x] ↔
      P.val.Evalb ![e,NamedArithmeticFixedSubstitution.value φ x] := positive_eval M P φ e x
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (P : 𝚺₁.Semisentence 2) (φ : Formula) (e x : M) :
    (negative P φ).val.Evalb ![e,x] ↔
      P.val.Evalb ![e,NamedArithmeticProofSearch.negationWord M
        (NamedArithmeticFixedSubstitution.value φ x)] := negative_eval M P φ e x
example (P : 𝚺₁.Semisentence 2) :
    ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ NamedArithmeticLiteralTotal.literalSentence :=
  proofSentenceMorphism P
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformPredicatesChecks
