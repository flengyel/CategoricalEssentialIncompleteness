/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedRawModels


/-! # Unstructured named models of the recursive RCF axioms -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
open OrderedFieldSyntax RealClosedAxioms
universe u
variable {K : Type u} (M : Interpretation K)

example (h : ∀ word∈RCFAxiomWords,∃ φ : Formula,formulaCode φ=word ∧
    ∀ ρ : ℕ → K,φ.Holds M.functions M.relations ρ) :
    letI : Field K := fieldStructure M (matrices_valid_of_models M h)
    letI : LinearOrder K := linearOrderStructure M (matrices_valid_of_models M h)
    letI : IsStrictOrderedRing K := strictOrderedRing M (matrices_valid_of_models M h)
    IsRealClosed K := realClosed_of_models M h

example : (∀ word∈RCFAxiomWords,∃ φ : Formula,formulaCode φ=word ∧
    ∀ ρ : ℕ → K,φ.Holds M.functions M.relations ρ) ↔
    ∃ fieldInst : Field K,∃ orderInst : LinearOrder K,
      letI : Field K := fieldInst
      letI : LinearOrder K := orderInst
      ∃ compatible : IsStrictOrderedRing K,
        letI : IsStrictOrderedRing K := compatible
        IsRealClosed K ∧ M.functions=Semantics.functions (constantValue M) ∧
          M.relations=Semantics.relations (K := K) := modelsRCF_iff_exists_realization M

example (hM : ∀ φ∈finiteMatrices,∀ ρ : ℕ → K,φ.Holds M.functions M.relations ρ)
    (φ : Formula) (ρ : ℕ → K) :
    letI : Field K := fieldStructure M hM
    letI : LinearOrder K := linearOrderStructure M hM
    letI : IsStrictOrderedRing K := strictOrderedRing M hM
    φ.Holds M.functions M.relations ρ ↔ Semantics.Holds (constantValue M) φ ρ :=
  holds_comparison M hM φ ρ

example (a : Point) : ModelsWords M (RCFAxiomWords∪cutAxioms a) ↔
    ModelsWords M RCFAxiomWords ∧ ModelsWords M (cutAxioms a) := modelsTheory_iff M a

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
