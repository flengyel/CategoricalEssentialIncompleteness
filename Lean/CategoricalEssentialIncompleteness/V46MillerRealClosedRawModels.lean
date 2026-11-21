/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedRawOrderedField
public import CategoricalEssentialIncompleteness.V46MillerRealClosedAxiomsCharacterization

/-! # Unstructured named models of the recursive RCF axioms

An input has only the original total interpretations of the bounded named signature.
The finite matrices construct its ordered field, exact constructor/lt diagrams
identify the interpretations, and the positive-square and odd-Horner schemes prove
real closure. No field or order instance is an input of the final model
characterization.
-/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
open OrderedFieldSyntax RealClosedAxioms
universe u
variable {K : Type u}

/-- Word satisfaction, with the original literal formula code. -/
def ModelsWords (M : Interpretation K) (A : Set ℕ) : Prop := ∀ word∈A,
  ∃ φ : Formula,formulaCode φ=word ∧ ∀ ρ : ℕ → K,Holds M φ ρ

theorem formula_valid_of_models (M : Interpretation K) {A : Set ℕ} (h : ModelsWords M A)
    (φ : Formula) (hφ : formulaCode φ∈A) : ∀ ρ : ℕ → K,Holds M φ ρ := by
  obtain ⟨ψ,hcode,hvalid⟩ := h (formulaCode φ) hφ
  have he : ψ=φ := NamedPostfixEncoding.formulaCode_injective hcode
  exact he ▸ hvalid

private theorem matrix_closure_mem (φ : Formula) (hφ : φ∈finiteMatrices) :
    formulaCode (close [0,1,2] φ)∈RCFAxiomWords := by
  apply Or.inl
  exact List.mem_map.mpr ⟨close [0,1,2] φ,
    List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨φ,hφ,rfl⟩)),rfl⟩

/-- The final model premise itself supplies every finite matrix law. -/
theorem matrices_valid_of_models (M : Interpretation K) (h : ModelsWords M RCFAxiomWords) : MatricesValid M := by
  intro φ hφ ρ
  exact close_elim M [0,1,2] φ ρ
    (formula_valid_of_models M h (close [0,1,2] φ) (matrix_closure_mem φ hφ) ρ)

private theorem nullary_comparison (M : Interpretation K) (symbol : FunctionSymbols 0)
    (arguments : Fin 0 → K) :
    M.functions ⟨0,by decide⟩ symbol arguments=
      if symbol.val=0 then zeroValue M else if symbol.val=1 then oneValue M
      else constantValue M (symbol.val-2) := by
  have ha : arguments=Fin.elim0 := by funext i; exact Fin.elim0 i
  rw [ha]
  by_cases h0 : symbol.val=0
  · simp only [ite_eq_left h0]
    have hs : symbol=zeroSymbol := Subtype.ext h0
    exact congrArg (fun s => M.functions ⟨0,by decide⟩ s Fin.elim0) hs
  · by_cases h1 : symbol.val=1
    · simp only [ite_eq_right h0,ite_eq_left h1]
      have hs : symbol=oneSymbol := Subtype.ext h1
      exact congrArg (fun s => M.functions ⟨0,by decide⟩ s Fin.elim0) hs
    · simp only [ite_eq_right h0,ite_eq_right h1]
      have hs : symbol=constantSymbol (symbol.val-2) := Subtype.ext (by
        change symbol.val=(symbol.val-2)+2
        omega)
      exact congrArg (fun s => M.functions ⟨0,by decide⟩ s Fin.elim0) hs

/-- All arities and every symbol label are compared, including the nullary c_n labels. The
structure uses the original total functions. -/
theorem functions_comparison (M : Interpretation K) (hM : MatricesValid M) :
    let : Field K := fieldStructure M hM
    let : LinearOrder K := linearOrderStructure M hM
    let : IsStrictOrderedRing K := strictOrderedRing M hM
    M.functions=Semantics.functions (constantValue M) := by
  let : Field K := fieldStructure M hM
  let : LinearOrder K := linearOrderStructure M hM
  let : IsStrictOrderedRing K := strictOrderedRing M hM
  funext n symbol arguments
  rcases n with ⟨n,hn⟩
  have hcases : n=0 ∨ n=1 ∨ n=2 := by change n<3 at hn; omega
  rcases hcases with rfl | rfl | rfl
  · exact nullary_comparison M symbol arguments
  ·
      have hs : symbol=negSymbol := Subtype.ext ((functionSymbols_one symbol.val).mp symbol.property)
      have ha : arguments=![arguments 0] := by funext i; fin_cases i; rfl
      rw [hs,ha]
      rfl
  ·
      have ha : arguments=![arguments 0,arguments 1] := by funext i; fin_cases i <;> rfl
      rcases (functionSymbols_two symbol.val).mp symbol.property with h0 | h1
      · have hs : symbol=addSymbol := Subtype.ext h0
        rw [hs,ha]
        rfl
      · have hs : symbol=mulSymbol := Subtype.ext h1
        rw [hs,ha]
        rfl

/-- The sole relation is exactly the original interpreted strict order. -/
theorem relations_comparison (M : Interpretation K) (hM : MatricesValid M) :
    let : Field K := fieldStructure M hM
    let : LinearOrder K := linearOrderStructure M hM
    let : IsStrictOrderedRing K := strictOrderedRing M hM
    M.relations=Semantics.relations (K := K) := by
  let : Field K := fieldStructure M hM
  let : LinearOrder K := linearOrderStructure M hM
  let : IsStrictOrderedRing K := strictOrderedRing M hM
  funext n symbol arguments
  rcases n with ⟨n,hn⟩
  obtain ⟨rfl,hval⟩ := (relationSymbols_iff n symbol.val).mp symbol.property
  have hs : symbol=ltSymbol := Subtype.ext hval
  have ha : arguments=![arguments 0,arguments 1] := by funext i; fin_cases i <;> rfl
  rw [hs,ha]
  rfl

theorem term_value_comparison (M : Interpretation K) (hM : MatricesValid M) (t : Term) (ρ : ℕ → K) :
    let : Field K := fieldStructure M hM
    let : LinearOrder K := linearOrderStructure M hM
    let : IsStrictOrderedRing K := strictOrderedRing M hM
    value M t ρ=Semantics.value (constantValue M) t ρ := by
  let : Field K := fieldStructure M hM
  let : LinearOrder K := linearOrderStructure M hM
  let : IsStrictOrderedRing K := strictOrderedRing M hM
  change t.evaluate M.functions ρ=t.evaluate (Semantics.functions (constantValue M)) ρ
  rw [functions_comparison M hM]

theorem holds_comparison (M : Interpretation K) (hM : MatricesValid M) (φ : Formula) (ρ : ℕ → K) :
    let : Field K := fieldStructure M hM
    let : LinearOrder K := linearOrderStructure M hM
    let : IsStrictOrderedRing K := strictOrderedRing M hM
    Holds M φ ρ ↔ Semantics.Holds (constantValue M) φ ρ := by
  let : Field K := fieldStructure M hM
  let : LinearOrder K := linearOrderStructure M hM
  let : IsStrictOrderedRing K := strictOrderedRing M hM
  change φ.Holds M.functions M.relations ρ ↔
    φ.Holds (Semantics.functions (constantValue M)) (Semantics.relations (K := K)) ρ
  rw [functions_comparison M hM,relations_comparison M hM]

/-- The arbitrary named model has a real-closed ordered field on its
original carrier, with no supplied field or order premise. -/
theorem realClosed_of_models (M : Interpretation K) (h : ModelsWords M RCFAxiomWords) :
    let : Field K := fieldStructure M (matrices_valid_of_models M h)
    let : LinearOrder K := linearOrderStructure M (matrices_valid_of_models M h)
    let : IsStrictOrderedRing K := strictOrderedRing M (matrices_valid_of_models M h)
    IsRealClosed K := by
  let hM := matrices_valid_of_models M h
  let : Field K := fieldStructure M hM
  let : LinearOrder K := linearOrderStructure M hM
  let : IsStrictOrderedRing K := strictOrderedRing M hM
  apply Characterization.isRealClosed_of_models (constantValue M)
  intro word hw
  obtain ⟨φ,hcode,hvalid⟩ := h word hw
  exact ⟨φ,hcode,fun ρ => (holds_comparison M hM φ ρ).mp (hvalid ρ)⟩

/-- Exact identification for arbitrary total named structures. The ordered field and all
comparisons are constructed in the forward implication; they are not extra premises on
the input model. -/
theorem modelsRCF_iff_exists_realization (M : Interpretation K) : ModelsWords M RCFAxiomWords ↔
    ∃ fieldInst : Field K,∃ orderInst : LinearOrder K,
      let : Field K := fieldInst
      let : LinearOrder K := orderInst
      ∃ compatible : IsStrictOrderedRing K,
        let : IsStrictOrderedRing K := compatible
        IsRealClosed K ∧ M.functions=Semantics.functions (constantValue M) ∧
          M.relations=Semantics.relations (K := K) := by
  constructor
  · intro h
    let hM := matrices_valid_of_models M h
    refine ⟨fieldStructure M hM,linearOrderStructure M hM,strictOrderedRing M hM,?_,?_,?_⟩
    · exact realClosed_of_models M h
    · exact functions_comparison M hM
    · exact relations_comparison M hM
  · rintro ⟨fieldInst,orderInst,compatible,hrcf,hfunctions,hrelations⟩
    let : Field K := fieldInst
    let : LinearOrder K := orderInst
    let : IsStrictOrderedRing K := compatible
    let : IsRealClosed K := hrcf
    intro word hw
    obtain ⟨φ,hcode,hvalid⟩ := Semantics.rcf_words_valid (constantValue M) word hw
    refine ⟨φ,hcode,fun ρ => ?_⟩
    change φ.Holds M.functions M.relations ρ
    rw [hfunctions,hrelations]
    exact hvalid ρ

/-- The T_a adds exactly its literal cut words to this recursive field theory. No claim of
truth is made for arbitrary consistent Γ. -/
theorem modelsTheory_iff (M : Interpretation K) (a : Point) :
    ModelsWords M (theoryAxioms a) ↔ ModelsWords M RCFAxiomWords ∧ ModelsWords M (cutAxioms a) := by
  constructor
  · intro h
    exact ⟨fun word hw => h word (Or.inl hw),fun word hw => h word (Or.inr hw)⟩
  · rintro ⟨hrcf,hcut⟩ word (hw | hw)
    · exact hrcf word hw
    · exact hcut word hw

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedRaw
