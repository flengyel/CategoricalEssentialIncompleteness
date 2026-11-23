/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticComplementaryInclusions
public import CategoricalEssentialIncompleteness.V46SubstitutionSource
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesImages

/-! # Substitution on its source and the two inverses in Lemma 8.9 -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.ProofSearch FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.V46 SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.AdmissibilityAndComplementChecks

section Admissibility
open ConcreteNamedSubstitution ConcreteNamedComparison SyntacticSyntax SyntacticLists

variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
theorem substitution_domains :
    let b := fun p : ℕ × ℕ × ℕ => substitutionFreeFor V σ π d p.1 p.2.1 p.2.2
    let D := fun p : ℕ × ℕ × ℕ => V.val.Evalb ![p.1] ∧
      (plainSyntaxCarrier V σ π d false).val.Evalb ![p.2.1] ∧
      (plainSyntaxCarrier V σ π d true).val.Evalb ![p.2.2]
    Primrec b ∧
    REPred (fun p => D p ∧ b p = 1) ∧ REPred (fun p => D p ∧ b p = 0) ∧
    ∀ p, D p → (b p = 0 ↔ b p ≠ 1) :=
  ⟨substitutionFreeFor_primrec V σ π d, substitutionBranch_enumerable V σ π d 1,
    substitutionBranch_enumerable V σ π d 0, substitution_failure_iff V σ π d⟩

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "Params" =>
  CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "Tm" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Fm" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)

example (n : M) :
    (plainAdmissibleCarrier T V σ π d).val.Evalb ![n] ↔
      ∃ h : (Fm ⨯ Params : PredicateCategory T).val.Evalb ![n],
        let q : Obj T M (Fm ⨯ Params) := ⟨n, h⟩
        substitutionFreeFor V σ π d
          ((F T M).map (prod.fst : Params ⟶ V) ((F T M).map prod.snd q)).val
          ((F T M).map (prod.snd : Params ⟶ Tm) ((F T M).map prod.snd q)).val
          ((F T M).map prod.fst q).val = 1 :=
  admissible_iff_source_and_success V σ π d T M n

end Admissibility

section Diagonal
open ArithmeticOmegaComparison ArithmeticComplementaryInclusions

example {X : TotalSplit 𝗣𝗔} (A : Subobject X) :
    ∃ r : X.obj ⟶ (A : TotalSplit 𝗣𝗔).obj,
      A.arrow.hom ≫ r = 𝟙 _ ∧ r ≫ A.arrow.hom = rst r :=
  totalSplit_mono_partial_inverse 𝗣𝗔 A.arrow

example : leftInjection.hom.hom = CoprodStruct.i0 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) ∧
    rightInjection.hom.hom = CoprodStruct.i1 (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) :=
  ⟨rfl, rfl⟩

example (A B : Subobject (identityOmega 𝗣𝗔)) (h : IsCompl A B) :
    ∃ (c : (A : TotalSplit 𝗣𝗔) ⨿ (B : TotalSplit 𝗣𝗔) ≅ identityOmega 𝗣𝗔)
      (ℓ : identityOmega 𝗣𝗔 ⟶ numberSum),
      c.hom = coprod.desc A.arrow B.arrow ∧
      ℓ = c.inv ≫ coprod.desc (A.arrow ≫ rightInjection) (B.arrow ≫ leftInjection) ∧
      A.arrow ≫ ℓ = A.arrow ≫ rightInjection ∧ B.arrow ≫ ℓ = B.arrow ≫ leftInjection ∧
      rst ℓ.hom.hom = 𝟙 (omegaObject 𝗣𝗔) :=
  conditional A B h

end Diagonal
end CategoricalEssentialIncompleteness.V46.AdmissibilityAndComplementChecks
