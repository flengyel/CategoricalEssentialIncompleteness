/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainAdmissibleValues
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonFreeFor

/-! # The actual substitution-domain classifier realizes independent free-for -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "X" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)

/-- The categorical success classifier. Its agreement with the
independently defined numerical free-for recursion is proved below. -/
def plainFreeForClassifier : @Quiver.Hom (PredicateCategory T) inferInstance
    (Y ⨯ P) (Two (PredicateCategory T)) :=
  (S).formulaSubstitutionOption ≫ SyntaxOptionTransport.optionTag (C := PredicateCategory T) Y

/-- This is a genuine pullback of the true point by the actual
classifier; it precedes comparison with any numerical flag. -/
theorem plainFreeForClassifier_isPullback :
    IsPullback (S).admissibleInclusion (terminal.from (S).admissibleSubstitution)
      (plainFreeForClassifier T V σ π d)
      (Two.point (C := PredicateCategory T) true) :=
  SyntaxOptionTransport.optionTag_success_isPullback (C := PredicateCategory T)
    («X» := (Y ⨯ P)) («Y» := Y) (S).formulaSubstitutionOption

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The native flag is the separate primitive recursive loop field,
not a definition in terms of this categorical success classifier. -/
theorem plainFreeForClassifier_model_iff (q : Obj T M (Y ⨯ P)) :
    (F T M).map (plainFreeForClassifier T V σ π d) q =
      (F T M).map (Two.constant (C := PredicateCategory T) (Y ⨯ P) true) q ↔
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val = 1 :=
  (model_classifier_image_iff T M (S).admissibleInclusion
    (plainFreeForClassifier T V σ π d)
    (plainFreeForClassifier_isPullback T V σ π d) q).symm.trans
      (plain_admissible_model_iff T V σ π d M q)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
