import CategoricalEssentialIncompleteness.V46NumericalArithmeticRuleComparison
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleComparison.Checks
open Coordinates
example (Γ : Carrier) (i : Fin 3) :
    (sourceRules Γ).instances i ≅ (targetRules Γ).instances i := labelIso Γ i
example (Γ : Carrier) (i : Fin 3) :
    (forward Γ).map i ≫ (targetRules Γ).premises i = (sourceRules Γ).premises i := (forward Γ).premises i
example (Γ : Carrier) (i : Fin 3) :
    (forward Γ).map i ≫ (targetRules Γ).conclusion i = (sourceRules Γ).conclusion i := (forward Γ).conclusion i
example (Γ : Carrier) (i : Fin 3) :
    (backward Γ).map i ≫ (sourceRules Γ).premises i = (targetRules Γ).premises i := (backward Γ).premises i
example (Γ : Carrier) :
    NumericalDerivation.codeObject (Rules.rules Γ) ≅ NumericalDerivation.codeObject (targetRules Γ) := proofIso Γ
example (Γ : Carrier) :
    (proofIso Γ).hom ≫ NumericalDerivation.codeConclusion (targetRules Γ) =
      NumericalDerivation.codeConclusion (Rules.rules Γ) ≫ formulaIso.hom := proof_conclusion Γ
example (Γ : Carrier) (i : Fin 3) :
    (backward Γ).map i ≫ (sourceRules Γ).conclusion i = (targetRules Γ).conclusion i :=
  (backward Γ).conclusion i
example (Γ : Carrier) (i : Fin 3) :
    (forward Γ).map i ≫ (backward Γ).map i = 𝟙 ((sourceRules Γ).instances i) := forward_backward Γ i
example (Γ : Carrier) (i : Fin 3) :
    (backward Γ).map i ≫ (forward Γ).map i = 𝟙 ((targetRules Γ).instances i) := backward_forward Γ i
example (Γ : Carrier) (i : Fin 3) : Partrec (labelForward Γ i) := labelForward_partrec Γ i
example (Γ : Carrier) (i : Fin 3) : Partrec (labelBackward Γ i) := labelBackward_partrec Γ i
example (Γ : Carrier) (i : Fin 3) (n k : ℕ) :
    k ∈ labelForward Γ i n ↔ ∃ x : NumericalTuples.Point ((sourceRules Γ).instances i),
      NumericalTuples.code ((sourceRules Γ).instances i).dimension x.val = n ∧
        NumericalTuples.code ((targetRules Γ).instances i).dimension
          ((labelIso Γ i).hom.toFun x).val = k := labelForward_graph Γ i n k
example (Γ : Carrier) (i : Fin 3) (n k : ℕ) :
    k ∈ labelBackward Γ i n ↔ ∃ x : NumericalTuples.Point ((targetRules Γ).instances i),
      NumericalTuples.code ((targetRules Γ).instances i).dimension x.val = n ∧
        NumericalTuples.code ((sourceRules Γ).instances i).dimension
          ((labelIso Γ i).inv.toFun x).val = k := labelBackward_graph Γ i n k
example (Γ : Carrier) (i : Fin 3) (x : NumericalTuples.Point ((sourceRules Γ).instances i)) :
    (labelForward Γ i (NumericalTuples.code ((sourceRules Γ).instances i).dimension x.val)).bind
        (labelBackward Γ i) = Part.some (NumericalTuples.code ((sourceRules Γ).instances i).dimension x.val) :=
  labelForward_backward Γ i x
example (Γ : Carrier) (i : Fin 3) (x : NumericalTuples.Point ((targetRules Γ).instances i)) :
    (labelBackward Γ i (NumericalTuples.code ((targetRules Γ).instances i).dimension x.val)).bind
        (labelForward Γ i) = Part.some (NumericalTuples.code ((targetRules Γ).instances i).dimension x.val) :=
  labelBackward_forward Γ i x
example (Γ : Carrier) : (sourceRules Γ).inference ≅ (targetRules Γ).inference :=
  NumericalRuleRelabel.inferenceIso (forward Γ) (backward Γ) (forward_backward Γ) (backward_forward Γ)
example (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (labelIso Γ i).hom := input_label Γ i
example (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ finitePowerMap (proofIso Γ).hom i.val :=
  input_children Γ i
example (Γ : Carrier) :
    (proofIso Γ).inv ≫ NumericalDerivation.codeConclusion (Rules.rules Γ) ≫ formulaIso.hom =
      NumericalDerivation.codeConclusion (targetRules Γ) := inverse_proof_conclusion Γ
example (Γ : Carrier) :
    ∃ p : NumericalTuples.Tuple (NumericalDerivation.codeObject (Rules.rules Γ)).dimension →
        Part (NumericalTuples.Tuple (NumericalDerivation.codeObject (targetRules Γ)).dimension),
      Partrec p ∧ ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject (Rules.rules Γ)),
        p x.val = Part.some ((proofIso Γ).hom.toFun x).val := forward_program Γ
example (Γ : Carrier) :
    ∃ p : NumericalTuples.Tuple (NumericalDerivation.codeObject (targetRules Γ)).dimension →
        Part (NumericalTuples.Tuple (NumericalDerivation.codeObject (Rules.rules Γ)).dimension),
      Partrec p ∧ ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject (targetRules Γ)),
        p x.val = Part.some ((proofIso Γ).inv.toFun x).val := backward_program Γ
example (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ Sigma.ι ((targetRules Γ).ruleObject
        (NumericalDerivation.codeAlgebra (targetRules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (targetRules Γ)).str.left =
      Sigma.ι ((Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (Rules.rules Γ)).str.left ≫ (proofIso Γ).hom := branch_constructor Γ i
example (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (labelIso Γ i).inv :=
  inverse_input_label Γ i
example (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫ pullback.snd _ _ = pullback.snd _ _ ≫ finitePowerMap (proofIso Γ).inv i.val :=
  inverse_input_children Γ i
example (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ inputComparisonInverse Γ i = 𝟙 _ := input_forward_inverse Γ i
example (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫ inputComparison Γ i = 𝟙 _ := input_inverse_forward Γ i
example (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫
        Sigma.ι ((Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (Rules.rules Γ)).str.left =
      Sigma.ι ((targetRules Γ).ruleObject (NumericalDerivation.codeAlgebra (targetRules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (targetRules Γ)).str.left ≫ (proofIso Γ).inv := inverse_branch_constructor Γ i
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleComparison.Checks
