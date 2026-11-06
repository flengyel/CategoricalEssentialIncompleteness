import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithmTyped

/-! Closed numerical terms are free for substitution in every typed
formula. The positive stack carrier carries the independently computed
free-for flag; it does not redefine admissibility as success. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticClosedSubstitution
open ConcreteNamedSubstitution

variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

def goodFormulaPayload : Carrier :=
  let F := formulaPayloadCarrier V σ π d
  .mkSigma “value. !F.val value ∧ !freeForGraph.val 1 value”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedArithmeticClosedSubstitutionModelDecidableEq : DecidableEq M := Classical.decEq M
local notation "A" => SyntaxPolynomial.termExpression V σ d
local notation "B" => SyntaxPolynomial.formulaExpression V π d
local notation "Tm" => Postfix.carrier false A B
local notation "Fm" => Postfix.carrier true A B
local notation "TP" => termPayloadCarrier V σ π d
local notation "FP" => formulaPayloadCarrier V σ π d
local notation "GP" => goodFormulaPayload V σ π d

@[simp] theorem goodFormulaPayload_eval (value : M) :
    (GP).val.Evalb ![value] ↔ (FP).val.Evalb ![value] ∧ freeFor value = 1 := by
  simp [goodFormulaPayload,eq_comm]

private theorem rawCarrier_weaken (X Y Z : Carrier)
    (h : ∀ u : M,Y.val.Evalb ![u] → Z.val.Evalb ![u])
    (q : RawPolynomial) (u : M) (hu : (rawCarrier X Y q).val.Evalb ![u]) :
    (rawCarrier X Z q).val.Evalb ![u] := by
  induction q generalizing u with
  | term => exact hu
  | formula => exact h u hu
  | coefficient C => exact hu
  | unit => exact hu
  | product a b ia ib =>
    obtain ⟨x,y,rfl,hx,hy⟩ := (rawCarrier_product_eval X Y a b u).mp hu
    exact (rawCarrier_product_eval X Z a b _).mpr ⟨x,y,rfl,ia x hx,ib y hy⟩
  | sum a b ia ib =>
    rcases (rawCarrier_sum_eval X Y a b u).mp hu with ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
    · exact (rawCarrier_sum_eval X Z a b _).mpr (Or.inl ⟨x,rfl,ia x hx⟩)
    · exact (rawCarrier_sum_eval X Z a b _).mpr (Or.inr ⟨y,rfl,ib y hy⟩)

private theorem allFlags_one (q : RawPolynomial) (u : M)
    (hu : (rawCarrier TP GP q).val.Evalb ![u]) :
    allChildren (fun _ => 1) freeFor q u = 1 := by
  induction q generalizing u with
  | term => rfl
  | formula => exact ((goodFormulaPayload_eval V σ π d u).mp hu).2
  | coefficient C => rfl
  | unit => rfl
  | product a b ia ib =>
    obtain ⟨x,y,rfl,hx,hy⟩ := (rawCarrier_product_eval TP GP a b u).mp hu
    simp [allChildren,ia x hx,ib y hy]
  | sum a b ia ib =>
    rcases (rawCarrier_sum_eval TP GP a b u).mp hu with ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
    · simpa [allChildren] using ia x hx
    · simpa [allChildren] using ib y hy

private theorem quantifierBody_good (u : M)
    (hu : (rawCarrier TP GP B).val.Evalb ![u]) (htag : π₂ u ≠ 0) :
    (GP).val.Evalb ![π₂ (π₁ u)] := by
  rcases (rawCarrier_sum_eval TP GP (formulaLeft π d)
      (.product (.coefficient V) .formula) u).mp hu with ⟨v,rfl,hv⟩ | ⟨v,rfl,hv⟩
  · simp at htag
  · obtain ⟨y,body,rfl,_,hb⟩ :=
      (rawCarrier_product_eval TP GP (.coefficient V) .formula v).mp hv
    simpa [rawCarrier] using hb

private theorem formulaRoot_flag (param u : M) :
    freeFor (formulaRoot V π d param u) =
      if π₂ u = 0 then
        if allChildren (fun _ => 1) freeFor B u = 1 then 1 else 0
      else if π₁ (π₁ u) = π₁ param then 1
      else if capture param u = 1 ∧ freeFor (π₂ (π₁ u)) = 1 then 1 else 0 := by
  simp only [formulaRoot,freeFor_payload]

private theorem formulaRoot_good (param u : M)
    (hclosed : π₂ (π₂ param) = 0) (hu : (rawCarrier TP GP B).val.Evalb ![u]) :
    (GP).val.Evalb ![formulaRoot V π d param u] := by
  have hw := rawCarrier_weaken TP GP FP
    (fun v hv => ((goodFormulaPayload_eval V σ π d v).mp hv).1) B u hu
  have ht := formulaRoot_carrier V σ π d param u hw
  have hall := allFlags_one V σ π d B u hu
  have hc : capture param u = 1 := by simp [capture,hclosed]
  apply (goodFormulaPayload_eval V σ π d _).mpr
  refine ⟨ht,?_⟩
  rw [formulaRoot_flag]
  by_cases htag : π₂ u = 0
  · simp [htag,hall]
  · have hb := ((goodFormulaPayload_eval V σ π d _).mp
      (quantifierBody_good V σ π d u hu htag)).2
    by_cases hname : π₁ (π₁ u) = π₁ param <;> simp [htag,hname,hc,hb]

/-- The traversal invariant is a closed Sigma-one payload carrier. Its
run proof is the existing internal PA induction on every prefix length. -/
theorem substitutionFreeFor_closed (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement])
    (hclosed : freeVariables V σ π d replacement = 0)
    (hw : (Fm).val.Evalb ![word]) :
    substitutionFreeFor V σ π d x replacement word = 1 := by
  let param := ⟪x,⟪replacement,freeVariables V σ π d replacement⟫⟫
  have hp : (Tm).val.Evalb ![π₁ (π₂ param)] := by simpa [param] using hrep
  have hc : π₂ (π₂ param) = 0 := by simpa [param] using hclosed
  have ht : ∀ u : M,(rawCarrier TP GP A).val.Evalb ![u] →
      (TP).val.Evalb ![termRoot V σ d param u] := by
    intro u hu
    exact termRoot_carrier V σ π d param u hp
      (rawCarrier_weaken TP GP FP
        (fun v hv => ((goodFormulaPayload_eval V σ π d v).mp hv).1) A u hu)
  have hg : (GP).val.Evalb ![substitutionPayload V σ π d x replacement word] :=
    Traversal.output_typed A B (termRootGraph V σ d) (formulaRootGraph V π d)
      (termRoot V σ d) (formulaRoot V π d) param TP GP ht
      (fun u hu => formulaRoot_good V σ π d param u hc hu) true word hw
  exact ((goodFormulaPayload_eval V σ π d _).mp hg).2

theorem substitutionResult_closed (x replacement word : M)
    (hrep : (Tm).val.Evalb ![replacement])
    (hclosed : freeVariables V σ π d replacement = 0)
    (hw : (Fm).val.Evalb ![word]) :
    ∃ out : M,(Fm).val.Evalb ![out] ∧ substitutionResult V σ π d x replacement word = ok out := by
  have hf := substitutionFreeFor_closed V σ π d x replacement word hrep hclosed hw
  have hs := (substitutionFreeFor_iff_success V σ π d x replacement word hrep hw).mp hf
  rcases substitutionResult_formula V σ π d x replacement word hrep hw with hz | hgood
  · simp [hz,pi₂_zero] at hs
  · exact hgood

end Models
end CategoricalEssentialIncompleteness.V46.NamedArithmeticClosedSubstitution
