/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonFunctionStep
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonVariableStep
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationPoints
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonTermRootArithmetic

/-! # The actual full term-substitution structure map has the numeric root result -/

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
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "A" => SyntaxPolynomial.termExpression V σ d
local notation "C" => SyntaxPolynomial.constructors σ d

theorem termSubstitution_structure_result_value (p : Obj T M P) (u : M)
    (q : Obj T M (((A).withParameters P).eval.obj (S).substitutionAlgebra.a).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) A).val.Evalb ![p.val,u,q.val]) :
    ((F T M).map (stateResultCodeArrow T P V σ π d false)
      ((F T M).map (S).substitutionAlgebra.str.1.left q)).val =
      ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.termRoot V σ d
        (Arithmetic.pair ((F T M).map (prod.fst : P ⟶ V) p).val
          (Arithmetic.pair ((F T M).map (prod.snd : P ⟶ _) p).val
            (ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map (prod.snd : P ⟶ _) p).val))) u) := by
  let L := ((SyntaxPolynomial.coefficient V).withParameters P).eval.obj (S).substitutionAlgebra.a
  let R := ((C).withParameters P).eval.obj (S).substitutionAlgebra.a
  rcases relation_sum_points T M P (S).substitutionAlgebra.a
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
    (.coefficient V) C p.val u q hq with
      ⟨name,z,hu,hz,hι⟩ | ⟨v,z,hu,hz,hι⟩
  · have hc : (constantLeaf T P V).val.Evalb ![p.val,name,z.val] := hz
    have hs := (constantLeaf_model T M P V p name z).mp hc
    have hstr : (coprod.inl : L ⟶ L ⨿ R) ≫ (S).substitutionAlgebra.str.1 =
        parameterHom (S).variableSubstitutionPair := by
      simp only [CategoricalSyntax.substitutionAlgebra,coprod.inl_desc]
    have hout : (F T M).map (S).substitutionAlgebra.str.1.left q =
        (F T M).map (parameterHom (S).variableSubstitutionPair).left z := by
      erw [← hι,← Functor.map_comp_apply,← Over.comp_left,hstr]
      all_goals rfl
    rw [hout]
    let : DecidableEq M := namedComparisonVariableStepModelDecidableEq M
    let outcome := fun x replacement name : M => if name = x then replacement else
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d) (Arithmetic.pair name 0)
    let xp := ((F T M).map (prod.fst : P ⟶ V) p).val
    let tp := ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) p).val
    let xz := ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.fst z)).val
    let tz := ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) ((F T M).map prod.fst z)).val
    let nz := ((F T M).map (prod.snd : P ⨯ V ⟶ V) z).val
    have hp := parameterHom_point_value T M (S).variableSubstitutionPair z
    have hcode := model_stateTermResultCode T P V σ π d M
      ((F T M).map (parameterHom (S).variableSubstitutionPair).left z)
    have hpoint := congrArg (fun value =>
      ((F T M).map (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ _) value).val) hp
    have hvar : ((F T M).map (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ _)
        ((F T M).map (S).variableSubstitutionPair z)).val = outcome xz tz nz :=
      variableSubstitutionPair_result_value T V σ π d M z
    have hx : xz = xp := congrArg (fun pp => ((F T M).map (prod.fst : P ⟶ V) pp).val) hs.1
    have ht : tz = tp := congrArg (fun pp => ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) pp).val) hs.1
    have hinputs : (xz,(tz,nz)) = (xp,(tp,name)) := Prod.ext hx (Prod.ext ht hs.2)
    have hscalar := congrArg (fun args : M × M × M => outcome args.1 args.2.1 args.2.2) hinputs
    have hroot : outcome xp tp name = ConcreteNamedSubstitution.result
        (ConcreteNamedSubstitution.termRoot V σ d
          (Arithmetic.pair xp (Arithmetic.pair tp (ConcreteNamedSubstitution.freeVariables V σ π d tp)))
          (Arithmetic.pair name 0)) :=
      (termRoot_variable_result V σ d xp tp (ConcreteNamedSubstitution.freeVariables V σ π d tp) name).symm
    exact hcode.trans (hpoint.trans (hvar.trans (hscalar.trans (hroot.trans
      (congrArg (fun word => ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.termRoot V σ d
        (Arithmetic.pair xp (Arithmetic.pair tp (ConcreteNamedSubstitution.freeVariables V σ π d tp))) word)) hu.symm)))))

  · have hstr : (coprod.inr : R ⟶ L ⨿ R) ≫ (S).substitutionAlgebra.str.1 =
        SyntaxPolynomial.parameterComparison P (S).substitutionCarriers C ≫
          (constantFamilyFunctor P).map (S).functionSubstitutionPair := by
      simp only [CategoricalSyntax.substitutionAlgebra,coprod.inr_desc]
    have hout : (F T M).map (S).substitutionAlgebra.str.1.left q =
        (F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers C ≫
          (constantFamilyFunctor P).map (S).functionSubstitutionPair).left z := by
      erw [← hι,← Functor.map_comp_apply,← Over.comp_left,hstr]
      all_goals rfl
    rw [hout]
    have hcode := model_stateTermResultCode T P V σ π d M
      ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers C ≫
        (constantFamilyFunctor P).map (S).functionSubstitutionPair).left z)
    have hfun := functionSubstitutionPair_result_value T V σ π d M p v z hz
    let xp := ((F T M).map (prod.fst : P ⟶ V) p).val
    let tp := ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) p).val
    have hroot := (termRoot_function_result V σ d xp tp
      (ConcreteNamedSubstitution.freeVariables V σ π d tp) v).symm
    exact hcode.trans (hfun.trans (hroot.trans
      (congrArg (fun word => ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.termRoot V σ d
        (Arithmetic.pair xp (Arithmetic.pair tp (ConcreteNamedSubstitution.freeVariables V σ π d tp))) word)) hu.symm)))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
