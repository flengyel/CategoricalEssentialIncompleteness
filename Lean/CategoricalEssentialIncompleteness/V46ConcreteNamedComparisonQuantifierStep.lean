/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonQuantifierValues
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateProjections
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationPoints

/-! # The actual shared-parameter quantifier step has the numeric root result -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
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
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)
local notation "Q₀" => SyntaxPolynomial.product (SyntaxPolynomial.coefficient V)
  (SyntaxPolynomial.formula : SyntaxPolynomial (PredicateCategory T))

theorem quantifierSubstitutionPair_result_code (p : Obj T M P) (u : M)
    (q : Obj T M (((Q₀).withParameters P).eval.obj (S).substitutionAlgebra.a).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) Q₀).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers Q₀ ≫
          parameterHom (S).quantifierSubstitutionPair).left q))) =
      ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d
        (Arithmetic.pair ((F T M).map (prod.fst : P ⟶ V) p).val
          (Arithmetic.pair ((F T M).map (prod.snd : P ⟶ _) p).val
            (ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map (prod.snd : P ⟶ _) p).val)))
        (quantifierInput u)) := by
  let C := constantFamily P V
  let D := constantFamily P (S).substitutionCarriers.2
  let qn := (F T M).map (prod.fst : C ⨯ D ⟶ C).left q
  let qb := (F T M).map (prod.snd : C ⨯ D ⟶ D).left q
  obtain ⟨name,body,hu,hn,hb⟩ := relation_product_points T M P (S).substitutionAlgebra.a
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) (.coefficient V) .formula p.val u q hq
  have hname : (constantLeaf T P V).val.Evalb ![p.val,name,qn.val] := hn
  have hcoef := (constantLeaf_model T M P V p name qn).mp hname
  have hparam : (F T M).map (((Q₀).withParameters P).eval.obj (S).substitutionAlgebra.a).hom q = p :=
    (over_value T M (prod.fst : C ⨯ D ⟶ C) q).symm.trans hcoef.1
  let w := (F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers Q₀).left q
  let base := (F T M).map (parameterValueMap T P (S).substitutionCarriers.1 (S).substitutionCarriers.2 Q₀) q
  have hwp := (parameterComparison_point_parameter T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 Q₀ q).trans hparam
  have hwv := parameterComparison_point_value T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 Q₀ q
  have hbn := (parameterPoint_product_fst T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 (.coefficient V) .formula q).trans
      (parameterPoint_coefficient T M P (S).substitutionCarriers.1 (S).substitutionCarriers.2 V qn)
  have hbb := (parameterPoint_product_snd T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 (.coefficient V) .formula q).trans
      (parameterPoint_formula T M P (S).substitutionCarriers.1 (S).substitutionCarriers.2 qb)
  have hx : ((F T M).map (prod.fst ≫ prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ V) w).val =
      ((F T M).map (prod.fst : P ⟶ V) p).val := by
    rw [Functor.map_comp_apply]
    exact congrArg (fun z => ((F T M).map (prod.fst : P ⟶ V) z).val) hwp
  have ht : ((F T M).map (prod.fst ≫ prod.snd : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ (S).algebra.a.1) w).val =
      ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) p).val := by
    rw [Functor.map_comp_apply]
    exact congrArg (fun z => ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) z).val) hwp
  have hy : ((F T M).map (prod.snd ≫ prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ V) w).val = name := by
    rw [Functor.map_comp_apply]
    exact (congrArg Subtype.val ((congrArg ((F T M).map (prod.fst : V ⨯ (S).substitutionCarriers.2 ⟶ V)) hwv).trans hbn)).trans hcoef.2
  have hbody := (congrArg ((F T M).map (prod.snd : V ⨯ (S).substitutionCarriers.2 ⟶ _)) hwv).trans hbb
  have hold : ((F T M).map (prod.snd ≫ prod.snd ≫ prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ Y) w).val =
      ConcreteNamedSubstitution.original body := by
    rw [Functor.map_comp_apply,Functor.map_comp_apply]
    exact (congrArg (fun z => ((F T M).map (prod.fst : (S).substitutionCarriers.2 ⟶ Y) z).val) hbody).trans
      (stateLeaf_formula_original T P V σ π d M p body qb hb)
  have hcode : optionCode T M Y ((F T M).map
      (prod.snd ≫ prod.snd ≫ prod.snd : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ OptionSyntax.obj Y) w) =
      ConcreteNamedSubstitution.result body := by
    rw [Functor.map_comp_apply,Functor.map_comp_apply]
    exact (congrArg (fun z => optionCode T M Y ((F T M).map
      (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) z)) hbody).trans
      (stateLeaf_formula_optionCode T P V σ π d M p body qb hb)
  have hmeta := ((stateLeaf_model T P V σ π d M true p body qb).mp hb).2.2.2.2
  have hp := model_lift_snd T M
    (prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ P) (S).quantifierSubstitutionPair w
  have hs := model_lift_snd T M (S).quantifierOriginal (S).quantifierSubstitutionResult w
  have hpoint : (F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers Q₀ ≫
          parameterHom (S).quantifierSubstitutionPair).left q)) =
      (F T M).map (S).quantifierSubstitutionResult w := by
    change (F T M).map prod.snd ((F T M).map prod.snd
      ((F T M).map ((SyntaxPolynomial.parameterComparison P (S).substitutionCarriers Q₀).left ≫
        (parameterHom (S).quantifierSubstitutionPair).left) q)) = _
    rw [Functor.map_comp_apply]
    exact (congrArg ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)) hp).trans hs
  have hm := quantifierSubstitutionResult_coordinate_value T V σ π d M w
  have hinputs :
      (((F T M).map (prod.fst ≫ prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ V) w).val,
        (((F T M).map (prod.snd ≫ prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ V) w).val,
          (((F T M).map (prod.snd ≫ prod.snd ≫ prod.fst : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ Y) w).val,
            (((F T M).map (prod.fst ≫ prod.snd : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ (S).algebra.a.1) w).val,
              optionCode T M Y ((F T M).map
                (prod.snd ≫ prod.snd ≫ prod.snd : P ⨯ (V ⨯ (S).substitutionCarriers.2) ⟶ OptionSyntax.obj Y) w))))) =
      (((F T M).map (prod.fst : P ⟶ V) p).val,
        (name,(ConcreteNamedSubstitution.original body,
          (((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) p).val,
            ConcreteNamedSubstitution.result body)))) :=
    Prod.ext hx (Prod.ext hy (Prod.ext hold (Prod.ext ht hcode)))
  have hscalar := congrArg (fun values : M × M × M × M × M =>
    quantifierResultValue V σ π d values.1 values.2.1 values.2.2.1 values.2.2.2.1 values.2.2.2.2) hinputs
  have hroot := quantifierResultValue_payload V σ π d
    ((F T M).map (prod.fst : P ⟶ V) p).val
    ((F T M).map (prod.snd : P ⟶ (S).algebra.a.1) p).val name body hmeta
  exact (congrArg (optionCode T M Y) hpoint).trans (hm.trans (hscalar.trans (hroot.trans
    (congrArg (fun input => ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d
      (Arithmetic.pair ((F T M).map (prod.fst : P ⟶ V) p).val
        (Arithmetic.pair ((F T M).map (prod.snd : P ⟶ _) p).val
          (ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map (prod.snd : P ⟶ _) p).val))) input))
      (congrArg quantifierInput hu.symm)))))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
