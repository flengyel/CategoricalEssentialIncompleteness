/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateCoordinates

/-! # Actual state projections respect the native payload coordinates -/

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
variable (P V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

def stateOriginalFamily : (formula : Bool) →
    constantFamily P (computationState T V σ π d formula) ⟶
      constantFamily P (syntaxCarrier V σ π d formula : PredicateCategory T)
  | false => (constantFamilyFunctor P).map prod.fst
  | true => (constantFamilyFunctor P).map prod.fst

def stateTermResultFamily : constantFamily P (computationState T V σ π d false) ⟶
    constantFamily P (syntaxCarrier V σ π d false : PredicateCategory T) :=
  (constantFamilyFunctor P).map prod.snd

def stateFormulaResultCodeFamily : constantFamily P (computationState T V σ π d true) ⟶
    constantFamily P (RawOption T (syntaxCarrier V σ π d true)) :=
  (constantFamilyFunctor P).map
    (prod.snd ≫ (optionIso T (syntaxCarrier V σ π d true)).inv)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem model_stateTermResultCode (q : Obj T M (P ⨯ computationState T V σ π d false)) :
    ((F T M).map (stateResultCodeArrow T P V σ π d false) q).val =
      ((F T M).map (prod.snd : computationState T V σ π d false ⟶ _)
        ((F T M).map prod.snd q)).val := by
  change ((F T M).map (prod.snd ≫ prod.snd) q).val = _
  erw [Functor.map_comp_apply]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem model_stateFormulaResultCode (q : Obj T M (P ⨯ computationState T V σ π d true)) :
    ((F T M).map (stateResultCodeArrow T P V σ π d true) q).val =
      optionCode T M (syntaxCarrier V σ π d true)
        ((F T M).map (prod.snd : computationState T V σ π d true ⟶ _)
          ((F T M).map prod.snd q)) := by
  change ((F T M).map (prod.snd ≫ prod.snd ≫
    (optionIso T (syntaxCarrier V σ π d true)).inv) q).val = _
  erw [Functor.map_comp_apply,Functor.map_comp_apply]
  rfl

theorem stateLeaf_formula_optionCode (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d true))
    (hz : (stateLeaf T P V σ π d true).val.Evalb ![p.val,u,z.val]) :
    optionCode T M (syntaxCarrier V σ π d true)
      ((F T M).map (prod.snd : computationState T V σ π d true ⟶ _)
        ((F T M).map prod.snd z)) = ConcreteNamedSubstitution.result u := by
  have hr := ((stateLeaf_model T P V σ π d M true p u z).mp hz).2.2.2.1
  change ((F T M).map (prod.snd ≫ prod.snd ≫
    (optionIso T (syntaxCarrier V σ π d true)).inv) z).val = _ at hr
  rw [Functor.map_comp_apply,Functor.map_comp_apply] at hr
  exact hr

theorem stateLeaf_formula_original (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d true))
    (hz : (stateLeaf T P V σ π d true).val.Evalb ![p.val,u,z.val]) :
    ((F T M).map (prod.fst : computationState T V σ π d true ⟶ _)
      ((F T M).map prod.snd z)).val = ConcreteNamedSubstitution.original u := by
  have ho := ((stateLeaf_model T P V σ π d M true p u z).mp hz).2.2.1
  change ((F T M).map (prod.snd ≫ prod.fst) z).val = _ at ho
  rw [Functor.map_comp_apply] at ho
  exact ho

theorem stateLeaf_formula_occurrences (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d true))
    (hz : (stateLeaf T P V σ π d true).val.Evalb ![p.val,u,z.val]) :
    ConcreteNamedSubstitution.freeVariables V σ π d
      ((F T M).map (prod.fst : computationState T V σ π d true ⟶ _)
        ((F T M).map prod.snd z)).val = ConcreteNamedSubstitution.occurrences u := by
  have hv := ((stateLeaf_model T P V σ π d M true p u z).mp hz).2.2.2.2
  exact (congrArg (ConcreteNamedSubstitution.freeVariables V σ π d)
    (stateLeaf_formula_original T P V σ π d M p u z hz)).trans hv.symm

theorem stateOriginalFamily_coordinates (formula : Bool) (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d formula))
    (hz : (stateLeaf T P V σ π d formula).val.Evalb ![p.val,u,z.val]) :
    (constantLeaf T P (syntaxCarrier V σ π d formula)).val.Evalb
      ![p.val,ConcreteNamedSubstitution.original u,
        ((F T M).map (stateOriginalFamily T P V σ π d formula).left z).val] := by
  have hs := (stateLeaf_model T P V σ π d M formula p u z).mp hz
  apply (constantLeaf_model T M P (syntaxCarrier V σ π d formula) p _ _).mpr
  refine ⟨(over_value T M (stateOriginalFamily T P V σ π d formula) z).trans hs.2.1,?_⟩
  have ho := hs.2.2.1
  cases formula
  · have hv := model_map_snd T M (𝟙 P)
      (prod.fst : computationState T V σ π d false ⟶ syntaxCarrier V σ π d false) z
    change ((F T M).map (prod.snd ≫ prod.fst) z).val = _ at ho
    rw [Functor.map_comp_apply] at ho
    exact (congrArg Subtype.val hv).trans ho
  · have hv := model_map_snd T M (𝟙 P)
      (prod.fst : computationState T V σ π d true ⟶ syntaxCarrier V σ π d true) z
    change ((F T M).map (prod.snd ≫ prod.fst) z).val = _ at ho
    rw [Functor.map_comp_apply] at ho
    exact (congrArg Subtype.val hv).trans ho

theorem stateTermResultFamily_coordinates (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d false))
    (hz : (stateLeaf T P V σ π d false).val.Evalb ![p.val,u,z.val]) :
    (constantLeaf T P (syntaxCarrier V σ π d false)).val.Evalb
      ![p.val,ConcreteNamedSubstitution.result u,
        ((F T M).map (stateTermResultFamily T P V σ π d).left z).val] := by
  have hs := (stateLeaf_model T P V σ π d M false p u z).mp hz
  apply (constantLeaf_model T M P (syntaxCarrier V σ π d false) p _ _).mpr
  refine ⟨(over_value T M (stateTermResultFamily T P V σ π d) z).trans hs.2.1,?_⟩
  have hr := hs.2.2.2.1
  have hv := model_map_snd T M (𝟙 P)
    (prod.snd : computationState T V σ π d false ⟶ syntaxCarrier V σ π d false) z
  change ((F T M).map (prod.snd ≫ prod.snd) z).val = _ at hr
  rw [Functor.map_comp_apply] at hr
  exact (congrArg Subtype.val hv).trans hr

theorem stateFormulaResultCodeFamily_coordinates (p : Obj T M P) (u : M)
    (z : Obj T M (P ⨯ computationState T V σ π d true))
    (hz : (stateLeaf T P V σ π d true).val.Evalb ![p.val,u,z.val]) :
    (constantLeaf T P (RawOption T (syntaxCarrier V σ π d true))).val.Evalb
      ![p.val,ConcreteNamedSubstitution.result u,
        ((F T M).map (stateFormulaResultCodeFamily T P V σ π d).left z).val] := by
  have hs := (stateLeaf_model T P V σ π d M true p u z).mp hz
  apply (constantLeaf_model T M P (RawOption T (syntaxCarrier V σ π d true)) p _ _).mpr
  refine ⟨(over_value T M (stateFormulaResultCodeFamily T P V σ π d) z).trans hs.2.1,?_⟩
  have hr := hs.2.2.2.1
  have hv := model_map_snd T M (𝟙 P)
    (prod.snd ≫ (optionIso T (syntaxCarrier V σ π d true)).inv) z
  change ((F T M).map (prod.snd ≫ prod.snd ≫
    (optionIso T (syntaxCarrier V σ π d true)).inv) z).val = _ at hr
  rw [Functor.map_comp_apply] at hr
  exact (congrArg Subtype.val hv).trans hr

theorem stateOriginal_polynomialCoordinates (p : Obj T M P)
    (a : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P (computationState T V σ π d false),
        constantFamily P (computationState T V σ π d true))).left)
    (hz : (representation T P
      (constantFamily P (computationState T V σ π d false),constantFamily P (computationState T V σ π d true))
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) a).val.Evalb ![p.val,u,z.val]) :
    (constantRepresentation T P (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true) a).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.original
        ConcreteNamedSubstitution.original a u,
        ((F T M).map ((a.withParameters P).eval.map
          ((stateOriginalFamily T P V σ π d false,stateOriginalFamily T P V σ π d true) :
          (constantFamily P (computationState T V σ π d false),
            constantFamily P (computationState T V σ π d true)) ⟶ (constantFamily P (syntaxCarrier V σ π d false : PredicateCategory T),
            constantFamily P (syntaxCarrier V σ π d true : PredicateCategory T)))).left z).val] := by
  apply representation_relation_map T M
    (stateOriginalFamily T P V σ π d false) (stateOriginalFamily T P V σ π d true)
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
    (constantLeaf T P (syntaxCarrier V σ π d false)) (constantLeaf T P (syntaxCarrier V σ π d true))
    p ConcreteNamedSubstitution.original ConcreteNamedSubstitution.original
    (fun v w hw => stateOriginalFamily_coordinates T P V σ π d M false p v w hw)
    (fun v w hw => stateOriginalFamily_coordinates T P V σ π d M true p v w hw) a u z hz

/-- Only the term result is selected on formula-free constructor
polynomials. The second map is the actual original projection; its
numeric function will be eliminated by the proved term-only AST law. -/
theorem stateResults_polynomialCoordinates (p : Obj T M P)
    (a : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P (computationState T V σ π d false),
        constantFamily P (computationState T V σ π d true))).left)
    (hz : (representation T P
      (constantFamily P (computationState T V σ π d false),constantFamily P (computationState T V σ π d true))
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) a).val.Evalb ![p.val,u,z.val]) :
    (constantRepresentation T P (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true) a).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
        ConcreteNamedSubstitution.original a u,
        ((F T M).map ((a.withParameters P).eval.map
          ((stateTermResultFamily T P V σ π d,stateOriginalFamily T P V σ π d true) :
          (constantFamily P (computationState T V σ π d false),
            constantFamily P (computationState T V σ π d true)) ⟶ (constantFamily P (syntaxCarrier V σ π d false : PredicateCategory T),
            constantFamily P (syntaxCarrier V σ π d true : PredicateCategory T)))).left z).val] := by
  apply representation_relation_map T M
    (stateTermResultFamily T P V σ π d) (stateOriginalFamily T P V σ π d true)
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
    (constantLeaf T P (syntaxCarrier V σ π d false)) (constantLeaf T P (syntaxCarrier V σ π d true))
    p ConcreteNamedSubstitution.result ConcreteNamedSubstitution.original
    (fun v w hw => stateTermResultFamily_coordinates T P V σ π d M p v w hw)
    (fun v w hw => stateOriginalFamily_coordinates T P V σ π d M true p v w hw) a u z hz

/-- For polynomials with formula children, read formula results through
the actual option chart. This includes failure values without choosing
or inventing a successful formula point. -/
theorem stateResultsCode_polynomialCoordinates (p : Obj T M P)
    (a : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P (computationState T V σ π d false),
        constantFamily P (computationState T V σ π d true))).left)
    (hz : (representation T P
      (constantFamily P (computationState T V σ π d false),constantFamily P (computationState T V σ π d true))
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) a).val.Evalb ![p.val,u,z.val]) :
    (constantRepresentation T P (syntaxCarrier V σ π d false)
      (RawOption T (syntaxCarrier V σ π d true)) a).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
        ConcreteNamedSubstitution.result a u,
        ((F T M).map ((a.withParameters P).eval.map
          ((stateTermResultFamily T P V σ π d,stateFormulaResultCodeFamily T P V σ π d) :
          (constantFamily P (computationState T V σ π d false),
            constantFamily P (computationState T V σ π d true)) ⟶ (constantFamily P (syntaxCarrier V σ π d false : PredicateCategory T),
            constantFamily P (RawOption T (syntaxCarrier V σ π d true))))).left z).val] := by
  apply representation_relation_map T M
    (stateTermResultFamily T P V σ π d) (stateFormulaResultCodeFamily T P V σ π d)
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
    (constantLeaf T P (syntaxCarrier V σ π d false))
    (constantLeaf T P (RawOption T (syntaxCarrier V σ π d true)))
    p ConcreteNamedSubstitution.result ConcreteNamedSubstitution.result
    (fun v w hw => stateTermResultFamily_coordinates T P V σ π d M p v w hw)
    (fun v w hw => stateFormulaResultCodeFamily_coordinates T P V σ π d M p v w hw) a u z hz

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
