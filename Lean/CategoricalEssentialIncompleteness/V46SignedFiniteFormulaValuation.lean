/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanEquations
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBooleans
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints
public import CategoricalEssentialIncompleteness.V46SignedDerivationFiniteSupport

/-! # The formula valuation determined by an internal finite support -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SignedFiniteFormulaValuation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {V X : PredicateCategory T}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0)

/-- The support is an internal list; its length need not be standard. -/
def atomAssignment (X : PredicateCategory T) :
    constantFamily (listObject T X) X ⟶
      constantFamily (listObject T X) (Two (PredicateCategory T)) :=
  parameterHom ((prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
    ConcreteNamedComparison.membershipArrow T X)

abbrev atomInputs (X : PredicateCategory T) : PredicateCategory T :=
  Limits.prod (C := PredicateCategory T) (listObject T X) X

/-- One total morphism simultaneously evaluates formulas at every support. -/
def valuation :
    Limits.prod (C := PredicateCategory T) (listObject T X) S.algebra.a.2 ⟶
      Two (PredicateCategory T) :=
  ParameterizedBooleanValuation.value S (listObject T X) (atomAssignment T X)

@[reassoc] theorem atom_value :
    ((constantFamilyFunctor (listObject T X)).map
      (NullaryInterpretation.atomFormula S)).left ≫ valuation T S =
        (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
          ConcreteNamedComparison.membershipArrow T X := by
  have h := congrArg (fun k => k.left ≫ prod.snd)
    (ParameterizedBooleanValuation.atom_value S (listObject T X) (atomAssignment T X))
  simpa only [Over.comp_left, Category.assoc, ParameterizedBooleanValuation.value,
    atomAssignment, parameterHom_value, valuation] using h

@[reassoc] theorem negative_atom_value :
    ((constantFamilyFunctor (listObject T X)).map
      (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left ≫ valuation T S =
        Two.unary Bool.not
          ((prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
            ConcreteNamedComparison.membershipArrow T X) := by
  have h : (constantFamilyFunctor (listObject T X)).map
        (NullaryInterpretation.atomFormula S ≫ S.negationConstructor) ≫
        ParameterizedBooleanValuation.valuation S (listObject T X) (atomAssignment T X) =
      atomAssignment T X ≫ (constantFamilyFunctor (listObject T X)).map
        (Two.unary Bool.not (𝟙 (Two (PredicateCategory T)))) := by
    rw [Functor.map_comp, Category.assoc, ParameterizedBooleanValuation.negation_value,
      ← Category.assoc, ParameterizedBooleanValuation.atom_value]
  have hh := congrArg (fun k => k.left ≫ prod.snd) h
  rw [ParameterizedBooleanValuation.family_unary_value] at hh
  simpa only [Over.comp_left, Category.assoc, valuation,
    ParameterizedBooleanValuation.value,
    atomAssignment, parameterHom_value] using hh

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : DecidableEq M := Classical.decEq M

private theorem membership_point (q : Obj T M (atomInputs T X)) (b : Bool)
    (hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val =
        if b then 1 else 0) :
    (F T M).map ((prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
      ConcreteNamedComparison.membershipArrow T X) q =
        (F T M).map (Two.constant (atomInputs T X) b) q := by
  have hm := ConcreteNamedComparison.membershipArrow_point T M X
    ((F T M).map (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom q) b
  have hp : ConcreteNamedSubstitution.member
      ((F T M).map (prod.fst : X ⨯ listObject T X ⟶ X)
        ((F T M).map (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom q)).val
      ((F T M).map (prod.snd : X ⨯ listObject T X ⟶ listObject T X)
        ((F T M).map (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom q)).val =
        if b then 1 else 0 := by
    simpa only [← Functor.map_comp_apply, prod.braiding_hom, prod.lift_fst, prod.lift_snd] using hb
  rw [Functor.map_comp_apply]
  exact (hm hp).trans (ConcreteNamedComparison.model_constant_comp T M
    (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom q b)

/-- The atom computation holds in every PA model, including on nonstandard lists. -/
theorem atom_point (q : Obj T M (atomInputs T X)) (b : Bool)
    (hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val =
        if b then 1 else 0) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S)).left q) =
      (F T M).map (Two.constant (atomInputs T X) b) q := by
  have he := ConcreteNamedComparison.parameterPoint_diagram T M
    ((constantFamilyFunctor (listObject T X)).map (NullaryInterpretation.atomFormula S)).left
    (valuation T S)
    (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom
    (ConcreteNamedComparison.membershipArrow T X) (atom_value T S) q
  have hm := membership_point T q b hb
  rw [Functor.map_comp_apply] at hm
  exact he.trans hm

/-- Negation computes the complementary Boolean value at the same support. -/
theorem negative_point (q : Obj T M (atomInputs T X)) (b : Bool)
    (hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val =
        if b then 1 else 0) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left q) =
      (F T M).map (Two.constant (atomInputs T X) (!b)) q := by
  let f : atomInputs T X ⟶ Two (PredicateCategory T) :=
    (prod.braiding (C := PredicateCategory T) (listObject T X) X).hom ≫
      ConcreteNamedComparison.membershipArrow T X
  have he := ConcreteNamedComparison.parameterPoint_diagram T M
    ((constantFamilyFunctor (listObject T X)).map
      (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left
    (valuation T S) f (Two.unary Bool.not (𝟙 (Two (PredicateCategory T))))
    (by simpa only [Two.unary, Category.id_comp] using negative_atom_value T S) q
  have hm := ConcreteNamedComparison.model_unary T M Bool.not f q b
    (membership_point T q b hb)
  have hm' : (F T M).map (Two.unary Bool.not (𝟙 (Two (PredicateCategory T))))
      ((F T M).map f q) = (F T M).map (Two.constant (atomInputs T X) (!b)) q := by
    simpa only [Two.unary, Functor.map_comp_apply, Functor.map_id_apply] using hm
  exact he.trans hm'

/-- Membership in the support gives a true positive atom. -/
theorem positive_atom (q : Obj T M (atomInputs T X))
    (hq : MemVec
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S)).left q) =
      (F T M).map (Two.constant (atomInputs T X) true) q := by
  apply atom_point T S q true
  rw [SignedDerivation.member_eq_lookup]
  exact (ArithmeticFiniteLookup.lookup_one_iff _ _).mpr hq

/-- A label disjoint from every support entry gives a false atom. -/
theorem absent_atom (q : Obj T M (atomInputs T X))
    (hq : ¬ MemVec
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S)).left q) =
      (F T M).map (Two.constant (atomInputs T X) false) q := by
  apply atom_point T S q false
  rw [SignedDerivation.member_eq_lookup]
  exact (ArithmeticFiniteLookup.lookup_zero_iff _ _).mpr hq

/-- An absent label makes the corresponding negative axiom true. -/
theorem negative_axiom (q : Obj T M (atomInputs T X))
    (hq : ¬ MemVec
      ((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val
      ((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left q) =
      (F T M).map (Two.constant (atomInputs T X) true) q := by
  apply negative_point T S q false
  rw [SignedDerivation.member_eq_lookup]
  exact (ArithmeticFiniteLookup.lookup_zero_iff _ _).mpr hq

/-- PA's proved disjointness makes every diagonal negative axiom true on
an arbitrary internal alpha-support. -/
theorem diagonal_negative_axiom (q : Obj T M (atomInputs T X))
    (hs : (FiniteSigmaOne.allEntriesCondition ArithmeticDiagonalCodes.alpha).Evalb
      ![((F T M).map (prod.fst : atomInputs T X ⟶ listObject T X) q).val])
    (hn : ArithmeticDiagonalCodes.beta.val.Evalb
      ![((F T M).map (prod.snd : atomInputs T X ⟶ X) q).val]) :
    (F T M).map (valuation T S)
        ((F T M).map ((constantFamilyFunctor (listObject T X)).map
          (NullaryInterpretation.atomFormula S ≫ S.negationConstructor)).left q) =
      (F T M).map (Two.constant (atomInputs T X) true) q := by
  apply negative_axiom T S q
  exact (ArithmeticFiniteLookup.zero_iff _ _).mp
    (ArithmeticSignedFiniteSupport.negative_value _ hs _ hn)

end Models
end CategoricalEssentialIncompleteness.V46.SignedFiniteFormulaValuation
