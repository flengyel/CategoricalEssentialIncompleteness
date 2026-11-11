/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalUnderlying
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGraphsFunctor
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # The original recursive word data in the uniform carrier category

Only the ordinary source syntax data is embedded by this functor. Target
algebras and their folds have arbitrary uniformly represented operations;
no preservation of initiality by this inclusion is asserted.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable (P : Uniform.Family)

def ordinaryCarrier (X : EnumerableCarriers.Carrier) : Total.Carrier P :=
  ⟨X.support,Uniform.Enumerable.of_re X.enumerable⟩

def ordinaryMap {X Y : EnumerableCarriers.Total} (f : X ⟶ Y) :
    (⟨ordinaryCarrier P X.obj⟩ : Total.TotalCategory P) ⟶ ⟨ordinaryCarrier P Y.obj⟩ :=
  let k := Total.arrow (EnumerableCarriers.val f.hom)
    (Uniform.Represented.of_partrec (EnumerableCarriers.val_partrec f.hom))
    (EnumerableCarriers.val_source f.hom) (EnumerableCarriers.val_target f.hom)
  ⟨k,(Total.total_iff k).mpr ((EnumerableCarriers.total_iff f.hom).mp f.property)⟩

theorem ordinaryMap_value {X Y : EnumerableCarriers.Total} (f : X ⟶ Y) :
    Total.val (ordinaryMap P f).hom = EnumerableCarriers.val f.hom := rfl

def ordinaryFunctor : EnumerableCarriers.Total ⥤ Total.TotalCategory P where
  obj X := ⟨ordinaryCarrier P X.obj⟩
  map := ordinaryMap P
  map_id X := by
    apply WideSubcategory.hom_ext
    apply Total.val_injective
    funext x
    apply Part.ext
    intro y
    change y ∈ EnumerableCarriers.val (𝟙 X.obj) x ↔
      y ∈ Total.supportIdentity X.obj.support x
    rw [EnumerableCarriers.val_id]
    exact (CategoricalEssentialIncompleteness.mem_supportIdentity X.obj.support x y).trans
      (Total.mem_supportIdentity X.obj.support x y).symm
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply Total.val_injective
    rfl

def numericalFunctor : NumericalTuples.Object ⥤ Total.TotalCategory P :=
  NumericalTuples.comparison ⋙ ordinaryFunctor P

def predicateFunctor : PredicateCategory 𝗣𝗔 ⥤ Total.TotalCategory P :=
  NumericalArithmetic.numericalInterpretation ⋙ numericalFunctor P

def ordinaryComparison : ordinaryFunctor P ⋙ Total.underlying ≅ EnumerableCarriers.underlying :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact Part.mem_unique (Total.totalFunction_mem (ordinaryMap P f) x)
      (EnumerableCarriers.totalFunction_mem f x))

def numericalComparison : numericalFunctor P ⋙ Total.underlying ≅ NumericalUnderlying.functor :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft NumericalTuples.comparison (ordinaryComparison P) ≪≫
      NumericalUnderlying.comparison.symm

/-- A natural comparison of the actual underlying carrier functions.
It asserts no faithfulness of standard interpretation or initiality. -/
def standardComparison : predicateFunctor P ⋙ Total.underlying ≅
    PredicateInterpretation.functor 𝗣𝗔 ℕ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft NumericalArithmetic.numericalInterpretation (numericalComparison P) ≪≫
      NumericalArithmetic.Geometry.standardComparison

def predicateObject (C : SyntacticPredicates.Carrier) : Total.Carrier P :=
  ordinaryCarrier P (NumericalCoordinates.predicateCarrier (C : PredicateCategory 𝗧𝗔)).obj

theorem predicateObject_support (C : SyntacticPredicates.Carrier) :
    (predicateObject P C).support = {n : ℕ | C.val.Evalb (M := ℕ) ![n]} := rfl

theorem predicateFunctor_object (C : PredicateCategory 𝗣𝗔) :
    (predicateFunctor P).obj C = (⟨predicateObject P C⟩ : Total.TotalCategory P) := by
  change (ordinaryFunctor P).obj (NumericalTuples.codedObject
    (NumericalTuples.unary (NumericalCoordinates.predicateCarrier (C : PredicateCategory 𝗧𝗔)))) = _
  rw [NumericalTuples.codedObject_unary]
  rfl

theorem predicateFunctor_program {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D) :
    Total.val ((predicateFunctor P).map f).hom =
      (NumericalArithmetic.numericalInterpretation.map f).restrictedProgram := rfl

theorem predicateFunctor_graph {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D) (x y : ℕ) :
    y ∈ Total.val ((predicateFunctor P).map f).hom x ↔
      ∃ a : PredicateInterpretation.Obj ℕ C,a.val=x ∧
        ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map f a).val=y := by
  rw [predicateFunctor_program,NumericalTuples.Map.restrictedProgram_graph]
  constructor
  · rintro ⟨a,ha,hb⟩
    refine ⟨a,?_,?_⟩
    · change NumericalTuples.code 1 a.val = x at ha
      simpa only [NumericalTuples.code_one] using ha
    · change NumericalTuples.code 1 ((NumericalArithmetic.numericalInterpretation.map f).toFun a).val = y at hb
      simpa only [NumericalTuples.code_one,NumericalArithmetic.numericalInterpretation_value] using hb
  · rintro ⟨a,ha,hb⟩
    refine ⟨a,?_,?_⟩
    · change NumericalTuples.code 1 a.val = x
      simpa only [NumericalTuples.code_one] using ha
    · change NumericalTuples.code 1 ((NumericalArithmetic.numericalInterpretation.map f).toFun a).val = y
      simpa only [NumericalTuples.code_one,NumericalArithmetic.numericalInterpretation_value] using hb

/-- These are the original literal word predicates. Computation witnesses
remain inside their membership conditions, not in their word coordinates. -/
def words (formula : Bool) (p q : SyntacticSyntax.RawPolynomial) : Total.Carrier P :=
  predicateObject P (SyntacticSyntax.Postfix.plainCarrier formula p q)

theorem words_support (formula : Bool) (p q : SyntacticSyntax.RawPolynomial) :
    (words P formula p q).support =
      {w : ℕ | (SyntacticSyntax.Postfix.plainCarrier formula p q).val.Evalb (M := ℕ) ![w]} := rfl

/-- The source is the already constructed original plain-postfix algebra.
Its initiality is not transported to the larger uniform morphism class. -/
abbrev sourceAlgebra (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :=
  SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 p q

end CategoricalEssentialIncompleteness.V46.Miller.Syntax
