/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralValues
import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportCoordinates

/-! # Literal numerical list constructors have the finite-word values -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport SyntacticLists.Transport

section ConsComparison
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : C) (W : D) (e : E.functor.obj V ≅ W)
variable (L : StableListAlgebra V) (R : StableListAlgebra W)

theorem listConsEqualityComparison (h : R = mappedStableListAlgebra E V W e L) :
    E.functor.map L.algebra.cons ≫ (mappedListEqualityIso E V W e L R h).hom =
      (SyntaxOptionTransport.productIso E e (mappedListEqualityIso E V W e L R h)).hom ≫
        R.algebra.cons := by
  cases h
  simpa only [mappedListEqualityIso, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    SyntaxOptionTransport.productIso, Iso.trans_hom, asIso_hom, prod.mapIso_hom, Category.assoc]
    using map_list_cons E V W e L

end ConsComparison

variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V

def literalListNilInputPresentationIso : ⊤_ NumericalTuples.Object ≅
    NumericalCoordinates.predicateObject (⊤_ (PredicateCategory 𝗧𝗔)) :=
  (asIso (terminalComparison (E).functor)).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (⊤_ (PredicateCategory 𝗧𝗔))

def literalListConsInputIso : (E).functor.obj (V₀ ⨯ (S₀).lists.algebra.carrier) ≅
    V ⨯ (S₁).lists.algebra.carrier :=
  SyntaxOptionTransport.productIso (E) ((E).counitIso.app V) (literalListIso V σ π d)

def literalListConsInputPresentationIso : V ⨯ (S₁).lists.algebra.carrier ≅
    NumericalCoordinates.predicateObject (V₀ ⨯ (S₀).lists.algebra.carrier) :=
  (literalListConsInputIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (V₀ ⨯ (S₀).lists.algebra.carrier)

theorem literal_listNil_code_square :
    (S₁).lists.algebra.nil ≫ (literalListPresentationIso V σ π d).hom =
      (literalListNilInputPresentationIso).hom ≫
        NumericalCoordinates.predicateMap (S₀).lists.algebra.nil :=
  conjugate_operation ((E).functor.map (S₀).lists.algebra.nil) (S₁).lists.algebra.nil
    (asIso (terminalComparison (E).functor)) (literalListIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (⊤_ (PredicateCategory 𝗧𝗔)))
    (NumericalCoordinates.predicatePresentationIso (S₀).lists.algebra.carrier)
    (syntaxList_nil_comparison (E) V σ π d (S₀) (S₁) (literalListsEquality V σ π d))

theorem literal_listCons_code_square :
    (S₁).lists.algebra.cons ≫ (literalListPresentationIso V σ π d).hom =
      (literalListConsInputPresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).lists.algebra.cons :=
  conjugate_operation ((E).functor.map (S₀).lists.algebra.cons) (S₁).lists.algebra.cons
    (literalListConsInputIso V σ π d) (literalListIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (V₀ ⨯ (S₀).lists.algebra.carrier))
    (NumericalCoordinates.predicatePresentationIso (S₀).lists.algebra.carrier)
    (listConsEqualityComparison (E) V₀ V ((E).counitIso.app V)
      (S₀).lists (S₁).lists (literalListsEquality V σ π d))

theorem literal_listCarrier_eval (word : ℕ) :
    (S₀).lists.algebra.carrier.val.Evalb (M := ℕ) ![word] ↔
      ∀ i < len word, nth word i ∈ NumericalTuples.codedSupport V := by
  change (SyntacticLists.listCarrier V₀).val.Evalb (M := ℕ) ![word] ↔ _
  rw [SyntacticLists.listCarrier_eval]
  simp only [NumericalCoordinates.codedPredicate_eval]

theorem literal_listWord_mem (x : NumericalTuples.Point (S₁).lists.algebra.carrier) :
    let word : ℕ := ((literalListPresentationIso V σ π d).hom.toFun x).val
    ∀ i < len word, nth word i ∈ NumericalTuples.codedSupport V :=
  (literal_listCarrier_eval V σ π d _).mp
    ((literalListPresentationIso V σ π d).hom.toFun x).property

theorem literal_listNil_value (x : NumericalTuples.Point (⊤_ NumericalTuples.Object)) :
    ((literalListPresentationIso V σ π d).hom.toFun ((S₁).lists.algebra.nil.toFun x)).val = (0 : ℕ) :=
  predicate_operation_value (S₀).lists.algebra.nil (S₁).lists.algebra.nil
    (literalListNilInputPresentationIso) (literalListPresentationIso V σ π d)
    (literal_listNil_code_square V σ π d) Subtype.val (fun _ => 0)
    (SyntacticLists.nil_value 𝗧𝗔 ℕ (⊤_ (PredicateCategory 𝗧𝗔)) V₀) x

theorem literal_listCons_value
    (x : NumericalTuples.Point (V ⨯ (S₁).lists.algebra.carrier)) :
    let x₀ := (literalListConsInputPresentationIso V σ π d).hom.toFun x
    ((literalListPresentationIso V σ π d).hom.toFun ((S₁).lists.algebra.cons.toFun x)).val =
      adjoin (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
          (V₀ ⨯ (S₀).lists.algebra.carrier) V₀)) x₀).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map
          (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
            (V₀ ⨯ (S₀).lists.algebra.carrier) (S₀).lists.algebra.carrier)) x₀).val :=
  predicate_operation_value (S₀).lists.algebra.cons (S₁).lists.algebra.cons
    (literalListConsInputPresentationIso V σ π d) (literalListPresentationIso V σ π d)
    (literal_listCons_code_square V σ π d) Subtype.val _
    (SyntacticLists.cons_value 𝗧𝗔 ℕ V₀) x

end CategoricalEssentialIncompleteness.V46.NumericalNamed
