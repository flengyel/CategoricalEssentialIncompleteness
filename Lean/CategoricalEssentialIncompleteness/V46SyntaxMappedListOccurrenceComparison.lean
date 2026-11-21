/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransport
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportDeletion
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportMembership

/-! # Occurrence comparison from the mapped list-algebra equality -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
section GenericListComparisons
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V₀ : C) (V₁ : D) (e : E.functor.obj V₀ ≅ V₁)
variable (L : StableListAlgebra V₀)

private theorem mapped_nil_identity :
    E.functor.map L.algebra.nil ≫ 𝟙 (E.functor.obj L.algebra.carrier) =
      terminalComparison E.functor ≫ (mappedStableListAlgebra E V₀ V₁ e L).algebra.nil :=
  (Category.comp_id (E.functor.map L.algebra.nil)).trans (map_list_nil E V₀ V₁ e L)

private theorem mapped_singleton_identity :
    E.functor.map L.singleton ≫ 𝟙 (E.functor.obj L.algebra.carrier) =
      e.hom ≫ (mappedStableListAlgebra E V₀ V₁ e L).singleton :=
  (Category.comp_id (E.functor.map L.singleton)).trans (map_list_singleton E V₀ V₁ e L)

private theorem mapped_append_identity :
    E.functor.map L.append ≫ 𝟙 (E.functor.obj L.algebra.carrier) =
      (SyntaxOptionTransport.productIso E (Iso.refl (E.functor.obj L.algebra.carrier))
        (Iso.refl (E.functor.obj L.algebra.carrier))).hom ≫
          (mappedStableListAlgebra E V₀ V₁ e L).append := by
  have h : (SyntaxOptionTransport.productIso E (Iso.refl (E.functor.obj L.algebra.carrier))
      (Iso.refl (E.functor.obj L.algebra.carrier))).hom =
      prodComparison E.functor L.algebra.carrier L.algebra.carrier := by
    simp only [SyntaxOptionTransport.productIso,Iso.trans_hom,asIso_hom,prod.mapIso_hom,
      Iso.refl_hom,prod.map_id_id,Category.comp_id]
  exact (Category.comp_id (E.functor.map L.append)).trans ((map_list_append E V₀ V₁ e L).trans
    (congrArg (fun k => k ≫ (mappedStableListAlgebra E V₀ V₁ e L).append) h.symm))

private theorem mapped_deletion_identity (ε₀ : DecidableVariables V₀) (ε₁ : DecidableVariables V₁) :
    E.functor.map (L.deletion ε₀) ≫ 𝟙 (E.functor.obj L.algebra.carrier) =
      (SyntaxOptionTransport.productIso E e (Iso.refl (E.functor.obj L.algebra.carrier))).hom ≫
        (mappedStableListAlgebra E V₀ V₁ e L).deletion ε₁ :=
  (Category.comp_id (E.functor.map (L.deletion ε₀))).trans ((map_list_deletion E V₀ V₁ e L ε₀ ε₁).trans
    (Category.assoc (prodComparison E.functor V₀ L.algebra.carrier)
      (prod.map e.hom (𝟙 _)) ((mappedStableListAlgebra E V₀ V₁ e L).deletion ε₁)).symm)

def mappedListEqualityIso (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L) :
    E.functor.obj L.algebra.carrier ≅ R.algebra.carrier :=
  eqToIso (congrArg (fun S : StableListAlgebra V₁ => S.algebra.carrier) h.symm)

private theorem mapped_nil_equal (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L) :
    E.functor.map L.algebra.nil ≫ (mappedListEqualityIso E V₀ V₁ e L R h).hom =
      terminalComparison E.functor ≫ R.algebra.nil := by
  cases h
  exact mapped_nil_identity E V₀ V₁ e L

private theorem mapped_singleton_equal (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L) :
    E.functor.map L.singleton ≫ (mappedListEqualityIso E V₀ V₁ e L R h).hom = e.hom ≫ R.singleton := by
  cases h
  exact mapped_singleton_identity E V₀ V₁ e L

private def mappedAppendStatement (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L) : Prop :=
  E.functor.map L.append ≫ (mappedListEqualityIso E V₀ V₁ e L R h).hom =
    (SyntaxOptionTransport.productIso E (X := L.algebra.carrier) (Y := L.algebra.carrier)
      (mappedListEqualityIso E V₀ V₁ e L R h) (mappedListEqualityIso E V₀ V₁ e L R h)).hom ≫ R.append

private theorem mapped_append_equal (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L) : mappedAppendStatement E V₀ V₁ e L R h := by
  cases h
  exact mapped_append_identity E V₀ V₁ e L

private theorem mapped_deletion_equal (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L)
    (ε₀ : DecidableVariables V₀) (ε₁ : DecidableVariables V₁) :
    E.functor.map (L.deletion ε₀) ≫ (mappedListEqualityIso E V₀ V₁ e L R h).hom =
      (SyntaxOptionTransport.productIso E (X := V₀) (Y := L.algebra.carrier) e
        (mappedListEqualityIso E V₀ V₁ e L R h)).hom ≫ R.deletion ε₁ := by
  cases h
  exact mapped_deletion_identity E V₀ V₁ e L ε₀ ε₁

private theorem mapped_membership_equal (R : StableListAlgebra V₁)
    (h : R = mappedStableListAlgebra E V₀ V₁ e L)
    (ε₀ : DecidableVariables V₀) (ε₁ : DecidableVariables V₁) :
    E.functor.map (L.membership ε₀) ≫ (DecidableVariables.Transport.booleanIso E).hom =
      (SyntaxOptionTransport.productIso E (X := V₀) (Y := L.algebra.carrier) e
        (mappedListEqualityIso E V₀ V₁ e L R h)).hom ≫ R.membership ε₁ := by
  cases h
  exact (map_list_membership E V₀ V₁ e ε₀ ε₁ L).trans
    (Category.assoc (prodComparison E.functor V₀ L.algebra.carrier)
      (prod.map e.hom (𝟙 _)) ((mappedStableListAlgebra E V₀ V₁ e L).membership ε₁)).symm

end GenericListComparisons

section Syntax
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (hLists : S₁.lists = mappedStableListAlgebra E (E.inverse.obj V) V
  (E.counitIso.app V) S₀.lists)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

/-- The carrier comparison comes from equality of the complete list-algebra records,
including their proved stability data. -/
def syntaxListIso : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier :=
  mappedListEqualityIso E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists

theorem syntaxList_nil_comparison :
    E.functor.map S₀.lists.algebra.nil ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
      terminalComparison E.functor ≫ S₁.lists.algebra.nil :=
  mapped_nil_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists

theorem syntaxList_singleton_comparison :
    E.functor.map S₀.lists.singleton ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
      (E.counitIso.app V).hom ≫ S₁.lists.singleton :=
  mapped_singleton_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists

theorem syntaxList_append_comparison :
    E.functor.map S₀.lists.append ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
      (SyntaxOptionTransport.productIso E (X := S₀.lists.algebra.carrier) (Y := S₀.lists.algebra.carrier)
        (syntaxListIso E V σ π d S₀ S₁ hLists) (syntaxListIso E V σ π d S₀ S₁ hLists)).hom ≫ S₁.lists.append :=
  mapped_append_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists

theorem syntaxList_deletion_comparison :
    E.functor.map (S₀.lists.deletion S₀.decidableVariables) ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
      (SyntaxOptionTransport.productIso E (X := E.inverse.obj V) (Y := S₀.lists.algebra.carrier)
        (E.counitIso.app V) (syntaxListIso E V σ π d S₀ S₁ hLists)).hom ≫
          S₁.lists.deletion S₁.decidableVariables :=
  mapped_deletion_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists
    S₀.decidableVariables S₁.decidableVariables

/-- This predicate is exactly the displayed term occurrence diagram. -/
def termOccurrenceComparison : Prop :=
  E.functor.map S₀.termOccurrences ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
    (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c).hom ≫ S₁.termOccurrences

/-- This predicate is exactly the displayed formula occurrence diagram. -/
def formulaOccurrenceComparison : Prop :=
  E.functor.map S₀.formulaOccurrences ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
    (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c).hom ≫ S₁.formulaOccurrences

/-- All local list-operation comparisons are derived before this application of the
occurrence-algebra isomorphism and initiality. -/
theorem mapped_termOccurrence_comparison : termOccurrenceComparison E V σ π d S₀ S₁ hLists c :=
  map_termOccurrences E V σ π d S₀ S₁ (syntaxListIso E V σ π d S₀ S₁ hLists)
    (mapped_nil_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists)
    (mapped_singleton_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists)
    (mapped_append_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists)
    (mapped_deletion_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists
      S₀.decidableVariables S₁.decidableVariables) c

theorem mapped_formulaOccurrence_comparison : formulaOccurrenceComparison E V σ π d S₀ S₁ hLists c :=
  map_formulaOccurrences E V σ π d S₀ S₁ (syntaxListIso E V σ π d S₀ S₁ hLists)
    (mapped_nil_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists)
    (mapped_singleton_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists)
    (mapped_append_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists)
    (mapped_deletion_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists
      S₀.decidableVariables S₁.decidableVariables) c

theorem syntaxList_membership_comparison :
    E.functor.map (S₀.lists.membership S₀.decidableVariables) ≫
      (DecidableVariables.Transport.booleanIso E).hom =
      (SyntaxOptionTransport.productIso E (X := E.inverse.obj V) (Y := S₀.lists.algebra.carrier)
        (E.counitIso.app V) (syntaxListIso E V σ π d S₀ S₁ hLists)).hom ≫
          S₁.lists.membership S₁.decidableVariables :=
  mapped_membership_equal E (E.inverse.obj V) V (E.counitIso.app V) S₀.lists S₁.lists hLists
    S₀.decidableVariables S₁.decidableVariables

theorem termOccurrenceComparison_iff : termOccurrenceComparison E V σ π d S₀ S₁ hLists c ↔
    E.functor.map S₀.termOccurrences ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
      (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c).hom ≫ S₁.termOccurrences := Iff.rfl

theorem formulaOccurrenceComparison_iff : formulaOccurrenceComparison E V σ π d S₀ S₁ hLists c ↔
    E.functor.map S₀.formulaOccurrences ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
      (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c).hom ≫ S₁.formulaOccurrences := Iff.rfl

end Syntax
end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
