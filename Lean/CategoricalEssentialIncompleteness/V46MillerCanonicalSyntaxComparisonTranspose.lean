/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonCore
public import CategoricalEssentialIncompleteness.V46SyntaxOptionTransport
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportDeletion
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportMembership

/-! # Transposing actual comparison squares through the equivalence unit

The inverse-signature transport library applies to E.symm and the explicit
forward signature. These lemmas transpose its equations through the unit;
neither an inverse-choice coordinate identity nor a new operation equation
is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (E : C ≌ D)

def transposeIso {X : C} {Y : D} (i : E.functor.obj X ≅ Y) : E.inverse.obj Y ≅ X :=
  E.inverse.mapIso i.symm ≪≫ (E.unitIso.app X).symm

theorem transpose_square {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : E.functor.map f ≫ j.hom = i.hom ≫ g) :
    E.inverse.map g ≫ (transposeIso E j).hom = (transposeIso E i).hom ≫ f := by
  have hg : g ≫ j.inv = i.inv ≫ E.functor.map f := by
    apply (cancel_epi i.hom).mp
    calc
      i.hom≫(g≫j.inv)=(i.hom≫g)≫j.inv := (Category.assoc _ _ _).symm
      _=(E.functor.map f≫j.hom)≫j.inv := congrArg
        (fun k : E.functor.obj X ⟶ Y' => k≫j.inv) h.symm
      _=E.functor.map f := by rw [Category.assoc,j.hom_inv_id,Category.comp_id]
      _=i.hom≫(i.inv≫E.functor.map f) := (Iso.hom_inv_id_assoc i _).symm
  change E.inverse.map g ≫ (E.inverse.map j.inv ≫ (E.unitIso.app Y).inv) =
    (E.inverse.map i.inv ≫ (E.unitIso.app X).inv) ≫ f
  rw [← Category.assoc, ← E.inverse.map_comp, hg, E.inverse.map_comp, Category.assoc]
  have hu := E.unitIso.inv.naturality f
  change E.inverse.map (E.functor.map f) ≫ (E.unitIso.app Y).inv =
    (E.unitIso.app X).inv ≫ f at hu
  simpa only [Category.assoc] using
    congrArg (fun k => E.inverse.map i.inv ≫ k) hu

theorem transpose_refl (X : C) :
    transposeIso E (Iso.refl (E.functor.obj X)) = (E.unitIso.app X).symm := by
  apply Iso.ext
  simp only [transposeIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.refl_inv, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The round trip used for a forward-mapped coefficient is the triangle
identity, rather than an equality of inverse-choice coordinates. -/
theorem transpose_unit_inverse (X : C) :
    transposeIso E.symm (E.unitIso.app X).symm = Iso.refl (E.functor.obj X) := by
  apply Iso.ext
  change E.functor.map (E.unitIso.app X).hom ≫ (E.counitIso.app (E.functor.obj X)).hom = 𝟙 _
  exact E.functor_unitIso_comp X

-- Only the following geometric comparisons use the finite-limit and
-- finite-coproduct structure. Bare transposition is an equivalence law.
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem transpose_terminal :
    transposeIso E (DecidableVariables.Transport.terminalIso E) =
      DecidableVariables.Transport.terminalIso E.symm := by
  apply Iso.ext
  exact terminalIsTerminal.hom_ext _ _

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem transpose_product {X Y : C} {X' Y' : D}
    (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y') :
    transposeIso E (SyntaxOptionTransport.productIso E i j) =
      SyntaxOptionTransport.productIso E.symm (transposeIso E i) (transposeIso E j) := by
  apply Iso.ext
  apply prod.hom_ext
  · exact (transpose_square E (SyntaxOptionTransport.productIso E i j) i prod.fst prod.fst
      (SyntaxOptionTransport.productIso_fst E i j).symm).symm.trans
        (SyntaxOptionTransport.productIso_fst E.symm (transposeIso E i) (transposeIso E j)).symm
  · exact (transpose_square E (SyntaxOptionTransport.productIso E i j) j prod.snd prod.snd
      (SyntaxOptionTransport.productIso_snd E i j).symm).symm.trans
        (SyntaxOptionTransport.productIso_snd E.symm (transposeIso E i) (transposeIso E j)).symm

theorem transpose_boolean :
    transposeIso E (DecidableVariables.Transport.booleanIso E) =
      DecidableVariables.Transport.booleanIso E.symm := by
  apply Iso.ext
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit E.inverse (⊤_ D) (⊤_ D))
  · exact (transpose_square E (DecidableVariables.Transport.terminalIso E)
      (DecidableVariables.Transport.booleanIso E) coprod.inl coprod.inl
      (SyntaxOperationsTransport.booleanIso_inl E)).trans
        ((congrArg (fun i => i.hom ≫ coprod.inl) (transpose_terminal E)).trans
          (SyntaxOperationsTransport.booleanIso_inl E.symm).symm)
  · exact (transpose_square E (DecidableVariables.Transport.terminalIso E)
      (DecidableVariables.Transport.booleanIso E) coprod.inr coprod.inr
      (DecidableVariables.Transport.booleanIso_inr E)).trans
        ((congrArg (fun i => i.hom ≫ coprod.inr) (transpose_terminal E)).trans
          (DecidableVariables.Transport.booleanIso_inr E.symm).symm)

theorem transpose_option {X : C} {X' : D} (i : E.functor.obj X ≅ X') :
    transposeIso E (SyntaxOptionTransport.optionIso E i) =
      SyntaxOptionTransport.optionIso E.symm (transposeIso E i) := by
  apply Iso.ext
  apply BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit E.inverse (⊤_ D) X')
  · exact (transpose_square E (DecidableVariables.Transport.terminalIso E)
      (SyntaxOptionTransport.optionIso E i) coprod.inl coprod.inl
      (SyntaxOptionTransport.optionIso_inl E i)).trans
        ((congrArg (fun t => t.hom ≫ coprod.inl) (transpose_terminal E)).trans
          (SyntaxOptionTransport.optionIso_inl E.symm (transposeIso E i)).symm)
  · exact (transpose_square E i (SyntaxOptionTransport.optionIso E i)
      coprod.inr coprod.inr (SyntaxOptionTransport.optionIso_inr E i)).trans
        (SyntaxOptionTransport.optionIso_inr E.symm (transposeIso E i)).symm

section Lists
open SyntacticLists.Transport SyntaxOperationsTransport
variable (V : C) (L : StableListAlgebra V)
local notation "M" => mappedStableListAlgebra E V (E.functor.obj V) (Iso.refl _) L

def reverseListIso : E.inverse.obj (M).algebra.carrier ≅ L.algebra.carrier :=
  (E.unitIso.app L.algebra.carrier).symm

theorem reverseList_nil :
    E.inverse.map (M).algebra.nil ≫ (reverseListIso E V L).hom =
      terminalComparison E.inverse ≫ L.algebra.nil := by
  have h := transpose_square E (DecidableVariables.Transport.terminalIso E)
    (Iso.refl (E.functor.obj L.algebra.carrier)) L.algebra.nil (M).algebra.nil
    ((Category.comp_id _).trans (map_list_nil E V (E.functor.obj V) (Iso.refl _) L))
  rw [transpose_terminal E,transpose_refl E] at h
  change E.inverse.map (M).algebra.nil ≫ (reverseListIso E V L).hom =
    terminalComparison E.inverse ≫ L.algebra.nil at h
  exact h

theorem reverseList_singleton :
    E.inverse.map (M).singleton ≫ (reverseListIso E V L).hom =
      (E.unitIso.app V).inv ≫ L.singleton := by
  have h := transpose_square E (Iso.refl (E.functor.obj V))
    (Iso.refl (E.functor.obj L.algebra.carrier)) L.singleton (M).singleton (by
      simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
        map_list_singleton E V (E.functor.obj V) (Iso.refl _) L)
  simpa only [transpose_refl, reverseListIso, Iso.symm_hom] using h

theorem reverseList_append :
    E.inverse.map (M).append ≫ (reverseListIso E V L).hom =
      (SyntaxOptionTransport.productIso E.symm (reverseListIso E V L)
        (reverseListIso E V L)).hom ≫ L.append := by
  have h := transpose_square E
    (SyntaxOptionTransport.productIso E (Iso.refl (E.functor.obj L.algebra.carrier))
      (Iso.refl (E.functor.obj L.algebra.carrier)))
    (Iso.refl (E.functor.obj L.algebra.carrier)) L.append (M).append (by
      simpa only [SyntaxOptionTransport.productIso, Iso.trans_hom, asIso_hom,
        prod.mapIso_hom, Iso.refl_hom, prod.map_id_id, Category.comp_id] using
          map_list_append E V (E.functor.obj V) (Iso.refl _) L)
  simpa only [transpose_product, transpose_refl, reverseListIso] using h

variable (S : DecidableVariables V) (T : DecidableVariables (E.functor.obj V))

theorem reverseList_deletion :
    E.inverse.map ((M).deletion T) ≫ (reverseListIso E V L).hom =
      (SyntaxOptionTransport.productIso E.symm (E.unitIso.app V).symm
        (reverseListIso E V L)).hom ≫ L.deletion S := by
  have h := transpose_square E
    (SyntaxOptionTransport.productIso E (Iso.refl (E.functor.obj V))
      (Iso.refl (E.functor.obj L.algebra.carrier)))
    (Iso.refl (E.functor.obj L.algebra.carrier)) (L.deletion S) ((M).deletion T) (by
      simpa only [SyntaxOptionTransport.productIso, Iso.trans_hom, asIso_hom,
        prod.mapIso_hom, Iso.refl_hom, prod.map_id_id, Category.comp_id, Category.id_comp]
        using map_list_deletion E V (E.functor.obj V) (Iso.refl _) L S T)
  simpa only [transpose_product, transpose_refl, reverseListIso] using h

theorem reverseList_membership :
    E.inverse.map ((M).membership T) ≫
        (DecidableVariables.Transport.booleanIso E.symm).hom =
      (SyntaxOptionTransport.productIso E.symm (E.unitIso.app V).symm
        (reverseListIso E V L)).hom ≫ L.membership S := by
  have h := transpose_square E
    (SyntaxOptionTransport.productIso E (Iso.refl (E.functor.obj V))
      (Iso.refl (E.functor.obj L.algebra.carrier)))
    (DecidableVariables.Transport.booleanIso E) (L.membership S) ((M).membership T) (by
      simpa only [SyntaxOptionTransport.productIso, Iso.trans_hom, asIso_hom,
        prod.mapIso_hom, Iso.refl_hom, prod.map_id_id, Category.comp_id, Category.id_comp]
        using map_list_membership E V (E.functor.obj V) (Iso.refl _) S T L)
  simpa only [transpose_boolean, transpose_product, transpose_refl, reverseListIso] using h
end Lists
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
