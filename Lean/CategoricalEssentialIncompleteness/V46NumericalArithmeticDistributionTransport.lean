/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralOperations
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralInputValues
public import CategoricalEssentialIncompleteness.V46SyntaxBooleanTransport
public import CategoricalEssentialIncompleteness.V46LogicalSchemes
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # The numerical absent-variable fiber under the literal equivalence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₀ v₁ u₀ u₁
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionTransport
open SyntaxOperationsTransport

section Equalizers
variable {C : Type u₀} [Category.{v₀} C] [HasEqualizers C]
variable {A B A' B' : C} (f g : A ⟶ B) (f' g' : A' ⟶ B')
  (i : A ≅ A') (j : B ≅ B')
  (hf : i.hom ≫ f' = f ≫ j.hom) (hg : i.hom ≫ g' = g ≫ j.hom)

omit [HasEqualizers C] in
private theorem inverse_square (h : A ⟶ B) (h' : A' ⟶ B')
    (hh : i.hom ≫ h' = h ≫ j.hom) :
    i.inv ≫ h = h' ≫ j.inv := by
  apply (cancel_mono j.hom).1
  rw [Category.assoc,← hh,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  simp

/-- The equalizer comparison changes its ambient coordinates; its point is not replaced by
a witness for equalization. -/
def equalizerChart : equalizer f g ≅ equalizer f' g' where
  hom := equalizer.lift (equalizer.ι f g ≫ i.hom) (by
    rw [Category.assoc,hf,← Category.assoc,equalizer.condition,Category.assoc,← hg,Category.assoc])
  inv := equalizer.lift (equalizer.ι f' g' ≫ i.inv) (by
    rw [Category.assoc,inverse_square i j f f' hf,
      ← Category.assoc,equalizer.condition,Category.assoc,
      ← inverse_square i j g g' hg,Category.assoc])
  hom_inv_id := by
    apply (cancel_mono (equalizer.ι f g)).1
    simp only [Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (equalizer.ι f' g')).1
    simp only [Category.assoc, equalizer.lift_ι, equalizer.lift_ι_assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc] theorem equalizerChart_inclusion :
    (equalizerChart f g f' g' i j hf hg).hom ≫ equalizer.ι f' g' =
      equalizer.ι f g ≫ i.hom := equalizer.lift_ι _ _
end Equalizers

section Syntax
variable {C : Type u₀} {D : Type u₁} [Category.{v₀} C] [Category.{v₁} D]
  [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
  (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
  (S₀ : CategoricalSyntax (E.inverse.obj V)
    (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
  (S₁ : CategoricalSyntax V σ π d)
  (hLists : S₁.lists = SyntacticLists.Transport.mappedStableListAlgebra E
    (E.inverse.obj V) V (E.counitIso.app V) S₀.lists)
  (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
local notation "bY" => syntaxFormulaIso («S₁» := S₁) E V σ π d S₀ c
local notation "bL" => syntaxListIso E V σ π d S₀ S₁ hLists

def baseIso : E.functor.obj (E.inverse.obj V ⨯ (S₀.algebra.a.2 ⨯ S₀.algebra.a.2)) ≅
    V ⨯ (S₁.algebra.a.2 ⨯ S₁.algebra.a.2) :=
  SyntaxOptionTransport.productIso E (E.counitIso.app V)
    (SyntaxOptionTransport.productIso E bY bY)

theorem occurrenceInput_square :
    E.functor.map (prod.lift prod.fst (prod.snd ≫ prod.fst ≫ S₀.formulaOccurrences)) ≫
      (SyntaxOptionTransport.productIso E (E.counitIso.app V) bL).hom =
        (baseIso E V σ π d S₀ S₁ c).hom ≫
          prod.lift prod.fst (prod.snd ≫ prod.fst ≫ S₁.formulaOccurrences) := by
  have hFV := (formulaOccurrenceComparison_iff E V σ π d S₀ S₁ hLists c).mp
    (mapped_formulaOccurrence_comparison E V σ π d S₀ S₁ hLists c)
  have hfirst : (baseIso E V σ π d S₀ S₁ c).hom ≫ prod.snd ≫ prod.fst =
      E.functor.map ((prod.snd : E.inverse.obj V ⨯ (S₀.algebra.a.2 ⨯ S₀.algebra.a.2) ⟶
        S₀.algebra.a.2 ⨯ S₀.algebra.a.2) ≫ prod.fst) ≫ (bY).hom := by
    change (SyntaxOptionTransport.productIso E (E.counitIso.app V)
      (SyntaxOptionTransport.productIso E bY bY)).hom ≫ prod.snd ≫ prod.fst = _
    rw [SyntaxOptionTransport.productIso_snd_assoc, SyntaxOptionTransport.productIso_fst,
      ← Category.assoc, ← E.functor.map_comp]
  change E.functor.map (prod.lift prod.fst
      (prod.snd ≫ prod.fst ≫ S₀.formulaOccurrences)) ≫
    (SyntaxOptionTransport.productIso E (E.counitIso.app V) bL).hom =
      (baseIso E V σ π d S₀ S₁ c).hom ≫
        prod.lift prod.fst (prod.snd ≫ prod.fst ≫ S₁.formulaOccurrences)
  rw [SyntaxOptionTransport.map_lift, prod.comp_lift]
  apply congrArg₂ (fun a b => prod.lift a b)
  · exact (SyntaxOptionTransport.productIso_fst E (E.counitIso.app V)
      (SyntaxOptionTransport.productIso E bY bY)).symm
  · calc
      _ = E.functor.map (prod.snd ≫ prod.fst) ≫
          E.functor.map S₀.formulaOccurrences ≫ (bL).hom := by
        rw [← Category.assoc, E.functor.map_comp, Category.assoc]
      _ = E.functor.map (prod.snd ≫ prod.fst) ≫ (bY).hom ≫ S₁.formulaOccurrences :=
        congrArg (fun k => E.functor.map (prod.snd ≫ prod.fst) ≫ k) hFV
      _ = ((baseIso E V σ π d S₀ S₁ c).hom ≫ prod.snd ≫ prod.fst) ≫ S₁.formulaOccurrences := by
        simpa only [Category.assoc] using congrArg (fun k => k ≫ S₁.formulaOccurrences) hfirst.symm
      _ = _ := by simp only [Category.assoc]

include hLists in
/-- The comparison of the Boolean occurrence classifiers follows from the membership fold
and occurrence-algebra diagrams. -/
theorem absence_square :
    E.functor.map S₀.distributionAbsence ≫ (DecidableVariables.Transport.booleanIso E).hom =
      (baseIso E V σ π d S₀ S₁ c).hom ≫ S₁.distributionAbsence := by
  dsimp only [CategoricalSyntax.distributionAbsence]
  rw [E.functor.map_comp,Category.assoc,
    syntaxList_membership_comparison E V σ π d S₀ S₁ hLists,
    ← Category.assoc,occurrenceInput_square,Category.assoc]

include hLists in
/-- The Q2 label comparison is an isomorphism of the prescribed false fibers. Its ambient
name and two formula entries are preserved. -/
def fiberIso : E.functor.obj S₀.distributionParameters ≅ S₁.distributionParameters :=
  PreservesEqualizer.iso E.functor S₀.distributionAbsence (Two.constant _ false) ≪≫
    equalizerChart (E.functor.map S₀.distributionAbsence)
      (E.functor.map (Two.constant _ false)) S₁.distributionAbsence (Two.constant _ false)
      (baseIso E V σ π d S₀ S₁ c) (DecidableVariables.Transport.booleanIso E)
      (absence_square E V σ π d S₀ S₁ hLists c).symm
      (by rw [map_constant,Two.comp_constant])

@[reassoc] theorem fiberIso_inclusion :
    (fiberIso E V σ π d S₀ S₁ hLists c).hom ≫ S₁.distributionInclusion =
      E.functor.map S₀.distributionInclusion ≫ (baseIso E V σ π d S₀ S₁ c).hom := by
  simp only [fiberIso, Iso.trans_hom, CategoricalSyntax.distributionInclusion, Two.fiberι,
    Category.assoc, equalizerChart_inclusion]
  rw [← Category.assoc, PreservesEqualizer.iso_hom, equalizerComparison_comp_π]

end Syntax
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionTransport
