/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentFamilies
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentSteps

/-! The actual absence equalizer on the original/result substitution carriers. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

/-- The term component compares ordinary terms; the formula component compares options. -/
def absenceInvariantTarget : Over S.substitutionParameters × Over S.substitutionParameters :=
  (constantFamily S.substitutionParameters S.algebra.a.1,
    constantFamily S.substitutionParameters (OptionSyntax.obj S.algebra.a.2))

/-- The masked result uses the original syntax exactly on the false membership fiber. -/
def absenceMask : S.substitutionAlgebra.a ⟶ S.absenceInvariantTarget :=
  (AbsentFamilies.mask S.lists S.decidableVariables prod.fst S.termOccurrences (𝟙 _),
    AbsentFamilies.mask S.lists S.decidableVariables prod.fst S.formulaOccurrences coprod.inr)

def absenceResult : S.substitutionAlgebra.a ⟶ S.absenceInvariantTarget :=
  (AbsentFamilies.result (P := S.substitutionParameters)
      (U := S.algebra.a.1) (Y := S.algebra.a.1),
    AbsentFamilies.result (P := S.substitutionParameters)
      (U := S.algebra.a.2) (Y := OptionSyntax.obj S.algebra.a.2))

theorem absence_equation_term {A : Over S.substitutionParameters}
    (m : A ⟶ constantFamily S.substitutionParameters S.substitutionCarriers.1) :
    m ≫ S.absenceMask.1 = m ≫ S.absenceResult.1 ↔
      S.termPairGood A.hom (m.left ≫ prod.snd) := by
  simpa only [absenceMask, absenceResult, termPairGood, termAbsenceTest,
    substitutionCarriers, substitutionParameters, ConditionalInvariant.Holds,
    Category.comp_id, Category.assoc] using AbsentFamilies.equation_iff
      S.lists S.decidableVariables (prod.fst : S.substitutionParameters ⟶ V)
        S.termOccurrences (𝟙 _) m

theorem absence_equation_formula {A : Over S.substitutionParameters}
    (m : A ⟶ constantFamily S.substitutionParameters S.substitutionCarriers.2) :
    m ≫ S.absenceMask.2 = m ≫ S.absenceResult.2 ↔
      S.formulaPairGood A.hom (m.left ≫ prod.snd) := by
  simpa only [absenceMask, absenceResult, formulaPairGood, formulaAbsenceTest,
    substitutionCarriers, substitutionParameters, ConditionalInvariant.Holds,
    Category.assoc] using AbsentFamilies.equation_iff
      S.lists S.decidableVariables (prod.fst : S.substitutionParameters ⟶ V)
        S.formulaOccurrences coprod.inr m

theorem absence_recursive_good {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ S.absenceMask = m ≫ S.absenceResult) :
    S.termPairGood A.1.hom (m.1.left ≫ prod.snd) ∧
      S.formulaPairGood A.2.hom (m.2.left ≫ prod.snd) :=
  ⟨(S.absence_equation_term m.1).mp (congrArg Prod.fst hm),
    (S.absence_equation_formula m.2).mp (congrArg Prod.snd hm)⟩

def absenceOriginalFamilies : S.substitutionAlgebra.a ⟶
    (constantFamily S.substitutionParameters S.algebra.a.1,
      constantFamily S.substitutionParameters S.algebra.a.2) :=
  ((constantFamilyFunctor S.substitutionParameters).map S.originalProjection.1,
    (constantFamilyFunctor S.substitutionParameters).map S.originalProjection.2)

def absenceComputedFamilies : S.substitutionAlgebra.a ⟶
    (constantFamily S.substitutionParameters S.algebra.a.1,
      constantFamily S.substitutionParameters S.algebra.a.2) :=
  ((constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.1,
    (constantFamilyFunctor S.substitutionParameters).map S.termResultProjection.2)

@[simp, reassoc] theorem absenceOriginalFamilies_term
    {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a) :
    (m ≫ S.absenceOriginalFamilies).1.left ≫ prod.snd = m.1.left ≫ prod.snd ≫ prod.fst := by
  simp [absenceOriginalFamilies, originalProjection, constantFamilyFunctor, Over.comp_left,
    Category.assoc]

@[simp, reassoc] theorem absenceComputedFamilies_term
    {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a) :
    (m ≫ S.absenceComputedFamilies).1.left ≫ prod.snd = m.1.left ≫ prod.snd ≫ prod.snd := by
  simp [absenceComputedFamilies, termResultProjection, constantFamilyFunctor, Over.comp_left,
    Category.assoc]

theorem absence_arguments_fixed
    {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ S.absenceMask = m ≫ S.absenceResult) :
    ∀ {X : D} (k : X ⟶ A.1.left),
      prod.lift (k ≫ A.1.hom ≫ prod.fst)
        (k ≫ (m ≫ S.absenceOriginalFamilies).1.left ≫ prod.snd ≫ S.termOccurrences) ≫
          S.lists.membership S.decidableVariables = Two.constant X false →
      k ≫ (m ≫ S.absenceComputedFamilies).1.left ≫ prod.snd =
        k ≫ (m ≫ S.absenceOriginalFamilies).1.left ≫ prod.snd := by
  intro X k ha
  have hg := (S.absence_recursive_good m hm).1
  have ha' : S.termAbsenceTest (k ≫ A.1.hom)
      (k ≫ m.1.left ≫ prod.snd ≫ prod.fst) = Two.constant X false := by
    simpa only [termAbsenceTest, S.absenceOriginalFamilies_term_assoc, Category.assoc] using ha
  simpa only [S.absenceComputedFamilies_term, S.absenceOriginalFamilies_term,
    Category.assoc] using S.termPair_fixed A.1.hom (m.1.left ≫ prod.snd) hg k
      (by simpa only [Category.assoc] using ha')

theorem absence_recursive_term_precomp
    {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ S.absenceMask = m ≫ S.absenceResult)
    {X : Over S.substitutionParameters} (i : X ⟶ A.1) :
    S.termPairGood X.hom ((i ≫ m.1).left ≫ prod.snd) := by
  apply (S.absence_equation_term (i ≫ m.1)).mp
  have h : m.1 ≫ S.absenceMask.1 = m.1 ≫ S.absenceResult.1 := congrArg Prod.fst hm
  simpa only [Category.assoc] using congrArg (fun f => i ≫ f) h

theorem absence_recursive_formula_precomp
    {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a)
    (hm : m ≫ S.absenceMask = m ≫ S.absenceResult)
    {X : Over S.substitutionParameters} (i : X ⟶ A.2) :
    S.formulaPairGood X.hom ((i ≫ m.2).left ≫ prod.snd) := by
  apply (S.absence_equation_formula (i ≫ m.2)).mp
  have h : m.2 ≫ S.absenceMask.2 = m.2 ≫ S.absenceResult.2 := congrArg Prod.snd hm
  simpa only [Category.assoc] using congrArg (fun f => i ≫ f) h

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
