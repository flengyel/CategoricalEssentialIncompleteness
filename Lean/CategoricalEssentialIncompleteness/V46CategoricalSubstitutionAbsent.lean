import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentClosure
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! Substitution at an absent named variable on its actual term/formula fibers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.AlgebraInvariant

/-- Equalizers in the category of pairs are constructed componentwise. -/
theorem pairEqualizers (C : Type u) [Category.{v} C] [HasEqualizers C] :
    HasEqualizers (C × C) := by
  have : ∀ {X Y : C × C} {f g : X ⟶ Y}, HasLimit (parallelPair f g) := by
    intro X Y f g
    let i : (equalizer f.1 g.1, equalizer f.2 g.2) ⟶ X :=
      (equalizer.ι f.1 g.1, equalizer.ι f.2 g.2)
    let t : Fork f g := Fork.ofι i (by
      apply Prod.ext
      · exact equalizer.condition f.1 g.1
      · exact equalizer.condition f.2 g.2)
    exact HasLimit.mk ⟨t, Fork.IsLimit.mk' t (fun s => by
      let l : s.pt ⟶ t.pt :=
        (equalizer.lift s.ι.1 (congrArg Prod.fst s.condition),
          equalizer.lift s.ι.2 (congrArg Prod.snd s.condition))
      refine ⟨l, ?_, ?_⟩
      · exact Prod.ext (equalizer.lift_ι _ _) (equalizer.lift_ι _ _)
      · intro m hm
        apply Prod.ext
        · apply equalizer.hom_ext
          have h := congrArg Prod.fst hm
          change m.1 ≫ equalizer.ι f.1 g.1 = s.ι.1 at h
          simpa only [l, equalizer.lift_ι] using h
        · apply equalizer.hom_ext
          have h := congrArg Prod.snd hm
          change m.2 ≫ equalizer.ι f.2 g.2 = s.ι.2 at h
          simpa only [l, equalizer.lift_ι] using h)⟩
  exact hasEqualizers_of_hasLimit_parallelPair (C × C)

end CategoricalEssentialIncompleteness.V46.AlgebraInvariant

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

theorem absence_fold_invariant :
    S.substitutionFold ≫ S.absenceMask = S.substitutionFold ≫ S.absenceResult := by
  have := AlgebraInvariant.pairEqualizers (Over S.substitutionParameters)
  exact AlgebraInvariant.fold_equalizes
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters)
    S.substitutionAlgebra (S.stable S.substitutionParameters)
    S.absenceMask S.absenceResult S.absence_constructor_closed

/-- Every generalized term input is fixed when the named variable is absent. -/
theorem term_substitution_absent {X : D}
    (k : X ⟶ S.algebra.a.1 ⨯ S.substitutionParameters)
    (ha : S.termAbsenceTest (k ≫ prod.snd) (k ≫ prod.fst) = Two.constant X false) :
    k ≫ S.termSubstitution = k ≫ prod.fst := by
  have good := (S.absence_recursive_good S.substitutionFold S.absence_fold_invariant).1
  let z := k ≫ (prod.braiding S.algebra.a.1 S.substitutionParameters).hom
  have hp : z ≫ prod.fst = k ≫ prod.snd := by simp [z, prod.braiding_hom]
  have ho : z ≫ S.substitutionFold.1.left ≫ prod.snd ≫ prod.fst = k ≫ prod.fst := by
    simpa only [z, Category.assoc] using
      congrArg (fun h => k ≫ h) S.termSubstitution_original
  have hz : S.termAbsenceTest (z ≫ prod.fst)
      (z ≫ S.substitutionFold.1.left ≫ prod.snd ≫ prod.fst) = Two.constant X false := by
    rw [hp, ho]
    exact ha
  have hr := S.termPair_fixed prod.fst (S.substitutionFold.1.left ≫ prod.snd) good z
    (by simpa only [Category.assoc] using hz)
  simp only [Category.assoc] at hr
  have hh := hr.trans ho
  simpa only [z, termSubstitution, Category.assoc] using hh

/-- Absence makes formula substitution successful and preserves the original formula. -/
theorem formula_substitution_absent {X : D}
    (k : X ⟶ S.algebra.a.2 ⨯ S.substitutionParameters)
    (ha : S.formulaAbsenceTest (k ≫ prod.snd) (k ≫ prod.fst) = Two.constant X false) :
    k ≫ S.formulaSubstitutionOption = k ≫ prod.fst ≫ coprod.inr := by
  have good := (S.absence_recursive_good S.substitutionFold S.absence_fold_invariant).2
  let z := k ≫ (prod.braiding S.algebra.a.2 S.substitutionParameters).hom
  have hp : z ≫ prod.fst = k ≫ prod.snd := by simp [z, prod.braiding_hom]
  have ho : z ≫ S.substitutionFold.2.left ≫ prod.snd ≫ prod.fst = k ≫ prod.fst := by
    simpa only [z, Category.assoc] using
      congrArg (fun h => k ≫ h) S.formulaSubstitution_original
  have hz : S.formulaAbsenceTest (z ≫ prod.fst)
      (z ≫ S.substitutionFold.2.left ≫ prod.snd ≫ prod.fst) = Two.constant X false := by
    rw [hp, ho]
    exact ha
  have hr := S.formulaPair_fixed prod.fst (S.substitutionFold.2.left ≫ prod.snd) good z
    (by simpa only [Category.assoc] using hz)
  simp only [Category.assoc] at hr
  have ho' := congrArg (fun h => h ≫
    (coprod.inr : S.algebra.a.2 ⟶ OptionSyntax.obj S.algebra.a.2)) ho
  simp only [Category.assoc] at ho'
  simpa only [z, formulaSubstitutionOption, Category.assoc] using hr.trans ho'

def termAbsentTest : S.algebra.a.1 ⨯ S.substitutionParameters ⟶ Two D :=
  S.termAbsenceTest prod.snd prod.fst

def formulaAbsentTest : S.algebra.a.2 ⨯ S.substitutionParameters ⟶ Two D :=
  S.formulaAbsenceTest prod.snd prod.fst

abbrev termAbsentObject : D := Two.Fiber S.termAbsentTest false
abbrev formulaAbsentObject : D := Two.Fiber S.formulaAbsentTest false

def termAbsentInclusion : S.termAbsentObject ⟶ S.algebra.a.1 ⨯ S.substitutionParameters :=
  Two.fiberι S.termAbsentTest false

def formulaAbsentInclusion : S.formulaAbsentObject ⟶ S.algebra.a.2 ⨯ S.substitutionParameters :=
  Two.fiberι S.formulaAbsentTest false

instance termAbsentInclusion_mono : Mono S.termAbsentInclusion := by
  dsimp [termAbsentInclusion]
  infer_instance
instance formulaAbsentInclusion_mono : Mono S.formulaAbsentInclusion := by
  dsimp [formulaAbsentInclusion]
  infer_instance

theorem termAbsent_fixed :
    S.termAbsentInclusion ≫ S.termSubstitution = S.termAbsentInclusion ≫ prod.fst :=
  S.term_substitution_absent _ (by
    simpa only [termAbsentInclusion, termAbsentObject, termAbsentTest, S.termAbsenceTest_comp] using
      Two.fiberι_comp S.termAbsentTest false)

theorem formulaAbsent_success :
    S.formulaAbsentInclusion ≫ S.formulaSubstitutionOption =
      S.formulaAbsentInclusion ≫ prod.fst ≫ coprod.inr :=
  S.formula_substitution_absent _ (by
    simpa only [formulaAbsentInclusion, formulaAbsentObject, formulaAbsentTest, S.formulaAbsenceTest_comp] using
      Two.fiberι_comp S.formulaAbsentTest false)

/-- The actual absent-formula fiber factors through the actual successful-option pullback. -/
def formulaAbsentAdmissible : S.formulaAbsentObject ⟶ S.admissibleSubstitution :=
  pullback.lift S.formulaAbsentInclusion (S.formulaAbsentInclusion ≫ prod.fst)
    (by simpa only [Category.assoc] using S.formulaAbsent_success)

@[simp, reassoc] theorem formulaAbsentAdmissible_inclusion :
    S.formulaAbsentAdmissible ≫ S.admissibleInclusion = S.formulaAbsentInclusion :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem formulaAbsentAdmissible_result :
    S.formulaAbsentAdmissible ≫ S.formulaSubstitution =
      S.formulaAbsentInclusion ≫ prod.fst := pullback.lift_snd _ _ _

theorem term_substitution_absent_names {X : D} (u : X ⟶ S.algebra.a.1)
    (x : X ⟶ V) (t : X ⟶ S.algebra.a.1)
    (ha : prod.lift x (u ≫ S.termOccurrences) ≫ S.lists.membership S.decidableVariables =
      Two.constant X false) :
    prod.lift u (prod.lift x t) ≫ S.termSubstitution = u := by
  simpa only [prod.lift_fst, substitutionParameters] using S.term_substitution_absent
    (prod.lift u (prod.lift x t)) (by simpa [termAbsenceTest] using ha)

theorem formula_substitution_absent_names {X : D} (φ : X ⟶ S.algebra.a.2)
    (x : X ⟶ V) (t : X ⟶ S.algebra.a.1)
    (ha : prod.lift x (φ ≫ S.formulaOccurrences) ≫ S.lists.membership S.decidableVariables =
      Two.constant X false) :
    prod.lift φ (prod.lift x t) ≫ S.formulaSubstitutionOption = φ ≫ coprod.inr := by
  simpa only [prod.lift_fst_assoc, substitutionParameters] using S.formula_substitution_absent
    (prod.lift φ (prod.lift x t)) (by simpa [formulaAbsenceTest] using ha)

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
