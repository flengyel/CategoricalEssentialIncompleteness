import CategoricalEssentialIncompleteness.V46MillerCanonicalParameterGeometry

/-! # All seven logical parameters in the actual canonical syntax

The Q1 and equality parameters are the prescribed pullbacks of successful
substitution. Q2 is the actual false equalizer of the occurrence classifier.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (V : PredicateCategory 𝗣𝗔)
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d
local notation "iv" => nameIso a V
local notation "it" => termIso a V σ π d
local notation "ifm" => formulaIso a V σ π d
local notation "ip" => parameterIso a V σ π d
local notation "ia" => admissibleIso a V σ π d

def formulaPairIso := SyntaxOptionTransport.productIso (E) (ifm) (ifm)
def formulaTripleIso := SyntaxOptionTransport.productIso (E) (formulaPairIso a V σ π d) (ifm)
def instantiationBaseIso := SyntaxOptionTransport.productIso (E) (iv)
  (SyntaxOptionTransport.productIso (E) (ifm) (it))
def distributionBaseIso := SyntaxOptionTransport.productIso (E) (iv) (formulaPairIso a V σ π d)
def equalityBaseIso := SyntaxOptionTransport.productIso (E)
  (SyntaxOptionTransport.productIso (E) (iv) (ifm)) (SyntaxOptionTransport.productIso (E) (it) (it))

theorem instantiationInput_comparison :
    (E).functor.map (S₁).instantiationInput ≫
        (SyntaxOptionTransport.productIso (E) (ifm) (ip)).hom =
      (instantiationBaseIso a V σ π d).hom ≫ (S₂).instantiationInput := by
  rw [parameterIso_product]
  exact ParameterGeometry.instantiation_square (E) (iv) (it) (ifm)


def instantiationIso : (E).functor.obj (S₁).instantiationParameters ≅ (S₂).instantiationParameters :=
  pullbackChart (E) (instantiationBaseIso a V σ π d) (ia)
    (SyntaxOptionTransport.productIso (E) (ifm) (ip))
    (S₁).instantiationInput (S₁).admissibleInclusion (S₂).instantiationInput (S₂).admissibleInclusion
    (instantiationInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

theorem instantiation_inclusion :
    (E).functor.map (S₁).instantiationInclusion ≫ (instantiationBaseIso a V σ π d).hom =
      (instantiationIso a V σ π d).hom ≫ (S₂).instantiationInclusion :=
  pullbackChart_fst (E) (instantiationBaseIso a V σ π d) (ia)
    (SyntaxOptionTransport.productIso (E) (ifm) (ip)) _ _ _ _
    (instantiationInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

theorem instantiation_admissible :
    (E).functor.map (S₁).instantiationAdmissible ≫ (ia).hom =
      (instantiationIso a V σ π d).hom ≫ (S₂).instantiationAdmissible :=
  pullbackChart_snd (E) (instantiationBaseIso a V σ π d) (ia)
    (SyntaxOptionTransport.productIso (E) (ifm) (ip)) _ _ _ _
    (instantiationInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

theorem distributionAbsence_comparison :
    (E).functor.map (S₁).distributionAbsence ≫
        (DecidableVariables.Transport.booleanIso (E)).hom =
      (distributionBaseIso a V σ π d).hom ≫ (S₂).distributionAbsence := by
  dsimp only [CategoricalSyntax.distributionAbsence, distributionBaseIso, formulaPairIso]
  apply square_comp («E» := (E)) (hg := membership_comparison a V σ π d)
  apply square_lift («E» := (E))
  · exact square_fst («E» := (E)) (iv) (formulaPairIso a V σ π d)
  · exact square_comp («E» := (E)) (square_snd («E» := (E)) (iv) (formulaPairIso a V σ π d))
      (square_comp («E» := (E)) (square_fst («E» := (E)) (ifm) (ifm))
        (formulaOccurrences_comparison a V σ π d))

def distributionIso : (E).functor.obj (S₁).distributionParameters ≅ (S₂).distributionParameters :=
  PreservesEqualizer.iso (E).functor (S₁).distributionAbsence (Two.constant _ false) ≪≫
    NumericalArithmetic.DistributionTransport.equalizerChart
      ((E).functor.map (S₁).distributionAbsence) ((E).functor.map (Two.constant _ false))
      (S₂).distributionAbsence (Two.constant _ false) (distributionBaseIso a V σ π d)
      (DecidableVariables.Transport.booleanIso (E))
      (distributionAbsence_comparison a V σ π d).symm (by
        rw [SyntaxOperationsTransport.map_constant, Two.comp_constant])

theorem distribution_inclusion :
    (E).functor.map (S₁).distributionInclusion ≫ (distributionBaseIso a V σ π d).hom =
      (distributionIso a V σ π d).hom ≫ (S₂).distributionInclusion := by
  symm
  simp only [distributionIso, Iso.trans_hom, CategoricalSyntax.distributionInclusion,
    Two.fiberι, Category.assoc, NumericalArithmetic.DistributionTransport.equalizerChart_inclusion]
  rw [← Category.assoc, PreservesEqualizer.iso_hom, equalizerComparison_comp_π]

theorem equalityFirstInput_comparison :
    (E).functor.map (S₁).equalityFirstInput ≫
        (SyntaxOptionTransport.productIso (E) (ifm) (ip)).hom =
      (equalityBaseIso a V σ π d).hom ≫ (S₂).equalityFirstInput := by
  rw [parameterIso_product]
  exact ParameterGeometry.equality_input_square (E) (iv) (it) (ifm)
    prod.fst prod.fst (square_fst («E» := (E)) (it) (it))


theorem equalitySecondInput_comparison :
    (E).functor.map (S₁).equalitySecondInput ≫
        (SyntaxOptionTransport.productIso (E) (ifm) (ip)).hom =
      (equalityBaseIso a V σ π d).hom ≫ (S₂).equalitySecondInput := by
  rw [parameterIso_product]
  exact ParameterGeometry.equality_input_square (E) (iv) (it) (ifm)
    prod.snd prod.snd (square_snd («E» := (E)) (it) (it))


def equalityFirstIso := pullbackChart (E) (equalityBaseIso a V σ π d) (ia)
  (SyntaxOptionTransport.productIso (E) (ifm) (ip))
  (S₁).equalityFirstInput (S₁).admissibleInclusion (S₂).equalityFirstInput (S₂).admissibleInclusion
  (equalityFirstInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

def equalitySecondIso := pullbackChart (E) (equalityBaseIso a V σ π d) (ia)
  (SyntaxOptionTransport.productIso (E) (ifm) (ip))
  (S₁).equalitySecondInput (S₁).admissibleInclusion (S₂).equalitySecondInput (S₂).admissibleInclusion
  (equalitySecondInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

theorem equalityFirst_fst :
    (E).functor.map (pullback.fst (S₁).equalityFirstInput (S₁).admissibleInclusion) ≫
        (equalityBaseIso a V σ π d).hom =
      (equalityFirstIso a V σ π d).hom ≫ pullback.fst (S₂).equalityFirstInput (S₂).admissibleInclusion :=
  pullbackChart_fst (E) (equalityBaseIso a V σ π d) (ia)
    (SyntaxOptionTransport.productIso (E) (ifm) (ip)) _ _ _ _
    (equalityFirstInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

theorem equalitySecond_fst :
    (E).functor.map (pullback.fst (S₁).equalitySecondInput (S₁).admissibleInclusion) ≫
        (equalityBaseIso a V σ π d).hom =
      (equalitySecondIso a V σ π d).hom ≫ pullback.fst (S₂).equalitySecondInput (S₂).admissibleInclusion :=
  pullbackChart_fst (E) (equalityBaseIso a V σ π d) (ia)
    (SyntaxOptionTransport.productIso (E) (ifm) (ip)) _ _ _ _
    (equalitySecondInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm

def equalitySchemeIso : (E).functor.obj (S₁).equalitySchemeParameters ≅ (S₂).equalitySchemeParameters :=
  pullbackChart (E) (equalityFirstIso a V σ π d) (equalitySecondIso a V σ π d)
    (equalityBaseIso a V σ π d) _ _ _ _ (equalityFirst_fst a V σ π d) (equalitySecond_fst a V σ π d)

theorem equality_inclusion :
    (E).functor.map (S₁).equalitySchemeInclusion ≫ (equalityBaseIso a V σ π d).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalitySchemeInclusion :=
  square_comp («E» := (E)) (pullbackChart_fst (E) (equalityFirstIso a V σ π d) (equalitySecondIso a V σ π d)
    (equalityBaseIso a V σ π d) _ _ _ _ (equalityFirst_fst a V σ π d) (equalitySecond_fst a V σ π d))
    (equalityFirst_fst a V σ π d)

theorem equality_first_admissible :
    (E).functor.map (S₁).equalityFirstAdmissible ≫ (ia).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalityFirstAdmissible :=
  square_comp («E» := (E)) (pullbackChart_fst (E) (equalityFirstIso a V σ π d) (equalitySecondIso a V σ π d)
    (equalityBaseIso a V σ π d) _ _ _ _ (equalityFirst_fst a V σ π d) (equalitySecond_fst a V σ π d))
    (pullbackChart_snd (E) (equalityBaseIso a V σ π d) (ia)
      (SyntaxOptionTransport.productIso (E) (ifm) (ip)) _ _ _ _
      (equalityFirstInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm)

theorem equality_second_admissible :
    (E).functor.map (S₁).equalitySecondAdmissible ≫ (ia).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).equalitySecondAdmissible :=
  square_comp («E» := (E)) (pullbackChart_snd (E) (equalityFirstIso a V σ π d) (equalitySecondIso a V σ π d)
    (equalityBaseIso a V σ π d) _ _ _ _ (equalityFirst_fst a V σ π d) (equalitySecond_fst a V σ π d))
    (pullbackChart_snd (E) (equalityBaseIso a V σ π d) (ia)
      (SyntaxOptionTransport.productIso (E) (ifm) (ip)) _ _ _ _
      (equalitySecondInput_comparison a V σ π d) (admissibleIso_inclusion a V σ π d).symm)

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
