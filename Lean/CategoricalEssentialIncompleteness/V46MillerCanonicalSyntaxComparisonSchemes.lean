import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonParameters

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

theorem hilbertOne_comparison :
    (E).functor.map (S₁).hilbertOne ≫ (ifm).hom =
      (formulaPairIso a V σ π d).hom ≫ (S₂).hilbertOne := by
  dsimp only [CategoricalSyntax.hilbertOne, formulaPairIso]
  exact square_comp («E» := (E)) (square_lift («E» := (E)) (square_fst («E» := (E)) _ _)
    (square_comp («E» := (E)) (square_lift («E» := (E)) (square_snd («E» := (E)) _ _) (square_fst («E» := (E)) _ _))
      (implication_comparison a V σ π d))) (implication_comparison a V σ π d)

theorem hilbertTwo_comparison :
    (E).functor.map (S₁).hilbertTwo ≫ (ifm).hom =
      (formulaTripleIso a V σ π d).hom ≫ (S₂).hilbertTwo := by
  dsimp only [CategoricalSyntax.hilbertTwo]
  have hpair := square_fst («E» := (E)) (formulaPairIso a V σ π d) (ifm)
  have hchi := square_snd («E» := (E)) (formulaPairIso a V σ π d) (ifm)
  have hphi := square_comp («E» := (E)) hpair (square_fst («E» := (E)) (ifm) (ifm))
  have hpsi := square_comp («E» := (E)) hpair (square_snd («E» := (E)) (ifm) (ifm))
  have himp := implication_comparison a V σ π d
  have hpsiChi := square_comp («E» := (E)) (square_lift («E» := (E)) hpsi hchi) himp
  have hleft := square_comp («E» := (E)) (square_lift («E» := (E)) hphi hpsiChi) himp
  have hphiPsi := square_comp («E» := (E)) hpair himp
  have hphiChi := square_comp («E» := (E)) (square_lift («E» := (E)) hphi hchi) himp
  have hright := square_comp («E» := (E)) (square_lift («E» := (E)) hphiPsi hphiChi) himp
  exact square_comp («E» := (E)) (square_lift («E» := (E)) hleft hright) himp

theorem hilbertThree_comparison :
    (E).functor.map (S₁).hilbertThree ≫ (ifm).hom =
      (formulaPairIso a V σ π d).hom ≫ (S₂).hilbertThree := by
  dsimp only [CategoricalSyntax.hilbertThree]
  have hphi := square_fst («E» := (E)) (ifm) (ifm)
  have hpsi := square_snd («E» := (E)) (ifm) (ifm)
  have hneg := negation_comparison a V σ π d
  have himp := implication_comparison a V σ π d
  have hnotPsi := square_comp («E» := (E)) hpsi hneg
  have hnotPhi := square_comp («E» := (E)) hphi hneg
  have hleft := square_comp («E» := (E)) (square_lift («E» := (E)) hnotPsi hnotPhi) himp
  exact square_comp («E» := (E)) (square_lift («E» := (E)) hleft himp) himp

theorem hilbertInstantiation_comparison :
    (E).functor.map (S₁).hilbertInstantiation ≫ (ifm).hom =
      (instantiationIso a V σ π d).hom ≫ (S₂).hilbertInstantiation := by
  dsimp only [CategoricalSyntax.hilbertInstantiation]
  apply square_comp («E» := (E)) (hg := implication_comparison a V σ π d)
  apply square_lift («E» := (E))
  · apply square_comp («E» := (E)) (hg := quantifier_comparison a V σ π d)
    exact square_lift («E» := (E)) (square_comp («E» := (E)) (instantiation_inclusion a V σ π d) (square_fst («E» := (E)) _ _))
      (square_comp («E» := (E)) (instantiation_inclusion a V σ π d)
        (square_comp («E» := (E)) (square_snd («E» := (E)) _ _) (square_fst («E» := (E)) _ _)))
  · exact square_comp («E» := (E)) (instantiation_admissible a V σ π d) (admissibleIso_result a V σ π d).symm

theorem hilbertDistribution_comparison :
    (E).functor.map (S₁).hilbertDistribution ≫ (ifm).hom =
      (distributionIso a V σ π d).hom ≫ (S₂).hilbertDistribution := by
  dsimp only [CategoricalSyntax.hilbertDistribution]
  have hname := square_fst («E» := (E)) (iv) (formulaPairIso a V σ π d)
  have hpair := square_snd («E» := (E)) (iv) (formulaPairIso a V σ π d)
  have hphi := square_comp («E» := (E)) hpair (square_fst («E» := (E)) (ifm) (ifm))
  have hpsi := square_comp («E» := (E)) hpair (square_snd («E» := (E)) (ifm) (ifm))
  have himp := implication_comparison a V σ π d
  have hall := quantifier_comparison a V σ π d
  have hphiPsi := square_comp («E» := (E)) hpair himp
  have hleft := square_comp («E» := (E)) (square_lift («E» := (E)) hname hphiPsi) hall
  have hallPsi := square_comp («E» := (E)) (square_lift («E» := (E)) hname hpsi) hall
  have hright := square_comp («E» := (E)) (square_lift («E» := (E)) hphi hallPsi) himp
  have hbody := square_comp («E» := (E)) (square_lift («E» := (E)) hleft hright) himp
  exact square_comp («E» := (E)) (distribution_inclusion a V σ π d) hbody

theorem hilbertReflexivity_comparison :
    (E).functor.map (S₁).hilbertReflexivity ≫ (ifm).hom =
      (it).hom ≫ (S₂).hilbertReflexivity := by
  dsimp only [CategoricalSyntax.hilbertReflexivity]
  exact square_comp («E» := (E)) (square_lift («E» := (E)) (square_id («E» := (E)) _) (square_id («E» := (E)) _)) (equality_comparison a V σ π d)

theorem hilbertEquality_comparison :
    (E).functor.map (S₁).hilbertEquality ≫ (ifm).hom =
      (equalitySchemeIso a V σ π d).hom ≫ (S₂).hilbertEquality := by
  dsimp only [CategoricalSyntax.hilbertEquality]
  apply square_comp («E» := (E)) (hg := implication_comparison a V σ π d)
  apply square_lift («E» := (E))
  · exact square_comp («E» := (E)) (equality_inclusion a V σ π d)
      (square_comp («E» := (E)) (square_snd («E» := (E)) _ _) (equality_comparison a V σ π d))
  · exact square_comp («E» := (E)) (square_lift («E» := (E))
      (square_comp («E» := (E)) (equality_first_admissible a V σ π d) (admissibleIso_result a V σ π d).symm)
      (square_comp («E» := (E)) (equality_second_admissible a V σ π d) (admissibleIso_result a V σ π d).symm))
      (implication_comparison a V σ π d)

def logicalParametersIso : (E).functor.obj (S₁).logicalParameters ≅ (S₂).logicalParameters :=
  SyntaxOperationsTransport.sumInputIso (E)
    (SyntaxOperationsTransport.sumInputIso (E)
      (SyntaxOperationsTransport.sumInputIso (E)
        (SyntaxOperationsTransport.sumInputIso (E)
          (SyntaxOperationsTransport.sumInputIso (E)
            (SyntaxOperationsTransport.sumInputIso (E) (formulaPairIso a V σ π d)
              (formulaTripleIso a V σ π d)) (formulaPairIso a V σ π d))
            (instantiationIso a V σ π d)) (distributionIso a V σ π d)) (it))
    (equalitySchemeIso a V σ π d)

theorem logicalAxioms_comparison :
    (E).functor.map (S₁).logicalAxioms ≫ (ifm).hom =
      (logicalParametersIso a V σ π d).hom ≫ (S₂).logicalAxioms := by
  dsimp only [CategoricalSyntax.logicalAxioms, logicalParametersIso]
  exact square_desc («E» := (E)) _ _ _
    (square_desc («E» := (E)) _ _ _
      (square_desc («E» := (E)) _ _ _
        (square_desc («E» := (E)) _ _ _
          (square_desc («E» := (E)) _ _ _
            (square_desc («E» := (E)) _ _ _ (hilbertOne_comparison a V σ π d) (hilbertTwo_comparison a V σ π d))
            (hilbertThree_comparison a V σ π d)) (hilbertInstantiation_comparison a V σ π d))
          (hilbertDistribution_comparison a V σ π d)) (hilbertReflexivity_comparison a V σ π d))
    (hilbertEquality_comparison a V σ π d)
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
