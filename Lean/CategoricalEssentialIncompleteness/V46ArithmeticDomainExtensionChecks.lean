import CategoricalEssentialIncompleteness.V46ArithmeticDomainExtension

/-! # The actual canonical domain interpretation and source Γ range -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtension

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtensionChecks

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example {X Y : TotalSplit 𝗣𝗔} (f : X ⟶ Y) :
    (canonicalExtension M).toFunctor.map f.hom =
      (fun x => Part.some ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map f x)) :=
  canonical_map_total M f

example (Γ : Carrier) :
    (canonicalExtension M).mapIdem
      (Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom) =
      ArithmeticLiteralCoordinates.theory M Γ :=
  interpreted_theory M Γ

example :
    (canonicalExtension M).toFunctor.map
      ((realization 𝗣𝗔).map ArithmeticLiteralModel.negation).hom =
      ArithmeticLiteralCoordinates.negationMap M :=
  interpreted_negation M

example (Γ : Carrier)
    (h : ArithmeticLiteralCoordinates.theory M Γ ⊔
      Idem.pull (ArithmeticLiteralCoordinates.negationMap M)
        (ArithmeticLiteralCoordinates.theory M Γ) ≠ ⊤) :
    Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom ⊔
      Idem.pull ((realization 𝗣𝗔).map ArithmeticLiteralModel.negation).hom
        (Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom) ≠ ⊤ :=
  source_noncoverage M Γ h

end CategoricalEssentialIncompleteness.V46.ArithmeticDomainExtensionChecks
