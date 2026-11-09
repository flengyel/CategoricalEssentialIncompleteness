import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonOperations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable (a : Point) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "E" => Total.pointPresentation a
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (Uniform.Family.ofPoint a) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d
example : listIso a V σ π d=Iso.refl ((E).functor.obj (S₁).lists.algebra.carrier) :=
  listIso_eq_refl a V σ π d
example : (E).functor.map (S₁).termOccurrences≫(listIso a V σ π d).hom=
    (termIso a V σ π d).hom≫(S₂).termOccurrences := termOccurrences_comparison a V σ π d
example : (E).functor.map (S₁).formulaOccurrences ≫ (listIso a V σ π d).hom =
    (formulaIso a V σ π d).hom ≫ (S₂).formulaOccurrences := formulaOccurrences_comparison a V σ π d
example : (E).functor.map (S₁).lists.algebra.nil≫(listIso a V σ π d).hom=
    terminalComparison (E).functor≫(S₂).lists.algebra.nil := nil_comparison a V σ π d
example : (E).functor.map (S₁).termSubstitution≫(termIso a V σ π d).hom=
    (SyntaxOptionTransport.productIso (E) (termIso a V σ π d) (parameterIso a V σ π d)).hom≫
      (S₂).termSubstitution := termSubstitution_comparison a V σ π d
example : (E).functor.map (S₁).formulaSubstitutionOption ≫
      (SyntaxOptionTransport.optionIso (E) (formulaIso a V σ π d)).hom =
    (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d) (parameterIso a V σ π d)).hom ≫
      (S₂).formulaSubstitutionOption := formulaSubstitutionOption_comparison a V σ π d
example : (admissibleIso a V σ π d).hom ≫ (S₂).formulaSubstitution =
    (E).functor.map (S₁).formulaSubstitution ≫ (formulaIso a V σ π d).hom := admissibleIso_result a V σ π d
example : (S₂).admissibleSubstitution=pullback (S₂).formulaSubstitutionOption
    (coprod.inr : (S₂).algebra.a.2 ⟶ OptionSyntax.obj (S₂).algebra.a.2) := rfl
example : (admissibleIso a V σ π d).hom≫(S₂).admissibleInclusion=
    (E).functor.map (S₁).admissibleInclusion≫
      (SyntaxOptionTransport.productIso (E) (formulaIso a V σ π d) (parameterIso a V σ π d)).hom :=
  admissibleIso_inclusion a V σ π d
example : (E).functor.map (S₁).negationConstructor≫(formulaIso a V σ π d).hom=
    (formulaIso a V σ π d).hom≫(S₂).negationConstructor := negation_comparison a V σ π d
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
