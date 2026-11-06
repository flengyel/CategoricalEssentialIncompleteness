import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportAlgebraFormula

/-! The actual two-sorted substitution algebra isomorphism. The only
operation premises concern the independently constructed lists; every
substitution branch equation has already been derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
local notation "P₀" => S₀.substitutionParameters
local notation "P₁" => S₁.substitutionParameters
local notation "b" => substitutionParameterIso E V σ π d S₀ S₁ c
local notation "H" => sliceEquivalence E b
local notation "a" => substitutionStateIso E V σ π d S₀ S₁ c
local notation "f" => substitutionFormulaStateIso E V σ π d S₀ S₁ c

variable (ℓ : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hnil : E.functor.map S₀.lists.algebra.nil ≫ ℓ.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)
variable (hsingleton : E.functor.map S₀.lists.singleton ≫ ℓ.hom =
  (E.counitIso.app V).hom ≫ S₁.lists.singleton)
variable (happend : E.functor.map S₀.lists.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ S₁.lists.append)
variable (hdeletion : E.functor.map (S₀.lists.deletion S₀.decidableVariables) ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
    S₁.lists.deletion S₁.decidableVariables)
variable (hmembership : E.functor.map (S₀.lists.membership S₀.decidableVariables) ≫
  (DecidableVariables.Transport.booleanIso E).hom =
    (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
      S₁.lists.membership S₁.decidableVariables)


include hnil hsingleton happend hdeletion hmembership in
def substitutionAlgebraIso :
    AlgebraTransport.mappedAlgebra ((H).prod H) (syntaxParameterLanguageIso E b V σ π d)
        S₀.substitutionAlgebra ≅ S₁.substitutionAlgebra := by
  let A := S₀.substitutionAlgebra
  let B := S₁.substitutionAlgebra
  let α := syntaxParameterLanguageIso E b V σ π d
  let i := substitutionFamilyPairIso E b S₀.substitutionCarriers S₁.substitutionCarriers a
  refine Endofunctor.Algebra.isoMk i ?_
  apply (cancel_epi (α.app A.a).hom).mp
  change (α.app A.a).hom ≫
      ((SyntaxPolynomial.jointFunctor
        ((SyntaxPolynomial.termExpression V σ d).withParameters P₁)
        ((SyntaxPolynomial.formulaExpression V π d).withParameters P₁)).map i.hom ≫ B.str) =
    (α.app A.a).hom ≫ (((α.app A.a).inv ≫ ((H).prod H).functor.map A.str) ≫ i.hom)
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  apply Prod.ext
  · change ((syntaxParameterLanguageIso E b V σ π d).hom.app
      (constantFamily P₀ S₀.substitutionCarriers.1,constantFamily P₀ S₀.substitutionCarriers.2)).1 ≫
        ((SyntaxPolynomial.termExpression V σ d).withParameters P₁).eval.map
          (substitutionFamilyPairIso E b S₀.substitutionCarriers S₁.substitutionCarriers a).hom ≫ B.str.1 =
      (H).functor.map A.str.1 ≫ (coefficientComparison E b S₀.substitutionCarriers.1
        S₁.substitutionCarriers.1 (substitutionTermStateIso E V σ π d S₀ S₁ c)).hom
    rw [syntaxParameterLanguageIso_fst_assoc]
    exact (substitutionTargetTerm_structure E V σ π d S₀ S₁ c).symm
  · change ((syntaxParameterLanguageIso E b V σ π d).hom.app
      (constantFamily P₀ S₀.substitutionCarriers.1,constantFamily P₀ S₀.substitutionCarriers.2)).2 ≫
        ((SyntaxPolynomial.formulaExpression V π d).withParameters P₁).eval.map
          (substitutionFamilyPairIso E b S₀.substitutionCarriers S₁.substitutionCarriers a).hom ≫ B.str.2 =
      (H).functor.map A.str.2 ≫ (coefficientComparison E b S₀.substitutionCarriers.2
        S₁.substitutionCarriers.2 f).hom
    rw [syntaxParameterLanguageIso_snd_assoc]
    exact (substitutionTargetFormula_structure E V σ π d S₀ S₁ c
      ℓ hnil hsingleton happend hdeletion hmembership).symm

include hnil hsingleton happend hdeletion hmembership in
/-- Initiality is applied to the mapped parameterized syntax itself.
Both compared arrows are actual algebra homomorphisms. -/
theorem substitutionFold_comparison :
    ((H).prod H).functor.map S₀.substitutionFold ≫
        (substitutionAlgebraIso E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership).hom.f =
      (syntaxParameterAlgebraIso E b V σ π d S₀ S₁ c).hom.f ≫ S₁.substitutionFold := by
  let α := syntaxParameterLanguageIso E b V σ π d
  let A := SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d)
    (SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d)
    S₀.algebra P₀
  let I := AlgebraTransport.initial ((H).prod H) α A (S₀.stable P₀)
  have h := I.hom_ext
    ((AlgebraTransport.functor ((H).prod H) α).map ((S₀.stable P₀).to S₀.substitutionAlgebra) ≫
      (substitutionAlgebraIso E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership).hom)
    ((syntaxParameterAlgebraIso E b V σ π d S₀ S₁ c).hom ≫
      (S₁.stable P₁).to S₁.substitutionAlgebra)
  exact congrArg Endofunctor.Algebra.Hom.f h

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
