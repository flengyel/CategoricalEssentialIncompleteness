import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportCapture
import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsFormula

/-! The quantified substitution branch commutes with the equivalence.
The equal-name branch is transported as the original quantified body,
independently of the recursive body's option-valued result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

theorem substitution_branch_square {X Y : C} {X' Y' : D}
    (k : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')
    (χ : X ⟶ Two C) (χ' : X' ⟶ Two D)
    (f g : X ⟶ Y) (f' g' : X' ⟶ Y')
    (hχ : E.functor.map χ ≫ (booleanIso E).hom = k.hom ≫ χ')
    (hf : E.functor.map f ≫ j.hom = k.hom ≫ f')
    (hg : E.functor.map g ≫ j.hom = k.hom ≫ g') :
    E.functor.map (Two.branch χ f g) ≫ j.hom = k.hom ≫ Two.branch χ' f' g' := by
  rw [map_branch E,transport_branch_postcomp,hχ,hf,hg,branch_precomp]

variable (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

theorem map_quantifierOriginal :
    E.functor.map S₀.quantifierOriginal ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.quantifierOriginal := by
  let k := substitutionQuantifierInputIso E V σ π d S₀ S₁ c
  let f := syntaxFormulaIso E V σ π d S₀ c
  have hp : E.functor.map
      (prod.lift (prod.snd ≫ prod.fst)
        (prod.snd ≫ prod.snd ≫ prod.fst) :
        S₀.substitutionParameters ⨯ (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫
      (SyntaxOptionTransport.productIso E (E.counitIso.app V) f).hom =
      k.hom ≫ prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst) := by
    rw [SyntaxOptionTransport.map_lift,prod.comp_lift,
      substitutionQuantifierInput_binder,substitutionQuantifierInput_originalBody]
    rfl
  change E.functor.map (_ ≫ S₀.quantifierConstructor) ≫ (f).hom =
    k.hom ≫ (_ ≫ S₁.quantifierConstructor)
  rw [E.functor.map_comp,Category.assoc,syntax_quantifier_constructor,
    ← Category.assoc,hp,Category.assoc]

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
  (booleanIso E).hom = (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
    S₁.lists.membership S₁.decidableVariables)

include hnil hsingleton happend hdeletion hmembership in
theorem map_quantifierSubstitutionResult :
    E.functor.map S₀.quantifierSubstitutionResult ≫
        (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c)).hom =
      (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.quantifierSubstitutionResult := by
  let k := substitutionQuantifierInputIso E V σ π d S₀ S₁ c
  let f := syntaxFormulaIso E V σ π d S₀ c
  let o := SyntaxOptionTransport.optionIso E f
  let a : S₀.substitutionParameters ⨯ (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶
      E.inverse.obj V ⨯ OptionSyntax.obj S₀.algebra.a.2 :=
    prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd)
  let a' : S₁.substitutionParameters ⨯ (V ⨯ S₁.substitutionCarriers.2) ⟶
      V ⨯ OptionSyntax.obj S₁.algebra.a.2 :=
    prod.lift (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.snd)
  have ha : E.functor.map a ≫
      (SyntaxOptionTransport.productIso E (E.counitIso.app V) o).hom = k.hom ≫ a' := by
    change E.functor.map (prod.lift _ _) ≫ _ = _ ≫ prod.lift _ _
    rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
    exact congrArg₂ (fun x y => prod.lift x y)
      (substitutionQuantifierInput_binder E V σ π d S₀ S₁ c).symm
      (substitutionQuantifierInput_bodyResult E V σ π d S₀ S₁ c).symm
  have hcoef : E.functor.map (a ≫ OptionSyntax.coefficient S₀.quantifierConstructor) ≫ o.hom =
      k.hom ≫ (a' ≫ OptionSyntax.coefficient S₁.quantifierConstructor) := by
    rw [E.functor.map_comp,Category.assoc,
      SyntaxOptionTransport.map_coefficient E (E.counitIso.app V) f f
        S₀.quantifierConstructor S₁.quantifierConstructor
        (syntax_quantifier_constructor E V σ π d S₀ S₁ c),
      ← Category.assoc,ha,Category.assoc]
  have hfail : E.functor.map (OptionSyntax.fail :
      S₀.substitutionParameters ⨯ (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶
        OptionSyntax.obj S₀.algebra.a.2) ≫ o.hom = k.hom ≫ OptionSyntax.fail := by
    rw [SyntaxOptionTransport.map_fail]
    simp only [OptionSyntax.fail,← Category.assoc,terminal.comp_from]
  have hinner := substitution_branch_square E k o S₀.captureAllowed S₁.captureAllowed
    OptionSyntax.fail (a ≫ OptionSyntax.coefficient S₀.quantifierConstructor)
    OptionSyntax.fail (a' ≫ OptionSyntax.coefficient S₁.quantifierConstructor)
    (map_captureAllowed E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership)
    hfail hcoef
  have hold : E.functor.map (S₀.quantifierOriginal ≫ coprod.inr) ≫ o.hom =
      k.hom ≫ (S₁.quantifierOriginal ≫ coprod.inr) := by
    rw [SyntaxOptionTransport.map_some,map_quantifierOriginal,Category.assoc]
  exact substitution_branch_square E k o S₀.quantifierEquality S₁.quantifierEquality _ _ _ _
    (map_quantifierEquality E V σ π d S₀ S₁ c) hinner hold

include hnil hsingleton happend hdeletion hmembership in
theorem map_quantifierSubstitutionPair :
    E.functor.map S₀.quantifierSubstitutionPair ≫
        (substitutionFormulaStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.quantifierSubstitutionPair := by
  change E.functor.map (prod.lift _ _) ≫
    (SyntaxOptionTransport.productIso E (syntaxFormulaIso E V σ π d S₀ c)
      (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c))).hom =
    _ ≫ prod.lift _ _
  rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
  exact congrArg₂ (fun f g => prod.lift f g)
    (map_quantifierOriginal E V σ π d S₀ S₁ c)
    (map_quantifierSubstitutionResult E V σ π d S₀ S₁ c ℓ hnil hsingleton happend hdeletion hmembership)

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
