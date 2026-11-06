import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportVariable

/-! The five coordinates of a quantified substitution input retain
the original body independently of its recursive option-valued result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

def substitutionQuantifierInputIso :
    E.functor.obj (S₀.substitutionParameters ⨯ (E.inverse.obj V ⨯ S₀.substitutionCarriers.2)) ≅
      S₁.substitutionParameters ⨯ (V ⨯ S₁.substitutionCarriers.2) :=
  SyntaxOptionTransport.productIso E (substitutionParameterIso E V σ π d S₀ S₁ c)
    (SyntaxOptionTransport.productIso E (E.counitIso.app V)
      (substitutionFormulaStateIso E V σ π d S₀ S₁ c))

theorem substitutionQuantifierInput_binder :
    (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ prod.snd ≫ prod.fst =
      E.functor.map ((prod.snd : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.fst) ≫
          (E.counitIso.app V).hom := by
  simp only [substitutionQuantifierInputIso,
    SyntaxOptionTransport.productIso_snd_assoc,SyntaxOptionTransport.productIso_fst,
    ← Functor.map_comp_assoc]

theorem substitutionQuantifierInput_query :
    (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ prod.fst ≫ prod.fst =
      E.functor.map ((prod.fst : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.fst) ≫
          (E.counitIso.app V).hom := by
  simp only [substitutionQuantifierInputIso,substitutionParameterIso,
    SyntaxOptionTransport.productIso_fst_assoc,SyntaxOptionTransport.productIso_fst,
    ← Functor.map_comp_assoc]

theorem substitutionQuantifierInput_replacement :
    (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ prod.fst ≫ prod.snd =
      E.functor.map ((prod.fst : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.snd) ≫
          (syntaxTermIso E V σ π d S₀ c).hom := by
  simp only [substitutionQuantifierInputIso,substitutionParameterIso,
    SyntaxOptionTransport.productIso_fst_assoc,SyntaxOptionTransport.productIso_snd,
    ← Functor.map_comp_assoc]

theorem substitutionQuantifierInput_originalBody :
    (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫
        prod.snd ≫ prod.snd ≫ prod.fst =
      E.functor.map ((prod.snd : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.snd ≫ prod.fst) ≫
          (syntaxFormulaIso E V σ π d S₀ c).hom := by
  simp only [substitutionQuantifierInputIso,substitutionFormulaStateIso,
    SyntaxOptionTransport.productIso_snd_assoc,SyntaxOptionTransport.productIso_fst,
    ← Functor.map_comp_assoc]

theorem substitutionQuantifierInput_bodyResult :
    (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫
        prod.snd ≫ prod.snd ≫ prod.snd =
      E.functor.map ((prod.snd : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.snd ≫ prod.snd) ≫
          (SyntaxOptionTransport.optionIso E (syntaxFormulaIso E V σ π d S₀ c)).hom := by
  simp only [substitutionQuantifierInputIso,substitutionFormulaStateIso,
    SyntaxOptionTransport.productIso_snd_assoc,SyntaxOptionTransport.productIso_snd,
    ← Functor.map_comp_assoc]

theorem map_quantifierEquality :
    E.functor.map S₀.quantifierEquality ≫ (booleanIso E).hom =
      (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.quantifierEquality := by
  let e := E.counitIso.app V
  let k := substitutionQuantifierInputIso E V σ π d S₀ S₁ c
  let a : S₀.substitutionParameters ⨯ (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶
      E.inverse.obj V ⨯ E.inverse.obj V :=
    prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ prod.fst)
  let a' : S₁.substitutionParameters ⨯ (V ⨯ S₁.substitutionCarriers.2) ⟶ V ⨯ V :=
    prod.lift (prod.snd ≫ prod.fst) (prod.fst ≫ prod.fst)
  have ha : E.functor.map a ≫ (SyntaxOptionTransport.productIso E e e).hom = k.hom ≫ a' := by
    change E.functor.map (prod.lift _ _) ≫ _ = _ ≫ prod.lift _ _
    rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
    exact congrArg₂ (fun x y => prod.lift x y)
      (substitutionQuantifierInput_binder E V σ π d S₀ S₁ c).symm
      (substitutionQuantifierInput_query E V σ π d S₀ S₁ c).symm
  have he := map_decidable_test E S₀.decidableVariables V e S₁.decidableVariables
  change E.functor.map S₀.decidableVariables.test ≫ (booleanIso E).hom =
    (SyntaxOptionTransport.productIso E e e).hom ≫ S₁.decidableVariables.test at he
  change E.functor.map (a ≫ S₀.decidableVariables.test) ≫ _ =
    k.hom ≫ (a' ≫ S₁.decidableVariables.test)
  rw [E.functor.map_comp,Category.assoc,he,← Category.assoc,ha,Category.assoc]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
