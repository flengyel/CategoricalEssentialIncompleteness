import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsCore
import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportBooleans

/-! The named-variable branch is transported with the actual equality
classifier and both coordinates of the substitution parameter. -/
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

def substitutionVariableInputIso :
    E.functor.obj (S₀.substitutionParameters ⨯ E.inverse.obj V) ≅
      S₁.substitutionParameters ⨯ V :=
  SyntaxOptionTransport.productIso E (substitutionParameterIso E V σ π d S₀ S₁ c)
    (E.counitIso.app V)

theorem map_variableSubstitutionPair :
    E.functor.map S₀.variableSubstitutionPair ≫
        (substitutionTermStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionVariableInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.variableSubstitutionPair := by
  let e := E.counitIso.app V
  let t := syntaxTermIso E V σ π d S₀ c
  let k := substitutionVariableInputIso E V σ π d S₀ S₁ c
  let a : S₀.substitutionParameters ⨯ E.inverse.obj V ⟶ E.inverse.obj V ⨯ E.inverse.obj V :=
    prod.lift prod.snd (prod.fst ≫ prod.fst)
  let a' : S₁.substitutionParameters ⨯ V ⟶ V ⨯ V :=
    prod.lift prod.snd (prod.fst ≫ prod.fst)
  let χ := a ≫ S₀.decidableVariables.test
  let χ' := a' ≫ S₁.decidableVariables.test
  have hchild : k.hom ≫ prod.snd = E.functor.map prod.snd ≫ e.hom :=
    SyntaxOptionTransport.productIso_snd E _ _
  have hquery : k.hom ≫ prod.fst ≫ prod.fst =
      E.functor.map ((prod.fst : S₀.substitutionParameters ⨯ E.inverse.obj V ⟶ _) ≫ prod.fst) ≫
        e.hom := by
    calc
      _ = E.functor.map prod.fst ≫
          (substitutionParameterIso E V σ π d S₀ S₁ c).hom ≫ prod.fst :=
        SyntaxOptionTransport.productIso_fst_assoc E (substitutionParameterIso E V σ π d S₀ S₁ c) e _
      _ = E.functor.map prod.fst ≫ E.functor.map prod.fst ≫ e.hom :=
        congrArg (fun z => E.functor.map prod.fst ≫ z) (SyntaxOptionTransport.productIso_fst E e t)
      _ = _ := by
        rw [E.functor.map_comp,Category.assoc]
        rfl
  have hreplacement : k.hom ≫ prod.fst ≫ prod.snd =
      E.functor.map ((prod.fst : S₀.substitutionParameters ⨯ E.inverse.obj V ⟶ _) ≫ prod.snd) ≫
        (t).hom := by
    calc
      _ = E.functor.map prod.fst ≫
          (substitutionParameterIso E V σ π d S₀ S₁ c).hom ≫ prod.snd :=
        SyntaxOptionTransport.productIso_fst_assoc E (substitutionParameterIso E V σ π d S₀ S₁ c) e _
      _ = E.functor.map prod.fst ≫ E.functor.map prod.snd ≫ (t).hom :=
        congrArg (fun z => E.functor.map prod.fst ≫ z) (SyntaxOptionTransport.productIso_snd E e t)
      _ = _ := by
        rw [E.functor.map_comp,Category.assoc]
        rfl
  have ha : E.functor.map a ≫ (SyntaxOptionTransport.productIso E e e).hom = k.hom ≫ a' := by
    change E.functor.map (prod.lift _ _) ≫ _ = _ ≫ prod.lift _ _
    rw [SyntaxOptionTransport.map_lift,prod.comp_lift,hchild,hquery]
  have he := map_decidable_test E S₀.decidableVariables V e S₁.decidableVariables
  change E.functor.map S₀.decidableVariables.test ≫ (booleanIso E).hom =
    (SyntaxOptionTransport.productIso E e e).hom ≫ S₁.decidableVariables.test at he
  have hχ : E.functor.map χ ≫ (booleanIso E).hom = k.hom ≫ χ' := by
    change E.functor.map (a ≫ S₀.decidableVariables.test) ≫ _ = k.hom ≫
      (a' ≫ S₁.decidableVariables.test)
    rw [E.functor.map_comp,Category.assoc,he,← Category.assoc,ha,Category.assoc]
  have hold : E.functor.map
      ((prod.snd : S₀.substitutionParameters ⨯ E.inverse.obj V ⟶ _) ≫ S₀.variableConstructor) ≫
        (t).hom = k.hom ≫ prod.snd ≫ S₁.variableConstructor := by
    rw [E.functor.map_comp,Category.assoc,syntax_variable_constructor,
      ← Category.assoc,← hchild,Category.assoc]
  have hresult : E.functor.map
      (Two.branch χ (prod.snd ≫ S₀.variableConstructor) (prod.fst ≫ prod.snd)) ≫ (t).hom =
      k.hom ≫ Two.branch χ' (prod.snd ≫ S₁.variableConstructor) (prod.fst ≫ prod.snd) := by
    rw [map_branch E,transport_branch_postcomp,hχ,hold,← hreplacement,branch_precomp]
  change E.functor.map (prod.lift _ _) ≫ (SyntaxOptionTransport.productIso E t t).hom =
    k.hom ≫ prod.lift _ _
  rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
  exact congrArg₂ (fun f g => prod.lift f g) hold hresult

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
