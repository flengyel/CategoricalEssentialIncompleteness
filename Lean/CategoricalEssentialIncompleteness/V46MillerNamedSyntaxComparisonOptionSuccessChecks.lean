import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptionSuccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
variable {W Y : C} {W' Y' : D} (i : F.obj W ≅ W') (j : F.obj Y ≅ Y')
variable (f : W ⟶ OptionSyntax.obj Y) (f' : W' ⟶ OptionSyntax.obj Y')
variable (hf : F.map f ≫ (Options.optionIso F j).hom=i.hom ≫ f')
example : IsPullback (F.map (pullback.fst f coprod.inr) ≫ i.hom)
    (F.map (pullback.snd f coprod.inr) ≫ j.hom) f' coprod.inr :=
  Options.success_isPullback F i j f f' hf
example : (Options.successIso F i j f f' hf).hom ≫ pullback.fst f' coprod.inr=
    F.map (pullback.fst f coprod.inr) ≫ i.hom := Options.successIso_fst F i j f f' hf
example : (Options.successIso F i j f f' hf).hom ≫ pullback.snd f' coprod.inr=
    F.map (pullback.snd f coprod.inr) ≫ j.hom := Options.successIso_snd F i j f f' hf
