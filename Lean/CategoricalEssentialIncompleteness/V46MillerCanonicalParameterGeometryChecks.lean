import CategoricalEssentialIncompleteness.V46MillerCanonicalParameterGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.ParameterGeometryChecks
open CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.ParameterGeometry
open CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D]
variable (E : C ≌ D) {V T A : C} {V' T' A' : D}
variable (iv : E.functor.obj V ≅ V') (it : E.functor.obj T ≅ T') (ia : E.functor.obj A ≅ A')
example :
    E.functor.map (prod.lift (prod.snd ≫ prod.fst)
        (prod.lift (prod.fst : V ⨯ (A ⨯ T) ⟶ V) (prod.snd ≫ prod.snd))) ≫
      (SyntaxOptionTransport.productIso E ia (SyntaxOptionTransport.productIso E iv it)).hom =
    (SyntaxOptionTransport.productIso E iv (SyntaxOptionTransport.productIso E ia it)).hom ≫
      prod.lift (prod.snd ≫ prod.fst)
        (prod.lift (prod.fst : V' ⨯ (A' ⨯ T') ⟶ V') (prod.snd ≫ prod.snd)) := instantiation_square E iv it ia

example (p : T ⨯ T ⟶ T) (p' : T' ⨯ T' ⟶ T')
    (hp : E.functor.map p ≫ it.hom=(SyntaxOptionTransport.productIso E it it).hom ≫ p') :
    E.functor.map (prod.lift (prod.fst ≫ prod.snd)
        (prod.lift (prod.fst ≫ prod.fst : (V ⨯ A) ⨯ (T ⨯ T) ⟶ V) (prod.snd ≫ p))) ≫
      (SyntaxOptionTransport.productIso E ia (SyntaxOptionTransport.productIso E iv it)).hom =
    (SyntaxOptionTransport.productIso E (SyntaxOptionTransport.productIso E iv ia)
      (SyntaxOptionTransport.productIso E it it)).hom ≫
      prod.lift (prod.fst ≫ prod.snd)
        (prod.lift (prod.fst ≫ prod.fst : (V' ⨯ A') ⨯ (T' ⨯ T') ⟶ V') (prod.snd ≫ p')) := equality_input_square E iv it ia p p' hp

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.ParameterGeometryChecks
