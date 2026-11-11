/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonSquares


/-! # Definitions and theorems in `V46MillerCanonicalParameterGeometry` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.ParameterGeometry
open CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D]
variable (E : C ≌ D) {V T A : C} {V' T' A' : D}
variable (iv : E.functor.obj V ≅ V') (it : E.functor.obj T ≅ T') (ia : E.functor.obj A ≅ A')
theorem instantiation_square :
    E.functor.map (prod.lift (prod.snd ≫ prod.fst)
        (prod.lift (prod.fst : V ⨯ (A ⨯ T) ⟶ V) (prod.snd ≫ prod.snd))) ≫
      (SyntaxOptionTransport.productIso E ia (SyntaxOptionTransport.productIso E iv it)).hom =
    (SyntaxOptionTransport.productIso E iv (SyntaxOptionTransport.productIso E ia it)).hom ≫
      prod.lift (prod.snd ≫ prod.fst)
        (prod.lift (prod.fst : V' ⨯ (A' ⨯ T') ⟶ V') (prod.snd ≫ prod.snd)) := by
  have hv := square_fst (E := E) iv (SyntaxOptionTransport.productIso E ia it)
  have hr := square_snd (E := E) iv (SyntaxOptionTransport.productIso E ia it)
  have ha := square_comp (E := E) hr (square_fst (E := E) ia it)
  have ht := square_comp (E := E) hr (square_snd (E := E) ia it)
  exact square_lift (E := E) ha (square_lift (E := E) hv ht)

theorem equality_input_square (p : T ⨯ T ⟶ T) (p' : T' ⨯ T' ⟶ T')
    (hp : E.functor.map p ≫ it.hom=(SyntaxOptionTransport.productIso E it it).hom ≫ p') :
    E.functor.map (prod.lift (prod.fst ≫ prod.snd)
        (prod.lift (prod.fst ≫ prod.fst : (V ⨯ A) ⨯ (T ⨯ T) ⟶ V) (prod.snd ≫ p))) ≫
      (SyntaxOptionTransport.productIso E ia (SyntaxOptionTransport.productIso E iv it)).hom =
    (SyntaxOptionTransport.productIso E (SyntaxOptionTransport.productIso E iv ia)
      (SyntaxOptionTransport.productIso E it it)).hom ≫
      prod.lift (prod.fst ≫ prod.snd)
        (prod.lift (prod.fst ≫ prod.fst : (V' ⨯ A') ⨯ (T' ⨯ T') ⟶ V') (prod.snd ≫ p')) := by
  have hl := square_fst (E := E) (SyntaxOptionTransport.productIso E iv ia)
    (SyntaxOptionTransport.productIso E it it)
  have hr := square_snd (E := E) (SyntaxOptionTransport.productIso E iv ia)
    (SyntaxOptionTransport.productIso E it it)
  have hv := square_comp (E := E) hl (square_fst (E := E) iv ia)
  have ha := square_comp (E := E) hl (square_snd (E := E) iv ia)
  have ht := square_comp (E := E) hr hp
  exact square_lift (E := E) ha (square_lift (E := E) hv ht)

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.ParameterGeometry
