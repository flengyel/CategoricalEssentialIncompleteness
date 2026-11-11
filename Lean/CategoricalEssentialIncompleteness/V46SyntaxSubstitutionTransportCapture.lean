/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportQuantifierCoordinates
public import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransport

/-! Capture transport uses the proved free-variable folds and the actual
membership diagram. The original body is the one tested for capture. -/

@[expose] public section
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

theorem substitution_membership_square {X A B : C} {X' A' B' : D}
    (k : E.functor.obj X ≅ X') (i : E.functor.obj A ≅ A') (j : E.functor.obj B ≅ B')
    (a : X ⟶ A) (b : X ⟶ B) (a' : X' ⟶ A') (b' : X' ⟶ B')
    (m : A ⨯ B ⟶ Two C) (m' : A' ⨯ B' ⟶ Two D)
    (ha : E.functor.map a ≫ i.hom = k.hom ≫ a')
    (hb : E.functor.map b ≫ j.hom = k.hom ≫ b')
    (hm : E.functor.map m ≫ (booleanIso E).hom =
      (SyntaxOptionTransport.productIso E i j).hom ≫ m') :
    E.functor.map (prod.lift a b ≫ m) ≫ (booleanIso E).hom =
      k.hom ≫ (prod.lift a' b' ≫ m') := by
  rw [E.functor.map_comp,Category.assoc,hm,← Category.assoc,SyntaxOptionTransport.map_lift,
    ha,hb,← prod.comp_lift,Category.assoc]

variable (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
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
theorem map_captureAllowed :
    E.functor.map S₀.captureAllowed ≫ (booleanIso E).hom =
      (substitutionQuantifierInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.captureAllowed := by
  let k := substitutionQuantifierInputIso E V σ π d S₀ S₁ c
  let e := E.counitIso.app V
  have hbody : E.functor.map
      (((prod.snd : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.snd ≫ prod.fst) ≫
          S₀.formulaOccurrences) ≫ ℓ.hom =
      k.hom ≫ (prod.snd ≫ prod.snd ≫ prod.fst ≫ S₁.formulaOccurrences) := by
    rw [E.functor.map_comp,Category.assoc,
      map_formulaOccurrences E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion c,
      ← Category.assoc,← substitutionQuantifierInput_originalBody,Category.assoc]
    simp only [Category.assoc]
    rfl
  have hreplacement : E.functor.map
      (((prod.fst : S₀.substitutionParameters ⨯
        (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.snd) ≫
          S₀.termOccurrences) ≫ ℓ.hom =
      k.hom ≫ (prod.fst ≫ prod.snd ≫ S₁.termOccurrences) := by
    rw [E.functor.map_comp,Category.assoc,
      map_termOccurrences E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion c,
      ← Category.assoc,← substitutionQuantifierInput_replacement,Category.assoc]
    simp only [Category.assoc]
    rfl
  have hm₀ := substitution_membership_square E k e ℓ
    ((prod.fst : S₀.substitutionParameters ⨯
      (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.fst)
    (prod.snd ≫ prod.snd ≫ prod.fst ≫ S₀.formulaOccurrences)
    (prod.fst ≫ prod.fst) (prod.snd ≫ prod.snd ≫ prod.fst ≫ S₁.formulaOccurrences)
    (S₀.lists.membership S₀.decidableVariables) (S₁.lists.membership S₁.decidableVariables)
    (substitutionQuantifierInput_query E V σ π d S₀ S₁ c).symm (by simpa only [Category.assoc] using hbody) hmembership
  have hm₁ := substitution_membership_square E k e ℓ
    ((prod.snd : S₀.substitutionParameters ⨯
      (E.inverse.obj V ⨯ S₀.substitutionCarriers.2) ⟶ _) ≫ prod.fst)
    (prod.fst ≫ prod.snd ≫ S₀.termOccurrences)
    (prod.snd ≫ prod.fst) (prod.fst ≫ prod.snd ≫ S₁.termOccurrences)
    (S₀.lists.membership S₀.decidableVariables) (S₁.lists.membership S₁.decidableVariables)
    (substitutionQuantifierInput_binder E V σ π d S₀ S₁ c).symm (by simpa only [Category.assoc] using hreplacement) hmembership
  unfold CategoricalSyntax.captureAllowed
  rw [map_boolean_binary E Bool.or,map_boolean_unary E Bool.not,map_boolean_unary E Bool.not,
    hm₀,hm₁,Two.comp_binary,Two.comp_unary,Two.comp_unary]
  rfl

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
