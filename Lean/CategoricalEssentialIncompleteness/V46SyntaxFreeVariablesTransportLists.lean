/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransportInputs
public import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables

/-! # Ordered tuple and symbol-occurrence transport -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

omit [Regular C] [Regular D] in
theorem mapped_coprod_hom_ext {A B : C} {Z : D} {f g : E.functor.obj (A ⨿ B) ⟶ Z}
    (h₀ : E.functor.map (coprod.inl : A ⟶ A ⨿ B) ≫ f = E.functor.map coprod.inl ≫ g)
    (h₁ : E.functor.map (coprod.inr : B ⟶ A ⨿ B) ≫ f = E.functor.map coprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit E.functor A B) h₀ h₁

omit [Regular C] [Regular D] in
theorem copair_comparison {A B X : C} {A' B' Y : D}
    (a : E.functor.obj A ≅ A') (b : E.functor.obj B ≅ B') (ℓ : E.functor.obj X ≅ Y)
    (f₀ : A ⟶ X) (g₀ : B ⟶ X) (f₁ : A' ⟶ Y) (g₁ : B' ⟶ Y)
    (hf : E.functor.map f₀ ≫ ℓ.hom = a.hom ≫ f₁)
    (hg : E.functor.map g₀ ≫ ℓ.hom = b.hom ≫ g₁) :
    E.functor.map (coprod.desc f₀ g₀) ≫ ℓ.hom =
      (sumInputIso E a b).hom ≫ coprod.desc f₁ g₁ := by
  apply mapped_coprod_hom_ext E
  · rw [← Category.assoc,← E.functor.map_comp,coprod.inl_desc,hf]
    rw [← Category.assoc,sumInputIso_inl,Category.assoc,coprod.inl_desc]
  · rw [← Category.assoc,← E.functor.map_comp,coprod.inr_desc,hg]
    rw [← Category.assoc,sumInputIso_inr,Category.assoc,coprod.inr_desc]

variable {V₀ : C} {V₁ : D} (L₀ : StableListAlgebra V₀) (L₁ : StableListAlgebra V₁)
variable (ℓ : E.functor.obj L₀.algebra.carrier ≅ L₁.algebra.carrier)
variable (hnil : E.functor.map L₀.algebra.nil ≫ ℓ.hom = terminalComparison E.functor ≫ L₁.algebra.nil)
variable (happend : E.functor.map L₀.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ L₁.append)

include hnil happend in
/-- Every ordered finite tuple is concatenated compatibly; arity zero
uses the actual terminal comparison and arity one the given list iso. -/
theorem tupleAppend_comparison (n : ℕ) :
    E.functor.map (L₀.tupleAppend n) ≫ ℓ.hom =
      (powerInputIso E ℓ n).hom ≫ L₁.tupleAppend n := by
  induction n with
  | zero => simpa only [StableListAlgebra.tupleAppend,powerInputIso_zero] using hnil
  | succ n ih =>
    cases n with
    | zero => simp [StableListAlgebra.tupleAppend,powerInputIso_one]
    | succ n =>
      have hp : E.functor.map (prod.map (L₀.tupleAppend (n+1)) (𝟙 L₀.algebra.carrier)) ≫
          (SyntaxOptionTransport.productIso E ℓ ℓ).hom =
          (powerInputIso E ℓ (n+2)).hom ≫ prod.map (L₁.tupleAppend (n+1)) (𝟙 L₁.algebra.carrier) := by
        apply prod.hom_ext
        · calc
            _ = E.functor.map (prod.fst ≫ L₀.tupleAppend (n+1)) ≫ ℓ.hom := by
              rw [SyntaxOptionTransport.mapped_product_fst,prod.map_fst]
              rfl
            _ = E.functor.map prod.fst ≫ ((powerInputIso E ℓ (n+1)).hom ≫ L₁.tupleAppend (n+1)) := by
              rw [E.functor.map_comp,Category.assoc,ih]
            _ = ((powerInputIso E ℓ (n+2)).hom ≫ prod.fst) ≫ L₁.tupleAppend (n+1) := by
              rw [powerInputIso_fst,Category.assoc]
            _ = _ := by simp only [Category.assoc,prod.map_fst]
        · calc
            _ = E.functor.map prod.snd ≫ ℓ.hom := by
              rw [SyntaxOptionTransport.mapped_product_snd,prod.map_snd,Category.comp_id]
            _ = (powerInputIso E ℓ (n+2)).hom ≫ prod.snd := (powerInputIso_snd E ℓ n).symm
            _ = _ := by
              simp only [Category.assoc,prod.map_snd]
              simpa only [Category.assoc,SyntaxPolynomial.eval,CategoryTheory.Prod.fst_obj] using (Category.comp_id (obj := D) ((powerInputIso E ℓ (n+2)).hom ≫
                (prod.snd : (SyntaxPolynomial.power .term (n+1)).eval.obj
                  (L₁.algebra.carrier,L₁.algebra.carrier) ⨯ L₁.algebra.carrier ⟶ L₁.algebra.carrier))).symm
      change E.functor.map (prod.map (L₀.tupleAppend (n+1)) (𝟙 _) ≫ L₀.append) ≫ ℓ.hom =
        (powerInputIso E ℓ (n+2)).hom ≫ (prod.map (L₁.tupleAppend (n+1)) (𝟙 _) ≫ L₁.append)
      rw [E.functor.map_comp,Category.assoc,happend,← Category.assoc,hp,Category.assoc]
      rfl

include hnil happend in
theorem symbolOccurrences_comparison (A : D) (n : ℕ) :
    E.functor.map ((prod.snd : E.inverse.obj A ⨯
      (SyntaxPolynomial.power .term n).eval.obj (L₀.algebra.carrier,L₀.algebra.carrier) ⟶ _) ≫
        L₀.tupleAppend n) ≫ ℓ.hom =
      (symbolInputIso E ℓ A n).hom ≫ prod.snd ≫ L₁.tupleAppend n := by
  rw [E.functor.map_comp,Category.assoc,tupleAppend_comparison E L₀ L₁ ℓ hnil happend,
    symbolInputIso_snd_assoc]

include hnil happend in
/-- Coefficient labels are retained while their ordered child lists
are concatenated. No inverse for a numerical polynomial chart is assumed. -/
theorem constructorOccurrences_comparison (σ : ℕ → D) (n : ℕ) :
    E.functor.map (L₀.constructorOccurrences (fun k => E.inverse.obj (σ k)) n) ≫ ℓ.hom =
      (constructorInputIso E ℓ σ n).hom ≫ L₁.constructorOccurrences σ n := by
  induction n with
  | zero =>
      simpa only [StableListAlgebra.constructorOccurrences,constructorInputIso_zero,
        SyntaxPolynomial.constructors,SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,Functor.const_obj_obj] using
        symbolOccurrences_comparison E L₀ L₁ ℓ hnil happend (σ 0) 0
  | succ n ih =>
      apply mapped_coprod_hom_ext E
      · calc
          _ = E.functor.map (L₀.constructorOccurrences (fun k => E.inverse.obj (σ k)) n) ≫ ℓ.hom := by
            rw [← Category.assoc,← E.functor.map_comp,StableListAlgebra.constructorOccurrences,coprod.inl_desc]
          _ = (constructorInputIso E ℓ σ n).hom ≫ L₁.constructorOccurrences σ n := ih
          _ = _ := by
            rw [← Category.assoc,constructorInputIso_inl,Category.assoc,StableListAlgebra.constructorOccurrences,
              coprod.inl_desc]
      · calc
          _ = E.functor.map ((prod.snd : E.inverse.obj (σ (n+1)) ⨯
            (SyntaxPolynomial.power .term (n+1)).eval.obj (L₀.algebra.carrier,L₀.algebra.carrier) ⟶ _) ≫
              L₀.tupleAppend (n+1)) ≫ ℓ.hom := by
            rw [← Category.assoc,← E.functor.map_comp,StableListAlgebra.constructorOccurrences,coprod.inr_desc]
            rfl
          _ = (symbolInputIso E ℓ (σ (n+1)) (n+1)).hom ≫ prod.snd ≫ L₁.tupleAppend (n+1) :=
            symbolOccurrences_comparison E L₀ L₁ ℓ hnil happend _ _
          _ = _ := by
            erw [constructorInputIso_inr_assoc]
            simp only [StableListAlgebra.constructorOccurrences,coprod.inr_desc]
            rfl

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
