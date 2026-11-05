/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Inference
import CategoricalEssentialIncompleteness.V46CategoricalSyntax
import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! # Finite rule coproducts and the ordered constructor polynomial -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PolynomialComparison
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]

def finiteSum (σ : ℕ → D) (N : ℕ) : D ⥤ D where
  obj X := ∐ (fun i : Fin (N + 1) => σ i.val ⨯ finitePower X i.val)
  map f := Limits.Sigma.map (fun i => prod.map (𝟙 (σ i.val)) (finitePowerMap f i.val))
  map_id X := by
    apply Sigma.hom_ext
    intro i
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro i
    simp [finitePowerMap_comp]

def nested (σ : ℕ → D) (N : ℕ) : D ⥤ D :=
  ((𝟭 D).prod' ((Functor.const D).obj (⊤_ D))) ⋙
    (SyntaxPolynomial.constructors σ N).eval

def powerIso (X : D) : (n : ℕ) → finitePower X n ≅
    (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.obj (X, ⊤_ D)
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | n + 2 => prod.mapIso (powerIso X (n + 1)) (Iso.refl X)

theorem powerIso_natural {X Y : D} (f : X ⟶ Y) (n : ℕ) :
    finitePowerMap f n ≫ (powerIso Y n).hom =
      (powerIso X n).hom ≫
        (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.map
          ((f, 𝟙 (⊤_ D)) : (X, ⊤_ D) ⟶ (Y, ⊤_ D)) := by
  induction n with
  | zero => simp [finitePowerMap, powerIso, SyntaxPolynomial.power, SyntaxPolynomial.eval]
  | succ n ih =>
      cases n with
      | zero => simp [finitePowerMap, powerIso, SyntaxPolynomial.power, SyntaxPolynomial.eval]
      | succ n =>
          change prod.map (finitePowerMap f (n + 1)) f ≫
            prod.map (powerIso Y (n + 1)).hom (𝟙 Y) =
              prod.map (powerIso X (n + 1)).hom (𝟙 X) ≫
                prod.map ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) (n + 1)).eval.map
                  ((f, 𝟙 (⊤_ D)) : (X, ⊤_ D) ⟶ (Y, ⊤_ D))) f
          simp only [prod.map_map, Category.comp_id, Category.id_comp, ih]

def summandIso (σ : ℕ → D) (X : D) (n : ℕ) :
    σ n ⨯ finitePower X n ≅
      σ n ⨯ (SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.obj (X, ⊤_ D) :=
  prod.mapIso (Iso.refl _) (powerIso X n)

theorem summandIso_natural (σ : ℕ → D) {X Y : D} (f : X ⟶ Y) (n : ℕ) :
    prod.map (𝟙 (σ n)) (finitePowerMap f n) ≫ (summandIso σ Y n).hom =
      (summandIso σ X n).hom ≫
        prod.map (𝟙 (σ n))
          ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) n).eval.map
            ((f, 𝟙 (⊤_ D)) : (X, ⊤_ D) ⟶ (Y, ⊤_ D))) := by
  change prod.map (𝟙 _) _ ≫ prod.map (𝟙 _) _ = prod.map (𝟙 _) _ ≫ prod.map (𝟙 _) _
  simp only [prod.map_map, Category.id_comp, powerIso_natural]

def injection (σ : ℕ → D) (X : D) : (N : ℕ) → (i : Fin (N + 1)) →
    σ i.val ⨯ finitePower X i.val ⟶ (nested σ N).obj X
  | 0, i => by
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact 𝟙 _
  | N + 1, i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact (summandIso σ X (N + 1)).hom ≫ coprod.inr
      · exact injection σ X N j ≫ coprod.inl

def descend (σ : ℕ → D) (X : D) : (N : ℕ) → {Y : D} →
    (∀ i : Fin (N + 1), σ i.val ⨯ finitePower X i.val ⟶ Y) → ((nested σ N).obj X ⟶ Y)
  | 0, _, w => w 0
  | N + 1, _, w => coprod.desc
      (descend σ X N (fun i => w i.castSucc))
      ((summandIso σ X (N + 1)).inv ≫ w (Fin.last (N + 1)))

@[simp, reassoc] theorem injection_descend (σ : ℕ → D) (X : D) (N : ℕ)
    {Y : D} (w : ∀ i : Fin (N + 1), σ i.val ⨯ finitePower X i.val ⟶ Y)
    (i : Fin (N + 1)) : injection σ X N i ≫ descend σ X N w = w i := by
  induction N with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp [injection, descend]
  | succ N ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [injection, descend, Fin.lastCases_last, Fin.val_last, Category.assoc,
          coprod.inr_desc, Iso.hom_inv_id_assoc]
      · simp only [injection, descend, Fin.lastCases_castSucc, Fin.val_castSucc,
          Category.assoc, coprod.inl_desc]
        exact ih (fun k => w k.castSucc) j

theorem hom_ext (σ : ℕ → D) (X : D) (N : ℕ) {Y : D}
    (f g : (nested σ N).obj X ⟶ Y)
    (h : ∀ i, injection σ X N i ≫ f = injection σ X N i ≫ g) : f = g := by
  induction N with
  | zero => simpa [injection] using h 0
  | succ N ih =>
      apply coprod.hom_ext
      · apply ih
        intro i
        simpa [injection, nested, SyntaxPolynomial.constructors, SyntaxPolynomial.eval,
          SyntaxPolynomial.sumFunctor, Fin.val_castSucc, Category.assoc] using h i.castSucc
      · have hl := h (Fin.last (N + 1))
        simp only [injection, Fin.lastCases_last, Fin.val_last, Category.assoc] at hl
        change (summandIso σ X (N + 1)).hom ≫
          (coprod.inr : _ ⟶ (nested σ (N + 1)).obj X) ≫ f =
            (summandIso σ X (N + 1)).hom ≫ coprod.inr ≫ g at hl
        exact (cancel_epi (summandIso σ X (N + 1)).hom).mp hl

def component (σ : ℕ → D) (N : ℕ) (X : D) :
    (nested σ N).obj X ≅ (finiteSum σ N).obj X where
  hom := descend σ X N (Sigma.ι _)
  inv := Sigma.desc (injection σ X N)
  hom_inv_id := by
    apply hom_ext σ X N
    intro i
    change injection σ X N i ≫ (descend σ X N (Sigma.ι _) ≫ Sigma.desc (injection σ X N)) =
      injection σ X N i ≫ 𝟙 ((nested σ N).obj X)
    simp only [injection_descend_assoc, Sigma.ι_comp_desc, Category.comp_id]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (fun j : Fin (N + 1) => σ j.val ⨯ finitePower X j.val) i ≫
      (Sigma.desc (injection σ X N) ≫ descend σ X N (Sigma.ι _)) = Sigma.ι (fun j : Fin (N + 1) => σ j.val ⨯ finitePower X j.val) i ≫
        𝟙 (∐ (fun j : Fin (N + 1) => σ j.val ⨯ finitePower X j.val))
    simp only [Sigma.ι_comp_desc_assoc, injection_descend, Category.comp_id]

@[simp, reassoc] theorem injection_component (σ : ℕ → D) (N : ℕ) (X : D)
    (i : Fin (N + 1)) :
    injection σ X N i ≫ (component σ N X).hom =
      Sigma.ι (fun j : Fin (N + 1) => σ j.val ⨯ finitePower X j.val) i :=
  injection_descend σ X N _ i

theorem injection_natural (σ : ℕ → D) (N : ℕ) {X Y : D} (f : X ⟶ Y)
    (i : Fin (N + 1)) :
    injection σ X N i ≫ (nested σ N).map f =
      prod.map (𝟙 (σ i.val)) (finitePowerMap f i.val) ≫ injection σ Y N i := by
  induction N with
  | zero =>
      have hi : i = 0 := Fin.eq_zero i
      subst i
      simp [injection, nested, SyntaxPolynomial.constructors, SyntaxPolynomial.power,
        SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, finitePowerMap]
  | succ N ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [injection, Fin.lastCases_last, Fin.val_last]
        change ((summandIso σ X (N + 1)).hom ≫ coprod.inr) ≫
          coprod.map ((nested σ N).map f) _ =
            prod.map (𝟙 (σ (N + 1))) (finitePowerMap f (N + 1)) ≫
              (summandIso σ Y (N + 1)).hom ≫ coprod.inr
        simp only [Category.assoc, coprod.inr_map]
        change (summandIso σ X (N + 1)).hom ≫
          prod.map (𝟙 (σ (N + 1)))
            ((SyntaxPolynomial.power (.term : SyntaxPolynomial D) (N + 1)).eval.map
              ((f, 𝟙 (⊤_ D)) : (X, ⊤_ D) ⟶ (Y, ⊤_ D))) ≫ coprod.inr = _
        rw [← Category.assoc, ← summandIso_natural, Category.assoc]
      · simp only [injection, Fin.lastCases_castSucc, Fin.val_castSucc]
        change (injection σ X N j ≫ coprod.inl) ≫
          coprod.map ((nested σ N).map f) _ =
            prod.map (𝟙 (σ j.val)) (finitePowerMap f j.val) ≫ injection σ Y N j ≫ coprod.inl
        simpa only [Category.assoc, coprod.inl_map] using
          congrArg (fun k => k ≫ (coprod.inl : (nested σ N).obj Y ⟶ (nested σ (N + 1)).obj Y))
            (ih j)

def naturalIso (σ : ℕ → D) (N : ℕ) : nested σ N ≅ finiteSum σ N :=
  NatIso.ofComponents (component σ N) (fun f => by
    apply hom_ext σ _ N
    intro i
    rw [← Category.assoc, injection_natural, Category.assoc, injection_component,
      injection_component_assoc]
    change prod.map (𝟙 (σ i.val)) (finitePowerMap f i.val) ≫
      Sigma.ι (fun j : Fin (N + 1) => σ j.val ⨯ finitePower _ j.val) i =
        Sigma.ι (fun j : Fin (N + 1) => σ j.val ⨯ finitePower _ j.val) i ≫
          Limits.Sigma.map (fun j : Fin (N + 1) =>
            prod.map (𝟙 (σ j.val)) (finitePowerMap f j.val))
    exact (Sigma.ι_map (fun j : Fin (N + 1) =>
      prod.map (𝟙 (σ j.val)) (finitePowerMap f j.val)) i).symm)

variable {F : D} {N : ℕ}

def ordinary (R : RulePresentation F N) : D ⥤ D where
  obj X := ∐ (fun i : Fin (N + 1) => R.instances i ⨯ finitePower X i.val)
  map f := Limits.Sigma.map (fun i => prod.map (𝟙 (R.instances i)) (finitePowerMap f i.val))
  map_id X := by
    apply Sigma.hom_ext
    intro i
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro i
    simp [finitePowerMap_comp]

def coefficients (R : RulePresentation F N) (n : ℕ) : D :=
  if h : n ≤ N then R.instances ⟨n, Nat.lt_succ_of_le h⟩ else ⊥_ D

@[simp] theorem coefficients_fin (R : RulePresentation F N) (i : Fin (N + 1)) :
    coefficients R i.val = R.instances i := by
  dsimp [coefficients]
  simp [Nat.le_of_lt_succ i.isLt]

def ordinaryIso (R : RulePresentation F N) : finiteSum (coefficients R) N ≅ ordinary R :=
  NatIso.ofComponents (fun X => Limits.Sigma.mapIso (fun i =>
    prod.mapIso (eqToIso (coefficients_fin R i)) (Iso.refl (finitePower X i.val)))) (fun f => by
      apply Sigma.hom_ext
      intro i
      simp [finiteSum, ordinary])

/-- Ordered constructor branches and the original finite rule coproduct
are compared on objects, morphisms and every labelled summand. -/
def comparison (R : RulePresentation F N) : nested (coefficients R) N ≅ ordinary R :=
  naturalIso (coefficients R) N ≪≫ ordinaryIso R

@[simp, reassoc] theorem injection_comparison (R : RulePresentation F N) (X : D)
    (i : Fin (N + 1)) :
    injection (coefficients R) X N i ≫ (comparison R).hom.app X =
      prod.map (eqToHom (coefficients_fin R i)) (𝟙 (finitePower X i.val)) ≫
        Sigma.ι (fun j : Fin (N + 1) => R.instances j ⨯ finitePower X j.val) i := by
  change injection (coefficients R) X N i ≫
    ((component (coefficients R) N X).hom ≫
      Limits.Sigma.map (fun j => prod.map (eqToHom (coefficients_fin R j))
        (𝟙 (finitePower X j.val)))) = _
  rw [← Category.assoc, injection_component, Sigma.ι_map]

def endofunctorComparison (R : RulePresentation F N) :
    nested (coefficients R) N ⋙ (CategoryTheory.Equivalence.refl : D ≌ D).functor ≅
      (CategoryTheory.Equivalence.refl : D ≌ D).functor ⋙ ordinary R :=
  Functor.rightUnitor _ ≪≫ comparison R ≪≫ (Functor.leftUnitor _).symm

def mappedAlgebra (R : RulePresentation F N)
    (A : Endofunctor.Algebra (nested (coefficients R) N)) :
    Endofunctor.Algebra (ordinary R) :=
  AlgebraTransport.mappedAlgebra (CategoryTheory.Equivalence.refl : D ≌ D)
    (endofunctorComparison R) A

def mappedInitial (R : RulePresentation F N)
    (A : Endofunctor.Algebra (nested (coefficients R) N)) (hA : IsInitial A) :
    IsInitial (mappedAlgebra R A) :=
  AlgebraTransport.initial (CategoryTheory.Equivalence.refl : D ≌ D)
    (endofunctorComparison R) A hA

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PolynomialComparison
