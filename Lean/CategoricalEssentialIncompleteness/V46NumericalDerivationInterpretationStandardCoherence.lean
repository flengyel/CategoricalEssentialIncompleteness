/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationWordCoherence
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationCoherence

/-! # Coherence with the original interpreted rule coefficients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.StandardCoherence
open SyntacticSyntax SyntacticDerivation Projection WordCoherence

section Bounded
variable {C : Type u} [Category.{v} C] [Regular C] [HasFiniteCoproducts C]

omit [Category.{v} C] [Regular C] [HasFiniteCoproducts C] in
theorem constructors_eq (a b : ℕ → C) (N : ℕ) (h : ∀ n ≤ N, a n = b n) :
    SyntaxPolynomial.constructors a N = SyntaxPolynomial.constructors b N := by
  induction N with
  | zero => simp only [SyntaxPolynomial.constructors,h 0 (Nat.le_refl 0)]
  | succ N ih =>
    have hh := ih (fun n hn => h n (Nat.le_trans hn (Nat.le_succ N)))
    simp only [SyntaxPolynomial.constructors,hh,h (N+1) (Nat.le_refl (N+1))]

def nestedChange (a b : ℕ → C) (N : ℕ) (h : ∀ n ≤ N, a n = b n) (X : C) :
    (PolynomialComparison.nested a N).obj X ≅ (PolynomialComparison.nested b N).obj X :=
  eqToIso (congrArg (fun p => (SyntaxPolynomial.eval p).obj (X,⊤_ C)) (constructors_eq a b N h))

omit [HasFiniteCoproducts C] in
private theorem product_cast {A B A' B' : C} (hA : A = A') (hB : B = B') :
    eqToHom (congrArg₂ (fun X Y : C => X ⨯ Y) hA hB) = prod.map (eqToHom hA) (eqToHom hB) := by
  cases hA
  cases hB
  simp

omit [Regular C] in
private theorem sum_cast_inl {A B A' B' : C} (hA : A = A') (hB : B = B') :
    (coprod.inl : A ⟶ A ⨿ B) ≫ eqToHom (congrArg₂ (fun X Y : C => X ⨿ Y) hA hB) =
      eqToHom hA ≫ (coprod.inl : A' ⟶ A' ⨿ B') := by
  cases hA
  cases hB
  simp

omit [Regular C] in
private theorem sum_cast_inr {A B A' B' : C} (hA : A = A') (hB : B = B') :
    (coprod.inr : B ⟶ A ⨿ B) ≫ eqToHom (congrArg₂ (fun X Y : C => X ⨿ Y) hA hB) =
      eqToHom hB ≫ (coprod.inr : B' ⟶ A' ⨿ B') := by
  cases hA
  cases hB
  simp

/-- Changing only the used coefficients preserves each labelled branch
and its ordered children. The unused coefficients are unrestricted. -/
theorem injection_change (a b : ℕ → C) (N : ℕ) (h : ∀ n ≤ N, a n = b n)
    (X : C) (i : Fin (N+1)) :
    PolynomialComparison.injection a X N i ≫ (nestedChange a b N h X).hom =
      prod.map (eqToHom (h i.val (Nat.le_of_lt_succ i.isLt))) (𝟙 (finitePower X i.val)) ≫
        PolynomialComparison.injection b X N i := by
  induction N with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change (𝟙 (a 0 ⨯ ⊤_ C)) ≫
      eqToHom (congrArg₂ (fun A B : C => A ⨯ B) (h 0 (Nat.le_refl 0)) rfl) =
      prod.map (eqToHom (h 0 (Nat.le_refl 0))) (𝟙 (⊤_ C)) ≫ 𝟙 _
    rw [Category.id_comp,Category.comp_id,product_cast (h 0 (Nat.le_refl 0)) (rfl : (⊤_ C) = ⊤_ C),eqToHom_refl]
  | succ N ih =>
    let h₀ : ∀ n ≤ N, a n = b n := fun n hn => h n (Nat.le_trans hn (Nat.le_succ N))
    let hL := congrArg (fun p => (SyntaxPolynomial.eval p).obj (X,⊤_ C)) (constructors_eq a b N h₀)
    let hR := congrArg (fun A : C => A ⨯
      (SyntaxPolynomial.power (.term : SyntaxPolynomial C) (N+1)).eval.obj (X,⊤_ C))
        (h (N+1) (Nat.le_refl (N+1)))
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [PolynomialComparison.injection,Fin.lastCases_last,Fin.val_last,Category.assoc]
      change (PolynomialComparison.summandIso a X (N+1)).hom ≫
        (coprod.inr ≫ eqToHom (congrArg₂ (fun A B : C => A ⨿ B) hL hR)) =
        prod.map (eqToHom (h (N+1) (Nat.le_refl (N+1)))) (𝟙 (finitePower X (N+1))) ≫
          ((PolynomialComparison.summandIso b X (N+1)).hom ≫ coprod.inr)
      rw [sum_cast_inr hL hR,← Category.assoc,← Category.assoc]
      apply congrArg (fun f => f ≫ coprod.inr)
      change (PolynomialComparison.summandIso a X (N+1)).hom ≫
        eqToHom (congrArg₂ (fun A B : C => A ⨯ B)
          (h (N+1) (Nat.le_refl (N+1))) rfl) = _
      rw [product_cast (h (N+1) (Nat.le_refl (N+1))) rfl,eqToHom_refl]
      simp only [PolynomialComparison.summandIso,prod.mapIso_hom,Iso.refl_hom,prod.map_map,
        Category.id_comp,Category.comp_id]
    · simp only [PolynomialComparison.injection,Fin.lastCases_castSucc,Fin.val_castSucc,Category.assoc]
      change PolynomialComparison.injection a X N j ≫
        (coprod.inl ≫ eqToHom (congrArg₂ (fun A B : C => A ⨿ B) hL hR)) =
        prod.map (eqToHom (h j.val (Nat.le_of_lt_succ j.castSucc.isLt)))
          (𝟙 (finitePower X j.val)) ≫
          (PolynomialComparison.injection b X N j ≫ coprod.inl)
      let tail : (PolynomialComparison.nested b N).obj X ⟶
          (PolynomialComparison.nested b (N+1)).obj X := coprod.inl
      calc
        _ = PolynomialComparison.injection a X N j ≫ eqToHom hL ≫ tail :=
          congrArg (fun f => PolynomialComparison.injection a X N j ≫ f) (sum_cast_inl hL hR)
        _ = _ := (Category.assoc (PolynomialComparison.injection a X N j) (eqToHom hL) tail).symm.trans
          ((congrArg (fun f => f ≫ tail) (ih h₀ j)).trans
            (Category.assoc
              (prod.map (eqToHom (h₀ j.val (Nat.le_of_lt_succ j.isLt)))
                (𝟙 (finitePower X j.val))) (PolynomialComparison.injection b X N j) tail))
end Bounded

section Output
/-- A second output normalization is just the corresponding object
cast. Equality induction treats the complete polynomial component. -/
theorem normalized_output {I : Type} (s : I → PredicateCategory 𝗣𝗔)
    (p : SyntaxPolynomial I) (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ p₂ : SyntaxPolynomial NumericalTuples.Object)
    (h₀ : p.mapCoefficients s = p₀)
    (h₁ : p.mapCoefficients (fun i => K.obj (s i)) = p₁)
    (h₂ : p.mapCoefficients (fun i => K.obj (s i)) = p₂)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    Polynomial.normalizedComponent s p p₀ p₂ h₀ h₂ A =
      Polynomial.normalizedComponent s p p₀ p₁ h₀ h₁ A ≪≫
        eqToIso (congrArg (fun r => (SyntaxPolynomial.eval r).obj ((K.prod K).obj A))
          (h₁.symm.trans h₂)) := by
  cases h₀
  cases h₁
  cases h₂
  simp [Polynomial.normalizedComponent]

private theorem polynomial_cast_map {p q : SyntaxPolynomial NumericalTuples.Object} (h : p = q)
    {A B : NumericalTuples.Object × NumericalTuples.Object} (f : A ⟶ B) :
    eqToHom (congrArg (fun r => (SyntaxPolynomial.eval r).obj A) h) ≫ q.eval.map f =
      p.eval.map f ≫ eqToHom (congrArg (fun r => (SyntaxPolynomial.eval r).obj B) h) := by
  cases h
  simp

/-- Terminal normalization of the second recursive coordinate commutes
with changing the output polynomial. -/
theorem oneSortInput_change (σ : ℕ → PredicateCategory 𝗣𝗔) (τ : ℕ → NumericalTuples.Object)
    (N : ℕ) (hp : (SyntaxPolynomial.constructors σ N).mapCoefficients K.obj = SyntaxPolynomial.constructors τ N)
    (X : PredicateCategory 𝗣𝗔) :
    oneSortInputIsoTo σ τ N hp X = oneSortInputIso σ N X ≪≫
      eqToIso (congrArg (fun p => (SyntaxPolynomial.eval p).obj (K.obj X,⊤_ NumericalTuples.Object))
        ((SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N).symm.trans hp)) := by
  apply Iso.ext
  change (Polynomial.normalizedComponent id _ _ _ _ hp (X,⊤_ (PredicateCategory 𝗣𝗔))).hom ≫
      (SyntaxPolynomial.constructors τ N).eval.map
        ((𝟙 (K.obj X),terminalComparison K) :
          (K.obj X,K.obj (⊤_ (PredicateCategory 𝗣𝗔))) ⟶ (K.obj X,⊤_ NumericalTuples.Object)) = _
  rw [normalized_output id (SyntaxPolynomial.constructors σ N) (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N) (SyntaxPolynomial.constructors τ N)
    (mapCoefficients_id (SyntaxPolynomial.constructors σ N))
    (SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N) hp
    (X,⊤_ (PredicateCategory 𝗣𝗔))]
  simp only [Iso.trans_hom,eqToIso.hom,Category.assoc]
  rw [polynomial_cast_map
    ((SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N).symm.trans hp),← Category.assoc]
  rfl
end Output

section Actual
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
local notation "σ" => PolynomialComparison.coefficients R
local notation "τ" => PolynomialComparison.coefficients (interpretedRules R)
local notation "hp" => interpreted_constructor_polynomial R

theorem coefficientAgreement (n : ℕ) (hn : n ≤ N) : K.obj (σ n) = τ n := by
  simp only [PolynomialComparison.coefficients,dite_eq_left hn,interpretedRules]

def actualNestedChange (X : NumericalTuples.Object) :
    (PolynomialComparison.nested (fun n => K.obj (σ n)) N).obj X ≅
      (PolynomialComparison.nested τ N).obj X :=
  nestedChange (fun n => K.obj (σ n)) τ N (coefficientAgreement R) X

/-- The finite coefficient casts in the generic comparison agree with
those of the original interpreted rule presentation. -/
theorem targetComparison_eq (X : NumericalTuples.Object) :
    (Coherence.targetComparison R).hom.app X =
      (actualNestedChange R X).hom ≫ (PolynomialComparison.comparison (interpretedRules R)).hom.app X := by
  apply PolynomialComparison.hom_ext (fun n => K.obj (σ n)) X N
  intro i
  rw [Coherence.targetComparison_injection,← Category.assoc]
  change _ = (PolynomialComparison.injection (fun n => K.obj (σ n)) X N i ≫
    (nestedChange (fun n => K.obj (σ n)) τ N (coefficientAgreement R) X).hom) ≫ _
  rw [injection_change,Category.assoc,PolynomialComparison.injection_comparison,← Category.assoc,prod.map_map]
  have he : eqToHom (coefficientAgreement R i.val (Nat.le_of_lt_succ i.isLt)) ≫
      eqToHom (PolynomialComparison.coefficients_fin (interpretedRules R) i) =
      K.map (eqToHom (PolynomialComparison.coefficients_fin R i)) := by
    rw [eqToHom_trans,eqToHom_map]
  simp only [Category.comp_id]
  rw [he]
  rfl

theorem actualInput_change (X : PredicateCategory 𝗣𝗔) :
    (oneSortInputIsoTo σ τ N hp X).hom =
      (oneSortInputIso σ N X).hom ≫ (actualNestedChange R (K.obj X)).hom := by
  exact congrArg (fun i => i.hom) (oneSortInput_change σ τ N hp X)

/-- This equation has exactly the original ordinary rule functor at
the target, including its coefficients_fin casts. -/
theorem standardcomparison_square (X : PredicateCategory 𝗣𝗔) :
    K.map ((PolynomialComparison.comparison R).hom.app X) ≫ (ordinaryObjectIso R X).hom =
      (oneSortInputIsoTo σ τ N hp X).hom ≫
        (PolynomialComparison.comparison (interpretedRules R)).hom.app (K.obj X) := by
  rw [Coherence.comparison_square,targetComparison_eq,← Category.assoc,← actualInput_change]

private theorem source_str
    (B : Endofunctor.Algebra (PolynomialComparison.nested σ N)) :
    (PolynomialComparison.mappedAlgebra R B).str =
      (PolynomialComparison.comparison R).inv.app B.a ≫ B.str := by
  simp [PolynomialComparison.mappedAlgebra,AlgebraTransport.mappedAlgebra,
    PolynomialComparison.endofunctorComparison]

private theorem target_str
    (B : Endofunctor.Algebra (PolynomialComparison.nested σ N)) :
    (PolynomialComparison.mappedAlgebra (interpretedRules R) (mappedOneSortAlgebraTo σ τ N hp B)).str =
      (PolynomialComparison.comparison (interpretedRules R)).inv.app (K.obj B.a) ≫
        (oneSortInputIsoTo σ τ N hp B.a).inv ≫ K.map B.str := by
  simp [PolynomialComparison.mappedAlgebra,AlgebraTransport.mappedAlgebra,
    PolynomialComparison.endofunctorComparison,mappedOneSortAlgebraTo]

theorem mapped_structure
    (B : Endofunctor.Algebra (PolynomialComparison.nested σ N)) :
    (mappedOrdinaryAlgebra R (PolynomialComparison.mappedAlgebra R B)).str =
      (PolynomialComparison.mappedAlgebra (interpretedRules R)
        (mappedOneSortAlgebraTo σ τ N hp B)).str := by
  let a := K.mapIso ((PolynomialComparison.comparison R).app B.a)
  let b := ordinaryObjectIso R B.a
  let c := oneSortInputIsoTo σ τ N hp B.a
  let d := (PolynomialComparison.comparison (interpretedRules R)).app (K.obj B.a)
  have hh : a ≪≫ b = c ≪≫ d := Iso.ext (standardcomparison_square R B.a)
  have hi : b.inv ≫ a.inv = d.inv ≫ c.inv := congrArg (fun i => i.inv) hh
  change (ordinaryObjectIso R B.a).inv ≫ K.map (PolynomialComparison.mappedAlgebra R B).str = _
  calc
    _ = b.inv ≫ a.inv ≫ K.map B.str := by
      rw [source_str,CategoryTheory.Functor.map_comp]
      rfl
    _ = d.inv ≫ c.inv ≫ K.map B.str := by
      exact (Category.assoc b.inv a.inv (K.map B.str)).symm.trans
        ((congrArg (fun f => f ≫ K.map B.str) hi).trans
          (Category.assoc d.inv c.inv (K.map B.str)))
    _ = _ := (target_str R B).symm

/-- The full algebra isomorphism uses the identity on its underlying
carrier. All constructor compatibility follows from the finite-branch
equation above; it is not an additional premise. -/
def mappedAlgebraIso
    (B : Endofunctor.Algebra (PolynomialComparison.nested σ N)) :
    mappedOrdinaryAlgebra R (PolynomialComparison.mappedAlgebra R B) ≅
      PolynomialComparison.mappedAlgebra (interpretedRules R)
        (mappedOneSortAlgebraTo σ τ N hp B) :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (PolynomialComparison.ordinary (interpretedRules R)).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id,mapped_structure])

@[simp] theorem mappedAlgebraIso_hom_f
    (B : Endofunctor.Algebra (PolynomialComparison.nested σ N)) :
    (mappedAlgebraIso R B).hom.f = 𝟙 (K.obj B.a) := rfl
end Actual

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.StandardCoherence
