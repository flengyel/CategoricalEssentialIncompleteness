/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationProjection

/-! # Ordered finite coproduct coherence for arithmetic interpretation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Coherence
open Projection SyntacticSyntax SyntacticDerivation

/-- Normalize the two equality legs before a concrete polynomial is used. -/
theorem normalized_product {I : Type} (s : I → PredicateCategory 𝗣𝗔)
    (p q : SyntaxPolynomial I) (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp₀ : p.mapCoefficients s = p₀) (hq₀ : q.mapCoefficients s = q₀)
    (hpN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    (hqN : q.mapCoefficients (fun i => K.obj (s i)) = qN)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (Polynomial.normalizedComponent s (.product p q) (.product p₀ q₀) (.product pN qN)
      (congrArg₂ SyntaxPolynomial.product hp₀ hq₀)
      (congrArg₂ SyntaxPolynomial.product hpN hqN) A).hom =
    prodComparison K (p₀.eval.obj A) (q₀.eval.obj A) ≫
      prod.map (Polynomial.normalizedComponent s p p₀ pN hp₀ hpN A).hom
        (Polynomial.normalizedComponent s q q₀ qN hq₀ hqN A).hom := by
  cases hp₀
  cases hq₀
  cases hpN
  cases hqN
  simp only [Polynomial.normalizedComponent,eqToIso_refl,CategoryTheory.Functor.mapIso_refl,
    Iso.refl_symm,Iso.refl_trans,Iso.trans_refl,Polynomial.component,Iso.trans_hom,
    asIso_hom,prod.mapIso_hom,Iso.refl_hom]
  exact CategoryTheory.Category.id_comp _

theorem normalized_sum {I : Type} (s : I → PredicateCategory 𝗣𝗔)
    (p q : SyntaxPolynomial I) (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp₀ : p.mapCoefficients s = p₀) (hq₀ : q.mapCoefficients s = q₀)
    (hpN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    (hqN : q.mapCoefficients (fun i => K.obj (s i)) = qN)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (Polynomial.normalizedComponent s (.sum p q) (.sum p₀ q₀) (.sum pN qN)
      (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀)
      (congrArg₂ SyntaxPolynomial.sum hpN hqN) A).hom =
    inv (coprodComparison K (p₀.eval.obj A) (q₀.eval.obj A)) ≫
      coprod.map (Polynomial.normalizedComponent s p p₀ pN hp₀ hpN A).hom
        (Polynomial.normalizedComponent s q q₀ qN hq₀ hqN A).hom := by
  cases hp₀
  cases hq₀
  cases hpN
  cases hqN
  simp only [Polynomial.normalizedComponent,eqToIso_refl,CategoryTheory.Functor.mapIso_refl,
    Iso.refl_symm,Iso.refl_trans,Iso.trans_refl,Polynomial.component,Iso.trans_hom,
    Iso.symm_hom,asIso_inv,coprod.mapIso_hom,Iso.refl_hom]
  exact CategoryTheory.Category.id_comp _

@[reassoc] theorem normalized_sum_inl {I : Type} (s : I → PredicateCategory 𝗣𝗔)
    (p q : SyntaxPolynomial I) (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp₀ : p.mapCoefficients s = p₀) (hq₀ : q.mapCoefficients s = q₀)
    (hpN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    (hqN : q.mapCoefficients (fun i => K.obj (s i)) = qN)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.map (coprod.inl (C := PredicateCategory 𝗣𝗔) : p₀.eval.obj A ⟶ p₀.eval.obj A ⨿ q₀.eval.obj A) ≫
      (Polynomial.normalizedComponent s (.sum p q) (.sum p₀ q₀) (.sum pN qN)
        (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hpN hqN) A).hom =
      (Polynomial.normalizedComponent s p p₀ pN hp₀ hpN A).hom ≫ coprod.inl := by
  rw [normalized_sum s p q p₀ q₀ pN qN hp₀ hq₀ hpN hqN A]
  simp only [map_inl_inv_coprodComparison_assoc,coprod.inl_map]

@[reassoc] theorem normalized_sum_inr {I : Type} (s : I → PredicateCategory 𝗣𝗔)
    (p q : SyntaxPolynomial I) (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp₀ : p.mapCoefficients s = p₀) (hq₀ : q.mapCoefficients s = q₀)
    (hpN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    (hqN : q.mapCoefficients (fun i => K.obj (s i)) = qN)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.map (coprod.inr (C := PredicateCategory 𝗣𝗔) : q₀.eval.obj A ⟶ p₀.eval.obj A ⨿ q₀.eval.obj A) ≫
      (Polynomial.normalizedComponent s (.sum p q) (.sum p₀ q₀) (.sum pN qN)
        (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hpN hqN) A).hom =
      (Polynomial.normalizedComponent s q q₀ qN hq₀ hqN A).hom ≫ coprod.inr := by
  rw [normalized_sum s p q p₀ q₀ pN qN hp₀ hq₀ hpN hqN A]
  simp only [map_inr_inv_coprodComparison_assoc,coprod.inr_map]

@[simp] theorem normalized_coefficient (C : PredicateCategory 𝗣𝗔)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (Polynomial.normalizedComponent id (.coefficient C) (.coefficient C) (.coefficient (K.obj C)) rfl rfl A).hom =
      𝟙 (K.obj C) := by
  simp [Polynomial.normalizedComponent,Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

@[simp] theorem normalized_term (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (Polynomial.normalizedComponent id .term .term .term rfl rfl A).hom = 𝟙 (K.obj A.1) := by
  simp [Polynomial.normalizedComponent,Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

def powerInputIso (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    K.obj ((SyntaxPolynomial.power (.term : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) n).eval.obj
      (X,⊤_ (PredicateCategory 𝗣𝗔))) ≅
    (SyntaxPolynomial.power (.term : SyntaxPolynomial NumericalTuples.Object) n).eval.obj
      (K.obj X,⊤_ NumericalTuples.Object) :=
  Polynomial.normalizedComponent id (SyntaxPolynomial.power .term n)
    (SyntaxPolynomial.power .term n) (SyntaxPolynomial.power .term n)
    (mapCoefficients_id _)
    (SyntaxOperationsTransport.mapCoefficients_power K.obj .term n)
    (X,⊤_ (PredicateCategory 𝗣𝗔)) ≪≫
  (SyntaxPolynomial.power (.term : SyntaxPolynomial NumericalTuples.Object) n).eval.mapIso
    ((@Iso.refl NumericalTuples.Object inferInstance (K.obj X)).prod (asIso (terminalComparison K)))

@[simp] theorem powerInputIso_zero (X : PredicateCategory 𝗣𝗔) :
    (powerInputIso X 0).hom = terminalComparison K := by
  simp [powerInputIso,SyntaxPolynomial.power,Polynomial.normalizedComponent,
    Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

@[simp] theorem powerInputIso_one (X : PredicateCategory 𝗣𝗔) :
    (powerInputIso X 1).hom = 𝟙 (K.obj X) := by
  simp [powerInputIso,SyntaxPolynomial.power,Polynomial.normalizedComponent,
    Polynomial.component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]

theorem powerInputIso_succ (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (powerInputIso X (n+2)).hom =
      prodComparison K
        ((SyntaxPolynomial.power (.term : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (n+1)).eval.obj
          (X,⊤_ (PredicateCategory 𝗣𝗔))) X ≫
        prod.map (powerInputIso X (n+1)).hom (𝟙 (K.obj X)) := by
  let A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔 := (X,⊤_ (PredicateCategory 𝗣𝗔))
  let p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.power .term (n+1)
  let pN : SyntaxPolynomial NumericalTuples.Object := SyntaxPolynomial.power .term (n+1)
  let leg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj A) (K.obj X,⊤_ NumericalTuples.Object) := (𝟙 (K.obj X),terminalComparison K)
  let a := Polynomial.normalizedComponent id p₀ p₀ pN (mapCoefficients_id _)
    (SyntaxOperationsTransport.mapCoefficients_power K.obj .term (n+1)) A
  have h := normalized_product id p₀ .term p₀ .term pN .term
    (mapCoefficients_id _) rfl
    (SyntaxOperationsTransport.mapCoefficients_power K.obj .term (n+1)) rfl A
  change (Polynomial.normalizedComponent id (.product p₀ .term) (.product p₀ .term) (.product pN .term)
      _ _ A).hom ≫ prod.map (pN.eval.map leg) (𝟙 (K.obj X)) =
    prodComparison K (p₀.eval.obj A) X ≫ prod.map (a.hom ≫ pN.eval.map leg) (𝟙 (K.obj X))
  calc
    _ = (prodComparison K (p₀.eval.obj A) X ≫
        prod.map a.hom (Polynomial.normalizedComponent id .term .term .term rfl rfl A).hom) ≫
          prod.map (pN.eval.map leg) (𝟙 (K.obj X)) := congrArg (fun f => f ≫ _) h
    _ = _ := by
      rw [normalized_term]
      change prodComparison K (p₀.eval.obj A) X ≫
          prod.map a.hom (𝟙 (K.obj X)) ≫ prod.map (pN.eval.map leg) (𝟙 (K.obj X)) = _
      rw [prod.map_map,CategoryTheory.Category.comp_id]

/-- Finite powers and the syntax-polynomial powers have the same
canonical interpretation map, including the nullary terminal object. -/
theorem power_square (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    K.map (PolynomialComparison.powerIso X n).hom ≫ (powerInputIso X n).hom =
      (finitePowerIso X n).hom ≫ (PolynomialComparison.powerIso (K.obj X) n).hom := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero => simp [PolynomialComparison.powerIso,powerInputIso_one,finitePowerIso,finitePower]
    | succ n =>
      change (K.map (prod.map (PolynomialComparison.powerIso X (n+1)).hom (𝟙 X)) ≫
          (powerInputIso X (n+2)).hom) = _
      rw [powerInputIso_succ]
      change K.map (prod.map (PolynomialComparison.powerIso X (n+1)).hom (𝟙 X)) ≫
          (prodComparison K _ X ≫ prod.map (powerInputIso X (n+1)).hom (𝟙 (K.obj X))) =
        (prodComparison K (finitePower X (n+1)) X ≫
          prod.map (finitePowerIso X (n+1)).hom (𝟙 (K.obj X))) ≫
          prod.map (PolynomialComparison.powerIso (K.obj X) (n+1)).hom (𝟙 (K.obj X))
      have hn := prodComparison_natural K (PolynomialComparison.powerIso X (n+1)).hom (𝟙 X)
      calc
        _ = (prodComparison K (finitePower X (n+1)) X ≫
            prod.map (K.map (PolynomialComparison.powerIso X (n+1)).hom) (K.map (𝟙 X))) ≫
              prod.map (powerInputIso X (n+1)).hom (𝟙 (K.obj X)) := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ _) hn
        _ = _ := by
          simp only [Category.assoc,prod.map_map,ih,CategoryTheory.Functor.map_id,Category.comp_id]

variable (σ : ℕ → PredicateCategory 𝗣𝗔)

def summandInputIso (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    K.obj (σ n ⨯ finitePower X n) ≅ K.obj (σ n) ⨯ finitePower (K.obj X) n :=
  asIso (prodComparison K (σ n) (finitePower X n)) ≪≫
    prod.mapIso (Iso.refl _) (finitePowerIso X n)

def constructorSummandIso (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    K.obj (σ n ⨯ (SyntaxPolynomial.power (.term : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) n).eval.obj
      (X,⊤_ (PredicateCategory 𝗣𝗔))) ≅
      K.obj (σ n) ⨯ (SyntaxPolynomial.power (.term : SyntaxPolynomial NumericalTuples.Object) n).eval.obj
        (K.obj X,⊤_ NumericalTuples.Object) :=
  asIso (prodComparison K _ _) ≪≫ prod.mapIso (Iso.refl _) (powerInputIso X n)

theorem summand_square (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    K.map (PolynomialComparison.summandIso σ X n).hom ≫ (constructorSummandIso σ X n).hom =
      (summandInputIso σ X n).hom ≫ (PolynomialComparison.summandIso (fun k => K.obj (σ k)) (K.obj X) n).hom := by
  simp only [PolynomialComparison.summandIso,constructorSummandIso,summandInputIso,Iso.trans_hom,
    prod.mapIso_hom,Iso.refl_hom,asIso_hom,Category.assoc]
  rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,power_square,CategoryTheory.Functor.map_id]
  simp only [prod.map_map,Category.comp_id]

/-- The normalized constructor input comparison is the canonical
product comparison at arity zero. -/
theorem oneSortInputIso_zero (X : PredicateCategory 𝗣𝗔) :
    (oneSortInputIso σ 0 X).hom = (summandInputIso σ X 0).hom := by
  simp [oneSortInputIso,constructorInputIso,SyntaxPolynomial.constructors,
    Polynomial.normalizedComponent,Polynomial.component,SyntaxPolynomial.mapCoefficients,
    SyntaxPolynomial.power,SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,
    summandInputIso,finitePowerIso,finitePower]

theorem constructorBranch_eq (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (Polynomial.normalizedComponent id
      (.product (.coefficient (σ n)) (SyntaxPolynomial.power .term n))
      (.product (.coefficient (σ n)) (SyntaxPolynomial.power .term n))
      (.product (.coefficient (K.obj (σ n))) (SyntaxPolynomial.power .term n))
      (mapCoefficients_id _)
      (by simp only [SyntaxPolynomial.mapCoefficients,SyntaxOperationsTransport.mapCoefficients_power,id_eq])
      (X,⊤_ (PredicateCategory 𝗣𝗔))).hom ≫
      (SyntaxPolynomial.product (.coefficient (K.obj (σ n))) (SyntaxPolynomial.power .term n)).eval.map
        ((𝟙 (K.obj X),terminalComparison K) :
          (K.obj X,K.obj (⊤_ (PredicateCategory 𝗣𝗔))) ⟶ (K.obj X,⊤_ NumericalTuples.Object)) =
    (constructorSummandIso σ X n).hom := by
  have h := normalized_product id (.coefficient (σ n)) (SyntaxPolynomial.power .term n)
    (.coefficient (σ n)) (SyntaxPolynomial.power .term n)
    (.coefficient (K.obj (σ n))) (SyntaxPolynomial.power .term n)
    rfl (mapCoefficients_id _) rfl (SyntaxOperationsTransport.mapCoefficients_power K.obj .term n)
    (X,⊤_ (PredicateCategory 𝗣𝗔))
  rw [h,normalized_coefficient]
  change (prodComparison K _ _ ≫ prod.map (𝟙 _) _) ≫ prod.map (𝟙 _) _ = _
  rw [CategoryTheory.Category.assoc,prod.map_map]
  simp only [CategoryTheory.Category.comp_id]
  rfl

theorem oneSortInputIso_succ_inl (N : ℕ) (X : PredicateCategory 𝗣𝗔) :
    K.map (coprod.inl : (PolynomialComparison.nested σ N).obj X ⟶ (PolynomialComparison.nested σ (N+1)).obj X) ≫
      (oneSortInputIso σ (N+1) X).hom = (oneSortInputIso σ N X).hom ≫ coprod.inl := by
  let A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔 := (X,⊤_ (PredicateCategory 𝗣𝗔))
  let leg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj A) (K.obj X,⊤_ NumericalTuples.Object) := (𝟙 (K.obj X),terminalComparison K)
  have h : K.map (coprod.inl : (PolynomialComparison.nested σ N).obj X ⟶
      (PolynomialComparison.nested σ (N+1)).obj X) ≫ (constructorInputIso σ (N+1) A).hom =
      (constructorInputIso σ N A).hom ≫ coprod.inl :=
    normalized_sum_inl id (SyntaxPolynomial.constructors σ N)
      (.product (.coefficient (σ (N+1))) (SyntaxPolynomial.power .term (N+1)))
      (SyntaxPolynomial.constructors σ N)
      (.product (.coefficient (σ (N+1))) (SyntaxPolynomial.power .term (N+1)))
      (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N)
      (.product (.coefficient (K.obj (σ (N+1)))) (SyntaxPolynomial.power .term (N+1)))
      (mapCoefficients_id _) (mapCoefficients_id _)
      (SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N)
      (by simp only [SyntaxPolynomial.mapCoefficients,SyntaxOperationsTransport.mapCoefficients_power,id_eq]) A
  change K.map coprod.inl ≫ ((constructorInputIso σ (N+1) A).hom ≫
      (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) (N+1)).eval.map leg) = _
  calc
    _ = ((constructorInputIso σ N A).hom ≫ coprod.inl) ≫
        (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) (N+1)).eval.map leg := by
      exact (CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ _) h)
    _ = _ := by
      change ((constructorInputIso σ N A).hom ≫ coprod.inl) ≫
          coprod.map ((SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N).eval.map leg) _ = _
      rw [CategoryTheory.Category.assoc,coprod.inl_map]
      rfl

theorem oneSortInputIso_succ_inr (N : ℕ) (X : PredicateCategory 𝗣𝗔) :
    K.map (coprod.inr : σ (N+1) ⨯
      (SyntaxPolynomial.power (.term : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (N+1)).eval.obj
        (X,⊤_ (PredicateCategory 𝗣𝗔)) ⟶ (PolynomialComparison.nested σ (N+1)).obj X) ≫
      (oneSortInputIso σ (N+1) X).hom =
      (constructorSummandIso σ X (N+1)).hom ≫ coprod.inr := by
  let A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔 := (X,⊤_ (PredicateCategory 𝗣𝗔))
  let leg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj A) (K.obj X,⊤_ NumericalTuples.Object) := (𝟙 (K.obj X),terminalComparison K)
  have h := normalized_sum_inr id (SyntaxPolynomial.constructors σ N)
    (.product (.coefficient (σ (N+1))) (SyntaxPolynomial.power .term (N+1)))
    (SyntaxPolynomial.constructors σ N)
    (.product (.coefficient (σ (N+1))) (SyntaxPolynomial.power .term (N+1)))
    (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N)
    (.product (.coefficient (K.obj (σ (N+1)))) (SyntaxPolynomial.power .term (N+1)))
    (mapCoefficients_id _) (mapCoefficients_id _)
    (SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N)
    (by simp only [SyntaxPolynomial.mapCoefficients,SyntaxOperationsTransport.mapCoefficients_power,id_eq]) A
  change K.map coprod.inr ≫ ((constructorInputIso σ (N+1) A).hom ≫
      (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) (N+1)).eval.map leg) = _
  calc
    _ = ((Polynomial.normalizedComponent id
        (.product (.coefficient (σ (N+1))) (SyntaxPolynomial.power .term (N+1)))
        (.product (.coefficient (σ (N+1))) (SyntaxPolynomial.power .term (N+1)))
        (.product (.coefficient (K.obj (σ (N+1)))) (SyntaxPolynomial.power .term (N+1)))
        _ _ A).hom ≫ coprod.inr) ≫
          (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) (N+1)).eval.map leg := by
      exact (CategoryTheory.Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ _) h)
    _ = _ := by
      change (_ ≫ coprod.inr) ≫ coprod.map _
        ((SyntaxPolynomial.product (.coefficient (K.obj (σ (N+1))))
          (SyntaxPolynomial.power .term (N+1))).eval.map leg) = _
      rw [CategoryTheory.Category.assoc,coprod.inr_map,← CategoryTheory.Category.assoc,constructorBranch_eq]
      rfl

/-- Every ordered labelled branch is preserved by the same canonical
input isomorphism. No rule matching or algebra law is assumed. -/
theorem injection_square (N : ℕ) (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    K.map (PolynomialComparison.injection σ X N i) ≫ (oneSortInputIso σ N X).hom =
      (summandInputIso σ X i.val).hom ≫
        PolynomialComparison.injection (fun n => K.obj (σ n)) (K.obj X) N i := by
  induction N with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [PolynomialComparison.injection,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id,oneSortInputIso_zero]
    rfl
  | succ N ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [PolynomialComparison.injection,Fin.lastCases_last,Fin.val_last,CategoryTheory.Functor.map_comp,Category.assoc]
      rw [oneSortInputIso_succ_inr,← Category.assoc,summand_square,Category.assoc]
    · simp only [PolynomialComparison.injection,Fin.lastCases_castSucc,Fin.val_castSucc,CategoryTheory.Functor.map_comp,Category.assoc]
      rw [oneSortInputIso_succ_inl,← Category.assoc,ih,Category.assoc]
      rfl

def finiteSumIso (N : ℕ) (X : PredicateCategory 𝗣𝗔) :
    K.obj ((PolynomialComparison.finiteSum σ N).obj X) ≅
      (PolynomialComparison.finiteSum (fun n => K.obj (σ n)) N).obj (K.obj X) :=
  (asIso (sigmaComparison K (fun i : Fin (N+1) => σ i.val ⨯ finitePower X i.val))).symm ≪≫
    Sigma.mapIso (fun i => summandInputIso σ X i.val)

@[reassoc] theorem finiteSumIso_iota (N : ℕ) (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    K.map (Sigma.ι (fun i : Fin (N+1) => σ i.val ⨯ finitePower X i.val) i) ≫
      (finiteSumIso σ N X).hom =
      (summandInputIso σ X i.val).hom ≫
        Sigma.ι (fun i : Fin (N+1) => K.obj (σ i.val) ⨯ finitePower (K.obj X) i.val) i := by
  simp only [finiteSumIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

private theorem mapSum_hom_ext {I : Type} [Finite I] (C : I → PredicateCategory 𝗣𝗔)
    {Y : NumericalTuples.Object} (f g : K.obj (∐ C) ⟶ Y)
    (h : ∀ i, K.map (Sigma.ι C i) ≫ f = K.map (Sigma.ι C i) ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison K C)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc] using h i

/-- Rebracketing the syntax constructor polynomial into the ordinary
finite rule coproduct commutes with arithmetic interpretation. -/
theorem component_square (N : ℕ) (X : PredicateCategory 𝗣𝗔) :
    K.map (PolynomialComparison.component σ N X).hom ≫ (finiteSumIso σ N X).hom =
      (oneSortInputIso σ N X).hom ≫
        (PolynomialComparison.component (fun n => K.obj (σ n)) N (K.obj X)).hom := by
  apply (cancel_epi (K.map (PolynomialComparison.component σ N X).inv)).mp
  apply mapSum_hom_ext (fun i : Fin (N+1) => σ i.val ⨯ finitePower X i.val)
  intro i
  have hinv : Sigma.ι (fun i : Fin (N+1) => σ i.val ⨯ finitePower X i.val) i ≫
      (PolynomialComparison.component σ N X).inv = PolynomialComparison.injection σ X N i := by
    exact Sigma.ι_comp_desc _ _
  have hl : K.map (Sigma.ι (fun i : Fin (N+1) => σ i.val ⨯ finitePower X i.val) i) ≫
      (K.map (PolynomialComparison.component σ N X).inv ≫
        (K.map (PolynomialComparison.component σ N X).hom ≫ (finiteSumIso σ N X).hom)) =
      (summandInputIso σ X i.val).hom ≫
        Sigma.ι (fun i : Fin (N+1) => K.obj (σ i.val) ⨯ finitePower (K.obj X) i.val) i := by
    rw [← CategoryTheory.Functor.map_comp_assoc,hinv,← CategoryTheory.Functor.map_comp_assoc,
      PolynomialComparison.injection_component,finiteSumIso_iota]
  have hr : K.map (Sigma.ι (fun i : Fin (N+1) => σ i.val ⨯ finitePower X i.val) i) ≫
      (K.map (PolynomialComparison.component σ N X).inv ≫
        ((oneSortInputIso σ N X).hom ≫
          (PolynomialComparison.component (fun n => K.obj (σ n)) N (K.obj X)).hom)) =
      (summandInputIso σ X i.val).hom ≫
        Sigma.ι (fun i : Fin (N+1) => K.obj (σ i.val) ⨯ finitePower (K.obj X) i.val) i := by
    rw [← CategoryTheory.Functor.map_comp_assoc,hinv,← Category.assoc,injection_square,
      Category.assoc,PolynomialComparison.injection_component]
  exact hl.trans hr.symm


variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

/-- Only the coefficients in the actual finite coproduct are changed.
No equality of unused coefficients beyond the arity bound is asserted. -/
def mappedOrdinaryIso :
    PolynomialComparison.finiteSum (fun n => K.obj (PolynomialComparison.coefficients R n)) N ≅
      PolynomialComparison.ordinary (interpretedRules R) :=
  NatIso.ofComponents (fun X => Sigma.mapIso (fun i =>
    prod.mapIso (K.mapIso (eqToIso (PolynomialComparison.coefficients_fin R i)))
      (Iso.refl (finitePower X i.val)))) (fun f => by
    apply Sigma.hom_ext
    intro i
    simp [PolynomialComparison.finiteSum,PolynomialComparison.ordinary,interpretedRules])

@[reassoc] theorem mappedOrdinaryIso_iota (X : NumericalTuples.Object) (i : Fin (N+1)) :
    Sigma.ι (fun i : Fin (N+1) => K.obj (PolynomialComparison.coefficients R i.val) ⨯
        finitePower X i.val) i ≫ (mappedOrdinaryIso R).hom.app X =
      prod.map (K.map (eqToHom (PolynomialComparison.coefficients_fin R i)))
          (𝟙 (finitePower X i.val)) ≫
        Sigma.ι (fun i : Fin (N+1) => K.obj (R.instances i) ⨯ finitePower X i.val) i := by
  simp only [mappedOrdinaryIso,NatIso.ofComponents_hom_app,Sigma.ι_mapIso_hom,
    prod.mapIso_hom,CategoryTheory.Functor.mapIso_hom,eqToIso.hom,Iso.refl_hom]
  rfl

/-- The ordinary-polynomial comparison uses the same coefficient chart
as the constructor polynomial at each actual rule arity. -/
theorem ordinary_square (X : PredicateCategory 𝗣𝗔) :
    K.map ((PolynomialComparison.ordinaryIso R).hom.app X) ≫ (ordinaryObjectIso R X).hom =
      (finiteSumIso (PolynomialComparison.coefficients R) N X).hom ≫
        (mappedOrdinaryIso R).hom.app (K.obj X) := by
  apply mapSum_hom_ext (fun i : Fin (N+1) =>
    PolynomialComparison.coefficients R i.val ⨯ finitePower X i.val)
  intro i
  rw [← CategoryTheory.Functor.map_comp_assoc]
  change K.map (Sigma.ι (fun i : Fin (N+1) =>
      PolynomialComparison.coefficients R i.val ⨯ finitePower X i.val) i ≫
        Limits.Sigma.map (fun j => prod.map (eqToHom (PolynomialComparison.coefficients_fin R j))
          (𝟙 (finitePower X j.val)))) ≫ (ordinaryObjectIso R X).hom = _
  rw [Sigma.ι_map,CategoryTheory.Functor.map_comp,Category.assoc,ordinaryObjectIso_iota,
    finiteSumIso_iota_assoc,mappedOrdinaryIso_iota]
  rw [← Category.assoc,← Category.assoc]
  apply congrArg (fun f => f ≫ Sigma.ι
    (fun j : Fin (N+1) => K.obj (R.instances j) ⨯ finitePower (K.obj X) j.val) i)
  change K.map (prod.map (eqToHom (PolynomialComparison.coefficients_fin R i))
      (𝟙 (finitePower X i.val))) ≫
      (prodComparison K (R.instances i) (finitePower X i.val) ≫
        prod.map (𝟙 (K.obj (R.instances i))) (finitePowerIso X i.val).hom) =
    (prodComparison K (PolynomialComparison.coefficients R i.val) (finitePower X i.val) ≫
      prod.map (𝟙 (K.obj (PolynomialComparison.coefficients R i.val)))
        (finitePowerIso X i.val).hom) ≫
      prod.map (K.map (eqToHom (PolynomialComparison.coefficients_fin R i)))
        (𝟙 (finitePower (K.obj X) i.val))
  rw [← Category.assoc,prodComparison_natural,Category.assoc]
  simp only [CategoryTheory.Category.assoc,prod.map_map,CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]

/-- The target ordinary polynomial is still the original finite rule
signature, rather than a polynomial with silently changed coefficients. -/
def targetComparison :
    PolynomialComparison.nested (fun n => K.obj (PolynomialComparison.coefficients R n)) N ≅
      PolynomialComparison.ordinary (interpretedRules R) :=
  PolynomialComparison.naturalIso (fun n => K.obj (PolynomialComparison.coefficients R n)) N ≪≫
    mappedOrdinaryIso R

@[reassoc] theorem targetComparison_injection (X : NumericalTuples.Object) (i : Fin (N+1)) :
    PolynomialComparison.injection
        (fun n => K.obj (PolynomialComparison.coefficients R n)) X N i ≫
      (targetComparison R).hom.app X =
      prod.map (K.map (eqToHom (PolynomialComparison.coefficients_fin R i)))
          (𝟙 (finitePower X i.val)) ≫
        Sigma.ι (fun j : Fin (N+1) => K.obj (R.instances j) ⨯ finitePower X j.val) i := by
  change PolynomialComparison.injection _ X N i ≫
      ((PolynomialComparison.component _ N X).hom ≫ (mappedOrdinaryIso R).hom.app X) = _
  rw [← Category.assoc,PolynomialComparison.injection_component,mappedOrdinaryIso_iota]

/-- Equality legs between predicate presentations do not change the
stored scalar coefficient when interpreted numerically. -/
theorem coefficient_eq_value {C D : PredicateCategory 𝗣𝗔} (h : C = D)
    (x : NumericalTuples.Point (K.obj C)) :
    ((K.map (eqToHom h)).toFun x).val = x.val := by
  cases h
  rw [eqToHom_refl,CategoryTheory.Functor.map_id]
  rfl

theorem coefficient_eq_code {C D : PredicateCategory 𝗣𝗔} (h : C = D)
    (x : NumericalTuples.Point (K.obj C)) :
    NumericalTuples.code (K.obj D).dimension ((K.map (eqToHom h)).toFun x).val =
      NumericalTuples.code (K.obj C).dimension x.val := by
  cases h
  rw [eqToHom_refl,CategoryTheory.Functor.map_id]
  rfl

/-- The constructor-to-ordinary comparison commutes with the canonical
arithmetic input map on every ordered branch, including arity zero. -/
theorem comparison_square (X : PredicateCategory 𝗣𝗔) :
    K.map ((PolynomialComparison.comparison R).hom.app X) ≫ (ordinaryObjectIso R X).hom =
      (oneSortInputIso (PolynomialComparison.coefficients R) N X).hom ≫
        (targetComparison R).hom.app (K.obj X) := by
  change K.map ((PolynomialComparison.component (PolynomialComparison.coefficients R) N X).hom ≫
      (PolynomialComparison.ordinaryIso R).hom.app X) ≫ (ordinaryObjectIso R X).hom = _
  rw [CategoryTheory.Functor.map_comp,Category.assoc,ordinary_square,← Category.assoc,component_square,Category.assoc]
  rfl


def targetEndofunctorComparison :
    PolynomialComparison.nested (fun n => K.obj (PolynomialComparison.coefficients R n)) N ⋙
        (CategoryTheory.Equivalence.refl : NumericalTuples.Object ≌ NumericalTuples.Object).functor ≅
      (CategoryTheory.Equivalence.refl : NumericalTuples.Object ≌ NumericalTuples.Object).functor ⋙
        PolynomialComparison.ordinary (interpretedRules R) :=
  CategoryTheory.Functor.rightUnitor _ ≪≫ targetComparison R ≪≫ (CategoryTheory.Functor.leftUnitor _).symm

def targetMappedAlgebra
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    Endofunctor.Algebra (PolynomialComparison.ordinary (interpretedRules R)) :=
  AlgebraTransport.mappedAlgebra
    (CategoryTheory.Equivalence.refl : NumericalTuples.Object ≌ NumericalTuples.Object)
    (targetEndofunctorComparison R)
    (mappedOneSortAlgebra (PolynomialComparison.coefficients R) N B)

private theorem source_mapped_str
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    (PolynomialComparison.mappedAlgebra R B).str =
      (PolynomialComparison.comparison R).inv.app B.a ≫ B.str := by
  simp [PolynomialComparison.mappedAlgebra,AlgebraTransport.mappedAlgebra,
    PolynomialComparison.endofunctorComparison]

private theorem target_mapped_str
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    (targetMappedAlgebra R B).str = (targetComparison R).inv.app (K.obj B.a) ≫
      (oneSortInputIso (PolynomialComparison.coefficients R) N B.a).inv ≫ K.map B.str := by
  simp [targetMappedAlgebra,AlgebraTransport.mappedAlgebra,targetEndofunctorComparison,
    mappedOneSortAlgebra]

/-- This is equality of the actual structure morphisms, with the
existing ordinary input comparison, rather than a carrier comparison. -/
theorem mapped_structure
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    (mappedOrdinaryAlgebra R (PolynomialComparison.mappedAlgebra R B)).str =
      (targetMappedAlgebra R B).str := by
  let a := K.mapIso ((PolynomialComparison.comparison R).app B.a)
  let b := ordinaryObjectIso R B.a
  let c := oneSortInputIso (PolynomialComparison.coefficients R) N B.a
  let d := (targetComparison R).app (K.obj B.a)
  have h : a ≪≫ b = c ≪≫ d := Iso.ext (comparison_square R B.a)
  have hi : b.inv ≫ a.inv = d.inv ≫ c.inv := congrArg (fun e => e.inv) h
  change (ordinaryObjectIso R B.a).inv ≫
    K.map (PolynomialComparison.mappedAlgebra R B).str = _
  rw [source_mapped_str R B,CategoryTheory.Functor.map_comp]
  change b.inv ≫ (a.inv ≫ K.map B.str) = (targetMappedAlgebra R B).str
  calc
    _ = (b.inv ≫ a.inv) ≫ K.map B.str := (CategoryTheory.Category.assoc _ _ _).symm
    _ = (d.inv ≫ c.inv) ≫ K.map B.str := congrArg (fun f => f ≫ K.map B.str) hi
    _ = _ := (CategoryTheory.Category.assoc _ _ _).trans (target_mapped_str R B).symm

/-- The identity on the carrier is an isomorphism of the full algebras.
Initiality of the one-sort image is proved separately at the concrete
postfix algebra; it is not a hypothesis of this comparison. -/
def mappedAlgebraIso
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    mappedOrdinaryAlgebra R (PolynomialComparison.mappedAlgebra R B) ≅ targetMappedAlgebra R B :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (PolynomialComparison.ordinary (interpretedRules R)).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id,mapped_structure])

def targetMappedInitial
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N))
    (hB : IsInitial (mappedOneSortAlgebra (PolynomialComparison.coefficients R) N B)) :
    IsInitial (targetMappedAlgebra R B) :=
  AlgebraTransport.initial
    (CategoryTheory.Equivalence.refl : NumericalTuples.Object ≌ NumericalTuples.Object)
    (targetEndofunctorComparison R)
    (mappedOneSortAlgebra (PolynomialComparison.coefficients R) N B) hB

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Coherence
