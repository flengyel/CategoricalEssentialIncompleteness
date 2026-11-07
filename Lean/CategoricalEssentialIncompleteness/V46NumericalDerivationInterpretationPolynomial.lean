/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationFunctor
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationConstructors

/-! # Canonical polynomial input comparison for the actual PA numerical functor

Only finite products and coproducts are transported. The factorization
below identifies the already proved raw-code comparison with these
canonical input maps; no preservation of initial algebras is presumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Polynomial

variable {I : Type} (s : I → PredicateCategory 𝗣𝗔)

def component : (p : SyntaxPolynomial I) → (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) →
    K.obj ((p.mapCoefficients s).eval.obj X) ≅
      (p.mapCoefficients (fun i => K.obj (s i))).eval.obj ((K.prod K).obj X)
  | .term, _ => Iso.refl _
  | .formula, _ => Iso.refl _
  | .coefficient _, _ => Iso.refl _
  | .unit, _ => asIso (terminalComparison K)
  | .product p q, X =>
      asIso (prodComparison K ((p.mapCoefficients s).eval.obj X) ((q.mapCoefficients s).eval.obj X)) ≪≫
        prod.mapIso (component p X) (component q X)
  | .sum p q, X =>
      (asIso (coprodComparison K ((p.mapCoefficients s).eval.obj X) ((q.mapCoefficients s).eval.obj X))).symm ≪≫
        coprod.mapIso (component p X) (component q X)

theorem component_natural (p : SyntaxPolynomial I)
    {X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔} (f : X ⟶ Y) :
    K.map ((p.mapCoefficients s).eval.map f) ≫ (component s p Y).hom =
      (component s p X).hom ≫
        (p.mapCoefficients (fun i => K.obj (s i))).eval.map ((K.prod K).map f) := by
  induction p with
  | term => simp [component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | formula => simp [component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | coefficient C => simp [component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | unit => simp [component,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | product p q hp hq =>
      change K.map (prod.map _ _) ≫ (prodComparison K _ _ ≫ prod.map _ _) =
        (prodComparison K _ _ ≫ prod.map _ _) ≫ prod.map _ _
      rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,hp,hq]
      simp only [Category.assoc,prod.map_map]
  | sum p q hp hq =>
      change K.map (coprod.map _ _) ≫ (inv (coprodComparison K _ _) ≫ coprod.map _ _) =
        (inv (coprodComparison K _ _) ≫ coprod.map _ _) ≫ coprod.map _ _
      apply (cancel_epi (coprodComparison K ((p.mapCoefficients s).eval.obj X)
        ((q.mapCoefficients s).eval.obj X))).mp
      rw [← Category.assoc,coprodComparison_natural]
      simp only [Category.assoc,IsIso.hom_inv_id_assoc,coprod.map_map]
      rw [hp,hq]

def naturalIso (p : SyntaxPolynomial I) :
    (p.mapCoefficients s).eval ⋙ K ≅
      (K.prod K) ⋙ (p.mapCoefficients (fun i => K.obj (s i))).eval :=
  NatIso.ofComponents (component s p) (fun f => component_natural s p f)

@[reassoc] theorem component_fst (p q : SyntaxPolynomial I)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (component s (.product p q) X).hom ≫ prod.fst =
      K.map prod.fst ≫ (component s p X).hom := by
  simp [component,Category.assoc]

@[reassoc] theorem component_snd (p q : SyntaxPolynomial I)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (component s (.product p q) X).hom ≫ prod.snd =
      K.map prod.snd ≫ (component s q X).hom := by
  simp [component,Category.assoc]

@[reassoc] theorem component_inl (p q : SyntaxPolynomial I)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.map (coprod.inl : (p.mapCoefficients s).eval.obj X ⟶
      (p.mapCoefficients s).eval.obj X ⨿ (q.mapCoefficients s).eval.obj X) ≫
      (component s (.sum p q) X).hom = (component s p X).hom ≫ coprod.inl := by
  simp only [component,Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    map_inl_inv_coprodComparison_assoc,coprod.inl_map]

@[reassoc] theorem component_inr (p q : SyntaxPolynomial I)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.map (coprod.inr : (q.mapCoefficients s).eval.obj X ⟶
      (p.mapCoefficients s).eval.obj X ⨿ (q.mapCoefficients s).eval.obj X) ≫
      (component s (.sum p q) X).hom = (component s q X).hom ≫ coprod.inr := by
  simp only [component,Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    map_inr_inv_coprodComparison_assoc,coprod.inr_map]

variable (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (X Y : PredicateCategory 𝗣𝗔) (X' Y' : PredicateCategory 𝗧𝗔)
  (bX : K.obj X ≅ NumericalSyntaxTreeChart.E.functor.obj X')
  (bY : K.obj Y ≅ NumericalSyntaxTreeChart.E.functor.obj Y')

def leafMap {A B A' B' : NumericalTuples.Object} (a : A ≅ A') (b : B ≅ B') :
    @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance (A,B) (A',B') :=
  (a.hom,b.hom)

/-- The raw-code input chart is exactly the canonical K comparison,
recursive leaf maps, and inverse literal-equivalence comparison. -/
theorem component_factorization (p : SyntaxPolynomial I) :
    (component s p (X,Y)).hom ≫
      (p.mapCoefficients (fun i => K.obj (s i))).eval.map (leafMap bX bY) ≫
        (SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t (fun i => K.obj (s i))
          (fun i => (c i).symm) p (X',Y')).inv =
      (NumericalPolynomialRepresentation.polynomialIso s t c X Y X' Y' bX bY p).hom := by
  induction p with
  | term => simp [component,leafMap,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component,NumericalPolynomialRepresentation.polynomialIso]
  | formula => simp [component,leafMap,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component,NumericalPolynomialRepresentation.polynomialIso]
  | coefficient i => simp [component,leafMap,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component,NumericalPolynomialRepresentation.polynomialIso]
  | unit => simp [component,leafMap,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component,NumericalPolynomialRepresentation.polynomialIso]
  | product p q hp hq =>
      dsimp only [leafMap] at hp hq
      simp only [component,leafMap,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,SyntaxPolynomial.productFunctor,
        SyntaxPolynomialTransport.component,NumericalPolynomialRepresentation.polynomialIso,
        NumericalArithmetic.Geometry.productIso,Iso.trans_hom,Iso.trans_inv,prod.mapIso_hom,
        prod.mapIso_inv,Iso.symm_hom,asIso_hom,asIso_inv,Category.assoc,prod.map_map_assoc,hp,hq]
  | sum p q hp hq =>
      dsimp only [leafMap] at hp hq
      simp only [component,leafMap,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,SyntaxPolynomial.sumFunctor,
        SyntaxPolynomialTransport.component,NumericalPolynomialRepresentation.polynomialIso,
        NumericalArithmetic.Geometry.coproductIso,Iso.trans_hom,Iso.trans_inv,coprod.mapIso_hom,
        coprod.mapIso_inv,Iso.symm_hom,Iso.symm_inv,asIso_hom,asIso_inv,Category.assoc,coprod.map_map_assoc,hp,hq]


/-- Equality normalization is performed on the whole canonical input iso,
before concrete postfix carriers are substituted. -/
def normalizedComponent (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (pN : SyntaxPolynomial NumericalTuples.Object)
    (h₀ : p.mapCoefficients s = p₀) (hN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.obj (p₀.eval.obj A) ≅ pN.eval.obj ((K.prod K).obj A) :=
  (K.mapIso (eqToIso (congrArg (fun q => (SyntaxPolynomial.eval q).obj A) h₀))).symm ≪≫
    component s p A ≪≫
      eqToIso (congrArg (fun q => (SyntaxPolynomial.eval q).obj ((K.prod K).obj A)) hN)

theorem normalizedComponent_natural (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (pN : SyntaxPolynomial NumericalTuples.Object)
    (h₀ : p.mapCoefficients s = p₀) (hN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    {A B : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔} (f : A ⟶ B) :
    K.map (p₀.eval.map f) ≫ (normalizedComponent s p p₀ pN h₀ hN B).hom =
      (normalizedComponent s p p₀ pN h₀ hN A).hom ≫ pN.eval.map ((K.prod K).map f) := by
  cases h₀
  cases hN
  simpa only [normalizedComponent,eqToIso_refl,Functor.mapIso_refl,Iso.refl_symm,Iso.refl_trans,Iso.trans_refl] using
    component_natural s p f

def normalizedLiteralComponent (p : SyntaxPolynomial I)
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔)) (pN : SyntaxPolynomial NumericalTuples.Object)
    (h₁ : p.mapCoefficients t = p₁) (hN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    NumericalSyntaxTreeChart.E.functor.obj (p₁.eval.obj A) ≅
      pN.eval.obj ((NumericalSyntaxTreeChart.E.functor.prod NumericalSyntaxTreeChart.E.functor).obj A) :=
  (NumericalSyntaxTreeChart.E.functor.mapIso
    (eqToIso (congrArg (fun q => (SyntaxPolynomial.eval q).obj A) h₁))).symm ≪≫
    SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t (fun i => K.obj (s i))
      (fun i => (c i).symm) p A ≪≫
        eqToIso (congrArg (fun q => (SyntaxPolynomial.eval q).obj
          ((NumericalSyntaxTreeChart.E.functor.prod NumericalSyntaxTreeChart.E.functor).obj A)) hN)

theorem normalized_component_factorization (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (pN : SyntaxPolynomial NumericalTuples.Object)
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (hN : p.mapCoefficients (fun i => K.obj (s i)) = pN) :
    (normalizedComponent s p p₀ pN h₀ hN (X,Y)).hom ≫ pN.eval.map (leafMap bX bY) ≫
      (normalizedLiteralComponent s t c p p₁ pN h₁ hN (X',Y')).inv =
        (NumericalPolynomialRepresentation.normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom := by
  cases h₀
  cases h₁
  cases hN
  simpa only [normalizedComponent,normalizedLiteralComponent,NumericalPolynomialRepresentation.normalizedIso,
    eqToIso_refl,Functor.mapIso_refl,Iso.refl_symm,Iso.refl_trans,Iso.trans_refl] using
    component_factorization s t c X Y X' Y' bX bY p

/-- A proved literal constructor square becomes the actual algebra square
for the canonical mapped structure maps. No universal property is supplied. -/
theorem normalized_algebra_square (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (pN : SyntaxPolynomial NumericalTuples.Object)
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁)
    (hN : p.mapCoefficients (fun i => K.obj (s i)) = pN)
    {Z : PredicateCategory 𝗣𝗔} {Z' : PredicateCategory 𝗧𝗔}
    (bZ : K.obj Z ≅ NumericalSyntaxTreeChart.E.functor.obj Z')
    (sourceOp : p₀.eval.obj (X,Y) ⟶ Z) (targetOp : p₁.eval.obj (X',Y') ⟶ Z')
    (h : NormalizedConstructorEquation s t c X Y Z X' Y' Z' bX bY bZ
      p p₀ p₁ h₀ h₁ sourceOp targetOp) :
    pN.eval.map (leafMap bX bY) ≫
        ((normalizedLiteralComponent s t c p p₁ pN h₁ hN (X',Y')).inv ≫
          NumericalSyntaxTreeChart.E.functor.map targetOp) =
      ((normalizedComponent s p p₀ pN h₀ hN (X,Y)).inv ≫ K.map sourceOp) ≫ bZ.hom := by
  apply (cancel_epi (normalizedComponent s p p₀ pN h₀ hN (X,Y)).hom).mp
  change (normalizedComponent s p p₀ pN h₀ hN (X,Y)).hom ≫
      (pN.eval.map (leafMap bX bY) ≫
        ((normalizedLiteralComponent s t c p p₁ pN h₁ hN (X',Y')).inv ≫
          NumericalSyntaxTreeChart.E.functor.map targetOp)) = _
  calc
    _ = ((normalizedComponent s p p₀ pN h₀ hN (X,Y)).hom ≫
        pN.eval.map (leafMap bX bY) ≫
          (normalizedLiteralComponent s t c p p₁ pN h₁ hN (X',Y')).inv) ≫
            NumericalSyntaxTreeChart.E.functor.map targetOp := by simp only [Category.assoc]
    _ = (NumericalPolynomialRepresentation.normalizedIso s t c X Y X' Y' bX bY p p₀ p₁ h₀ h₁).hom ≫
        NumericalSyntaxTreeChart.E.functor.map targetOp :=
      congrArg (fun k => k ≫ NumericalSyntaxTreeChart.E.functor.map targetOp)
        (normalized_component_factorization s t c X Y X' Y' bX bY p p₀ p₁ pN h₀ h₁ hN)
    _ = K.map sourceOp ≫ bZ.hom := h.symm
    _ = _ := by simp only [Category.assoc,Iso.hom_inv_id_assoc]


end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Polynomial
