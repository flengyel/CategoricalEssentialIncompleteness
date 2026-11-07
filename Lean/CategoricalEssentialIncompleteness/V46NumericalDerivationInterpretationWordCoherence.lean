/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationInitial
import CategoricalEssentialIncompleteness.V46NumericalDerivationTreeUniqueness

/-! # Coefficient-index coherence for the literal derivation words

These structural identities compare the same constructor algebra before
and after coefficient substitution. The original interpretation map is
retained; a scalar word conclusion is obtained from its commuting word
inclusions, rather than from initiality without constructor comparisons.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordCoherence
open SyntacticSyntax
abbrev E := NumericalSyntaxTreeChart.E

section Structural
variable {I : Type} (f : I → PredicateCategory 𝗧𝗔) (g : I → NumericalTuples.Object)
  (c : ∀ i, E.functor.obj (f i) ≅ g i)

def componentNormalized (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗧𝗔)) (pN : SyntaxPolynomial NumericalTuples.Object)
    (h₀ : p.mapCoefficients f = p₀) (hN : p.mapCoefficients g = pN)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    E.functor.obj (p₀.eval.obj A) ≅ pN.eval.obj ((E.prod E).functor.obj A) :=
  (E.functor.mapIso (eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj A) h₀))).symm ≪≫
    SyntaxPolynomialTransport.component E f g c p A ≪≫
      eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj ((E.prod E).functor.obj A)) hN)

theorem normalized_product (p q : SyntaxPolynomial I)
    (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗧𝗔)) (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp₀ : p.mapCoefficients f = p₀) (hq₀ : q.mapCoefficients f = q₀)
    (hpN : p.mapCoefficients g = pN) (hqN : q.mapCoefficients g = qN)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    (componentNormalized f g c (.product p q) (.product p₀ q₀) (.product pN qN)
      (congrArg₂ SyntaxPolynomial.product hp₀ hq₀) (congrArg₂ SyntaxPolynomial.product hpN hqN) A).hom =
      prodComparison E.functor (p₀.eval.obj A) (q₀.eval.obj A) ≫
        prod.map (componentNormalized f g c p p₀ pN hp₀ hpN A).hom
          (componentNormalized f g c q q₀ qN hq₀ hqN A).hom := by
  cases hp₀
  cases hq₀
  cases hpN
  cases hqN
  simp only [componentNormalized,eqToIso_refl,CategoryTheory.Functor.mapIso_refl,Iso.refl_symm,
    Iso.refl_trans,Iso.trans_refl,SyntaxPolynomialTransport.component,Iso.trans_hom,
    asIso_hom,prod.mapIso_hom,Iso.refl_hom]
  exact CategoryTheory.Category.id_comp _

theorem normalized_sum (p q : SyntaxPolynomial I)
    (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗧𝗔)) (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp₀ : p.mapCoefficients f = p₀) (hq₀ : q.mapCoefficients f = q₀)
    (hpN : p.mapCoefficients g = pN) (hqN : q.mapCoefficients g = qN)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    (componentNormalized f g c (.sum p q) (.sum p₀ q₀) (.sum pN qN)
      (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hpN hqN) A).hom =
      inv (coprodComparison E.functor (p₀.eval.obj A) (q₀.eval.obj A)) ≫
        coprod.map (componentNormalized f g c p p₀ pN hp₀ hpN A).hom
          (componentNormalized f g c q q₀ qN hq₀ hqN A).hom := by
  cases hp₀
  cases hq₀
  cases hpN
  cases hqN
  simp only [componentNormalized,eqToIso_refl,CategoryTheory.Functor.mapIso_refl,Iso.refl_symm,
    Iso.refl_trans,Iso.trans_refl,SyntaxPolynomialTransport.component,Iso.trans_hom,
    Iso.symm_hom,asIso_inv,coprod.mapIso_hom,Iso.refl_hom]
  exact CategoryTheory.Category.id_comp _
end Structural

/-- Substituting coefficient indices commutes with the entire actual
input comparison. Both source and target equality casts are included. -/
theorem coefficient_reindex {I : Type} (g : I → NumericalTuples.Object) (p : SyntaxPolynomial I)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    (componentNormalized E.inverse.obj id (fun X => E.counitIso.app X)
      (p.mapCoefficients g) (p.mapCoefficients (fun i => E.inverse.obj (g i))) (p.mapCoefficients g)
      (mapCoefficients_comp g E.inverse.obj p) (mapCoefficients_id (p.mapCoefficients g)) A).hom =
      (SyntaxPolynomialTransport.component E (fun i => E.inverse.obj (g i)) g
        (fun i => E.counitIso.app (g i)) p A).hom := by
  induction p with
  | term => simp [componentNormalized,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component]
  | formula => simp [componentNormalized,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component]
  | coefficient i => simp [componentNormalized,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component]
  | unit => simp [componentNormalized,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval,
      SyntaxPolynomialTransport.component]
  | product p q hp hq =>
      change (componentNormalized E.inverse.obj id (fun X => E.counitIso.app X)
        (.product (p.mapCoefficients g) (q.mapCoefficients g))
        (.product (p.mapCoefficients (fun i => E.inverse.obj (g i)))
          (q.mapCoefficients (fun i => E.inverse.obj (g i))))
        (.product (p.mapCoefficients g) (q.mapCoefficients g))
        (congrArg₂ SyntaxPolynomial.product (mapCoefficients_comp g E.inverse.obj p)
          (mapCoefficients_comp g E.inverse.obj q))
        (congrArg₂ SyntaxPolynomial.product (mapCoefficients_id (p.mapCoefficients g))
          (mapCoefficients_id (q.mapCoefficients g))) A).hom = _
      rw [normalized_product E.inverse.obj id (fun X => E.counitIso.app X)
        (p.mapCoefficients g) (q.mapCoefficients g)
        (p.mapCoefficients (fun i => E.inverse.obj (g i)))
        (q.mapCoefficients (fun i => E.inverse.obj (g i)))
        (p.mapCoefficients g) (q.mapCoefficients g)
        (mapCoefficients_comp g E.inverse.obj p) (mapCoefficients_comp g E.inverse.obj q)
        (mapCoefficients_id (p.mapCoefficients g)) (mapCoefficients_id (q.mapCoefficients g)) A]
      change prodComparison E.functor _ _ ≫ prod.map _ _ =
        prodComparison E.functor _ _ ≫ prod.map _ _
      rw [hp,hq]
  | sum p q hp hq =>
      change (componentNormalized E.inverse.obj id (fun X => E.counitIso.app X)
        (.sum (p.mapCoefficients g) (q.mapCoefficients g))
        (.sum (p.mapCoefficients (fun i => E.inverse.obj (g i)))
          (q.mapCoefficients (fun i => E.inverse.obj (g i))))
        (.sum (p.mapCoefficients g) (q.mapCoefficients g))
        (congrArg₂ SyntaxPolynomial.sum (mapCoefficients_comp g E.inverse.obj p)
          (mapCoefficients_comp g E.inverse.obj q))
        (congrArg₂ SyntaxPolynomial.sum (mapCoefficients_id (p.mapCoefficients g))
          (mapCoefficients_id (q.mapCoefficients g))) A).hom = _
      rw [normalized_sum E.inverse.obj id (fun X => E.counitIso.app X)
        (p.mapCoefficients g) (q.mapCoefficients g)
        (p.mapCoefficients (fun i => E.inverse.obj (g i)))
        (q.mapCoefficients (fun i => E.inverse.obj (g i)))
        (p.mapCoefficients g) (q.mapCoefficients g)
        (mapCoefficients_comp g E.inverse.obj p) (mapCoefficients_comp g E.inverse.obj q)
        (mapCoefficients_id (p.mapCoefficients g)) (mapCoefficients_id (q.mapCoefficients g)) A]
      change inv (coprodComparison E.functor _ _) ≫ coprod.map _ _ =
        inv (coprodComparison E.functor _ _) ≫ coprod.map _ _
      rw [hp,hq]

section RawReindex
variable {p q p' q' : SyntaxPolynomial (PredicateCategory 𝗧𝗔)}

def reindexReflIso (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    NumericalSyntaxTreeChart.reindexAlgebra rfl rfl A ≅ A :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    apply Prod.ext
    · simp [NumericalSyntaxTreeChart.reindexAlgebra,NumericalSyntaxTreeChart.reindexComparison,
        AlgebraTransport.mappedAlgebra]
      change A.str.1 = 𝟙 (p.eval.obj A.a) ≫ 𝟙 (p.eval.obj A.a) ≫ 𝟙 (p.eval.obj A.a) ≫ A.str.1
      simp only [CategoryTheory.Category.id_comp]
    · simp [NumericalSyntaxTreeChart.reindexAlgebra,NumericalSyntaxTreeChart.reindexComparison,
        AlgebraTransport.mappedAlgebra]
      change A.str.2 = 𝟙 (q.eval.obj A.a) ≫ 𝟙 (q.eval.obj A.a) ≫ 𝟙 (q.eval.obj A.a) ≫ A.str.2
      simp only [CategoryTheory.Category.id_comp])

def reindexPlainIso (hp : p = p') (hq : q = q') :
    NumericalSyntaxTreeChart.reindexAlgebra hp hq (plainPostfixAlgebra 𝗧𝗔 p q) ≅
      plainPostfixAlgebra 𝗧𝗔 p' q' := by
  cases hp
  cases hq
  exact reindexReflIso (plainPostfixAlgebra 𝗧𝗔 p q)

/-- Equality transport of raw words fixes their scalar value in every
TA model. It is proved before the actual parser predicates are supplied. -/
theorem predicate_eq_value {C D : PredicateCategory 𝗧𝗔} (h : C = D)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗧𝗔] (x : SyntacticLists.Obj 𝗧𝗔 M C) :
    ((SyntacticLists.F 𝗧𝗔 M).map (eqToHom h) x).val = x.val := by
  cases h
  exact congrArg Subtype.val (congrArg (fun f => f x) ((SyntacticLists.F 𝗧𝗔 M).map_id C))
end RawReindex
section DirectProjection
variable (σ : ℕ → PredicateCategory 𝗣𝗔) (τ : ℕ → NumericalTuples.Object) (N : ℕ)
  (hp : (SyntaxPolynomial.constructors σ N).mapCoefficients K.obj = SyntaxPolynomial.constructors τ N)

def constructorInputIsoTo (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.obj ((SyntaxPolynomial.constructors σ N).eval.obj A) ≅
      (SyntaxPolynomial.constructors τ N).eval.obj ((K.prod K).obj A) :=
  Polynomial.normalizedComponent id (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors τ N)
    (mapCoefficients_id _) hp A

theorem constructorInputIso_naturalTo {A B : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    (f : A ⟶ B) :
    K.map ((SyntaxPolynomial.constructors σ N).eval.map f) ≫ (constructorInputIsoTo σ τ N hp B).hom =
      (constructorInputIsoTo σ τ N hp A).hom ≫
        (SyntaxPolynomial.constructors τ N).eval.map ((K.prod K).map f) :=
  Polynomial.normalizedComponent_natural id (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors τ N)
    (mapCoefficients_id _) hp f

def oneSortInputIsoTo (X : PredicateCategory 𝗣𝗔) :
    K.obj ((constructorFunctor σ N).obj X) ≅
      (constructorFunctor τ N).obj (K.obj X) :=
  constructorInputIsoTo σ τ N hp (X,⊤_ (PredicateCategory 𝗣𝗔)) ≪≫
    (SyntaxPolynomial.constructors τ N).eval.mapIso
      ((@Iso.refl NumericalTuples.Object inferInstance (K.obj X)).prod (asIso (terminalComparison K)))

/-- This is mapping of the displayed polynomial algebra only. -/
def mappedJointAlgebraTo
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    Endofunctor.Algebra
      (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors τ N) .unit) where
  a := (K.prod K).obj A.a
  str := ((constructorInputIsoTo σ τ N hp A.a).inv ≫ K.map A.str.1,
    (asIso (terminalComparison K)).inv ≫ K.map A.str.2)

def mappedOneSortAlgebraTo (B : Endofunctor.Algebra (constructorFunctor σ N)) :
    Endofunctor.Algebra (constructorFunctor τ N) where
  a := K.obj B.a
  str := (oneSortInputIsoTo σ τ N hp B.a).inv ≫ K.map B.str

/-- The entire projection square is proved before any postfix carrier
or constructor operation is substituted. -/
theorem projection_squareTo
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    K.map (constructorProjection σ N A) ≫ (oneSortInputIsoTo σ τ N hp A.a.1).hom =
      (constructorInputIsoTo σ τ N hp A.a).hom ≫
        constructorProjection τ N (mappedJointAlgebraTo σ τ N hp A) := by
  let sourceLeg : @Quiver.Hom (PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) inferInstance
      A.a (A.a.1,⊤_ (PredicateCategory 𝗣𝗔)) := (𝟙 A.a.1,terminal.from A.a.2)
  let terminalLeg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj (A.a.1,⊤_ (PredicateCategory 𝗣𝗔)))
      (K.obj A.a.1,⊤_ NumericalTuples.Object) := (𝟙 _,terminalComparison K)
  let targetLeg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj A.a) (K.obj A.a.1,⊤_ NumericalTuples.Object) :=
    (𝟙 _,terminal.from (K.obj A.a.2))
  have he : (K.prod K).map sourceLeg ≫ terminalLeg = targetLeg := by
    apply Prod.ext
    · change K.map (𝟙 A.a.1) ≫ 𝟙 (K.obj A.a.1) = 𝟙 (K.obj A.a.1)
      rw [CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp]
    · exact terminal.hom_ext _ _
  change K.map ((SyntaxPolynomial.constructors σ N).eval.map sourceLeg) ≫
      ((constructorInputIsoTo σ τ N hp (A.a.1,⊤_ (PredicateCategory 𝗣𝗔))).hom ≫
        (SyntaxPolynomial.constructors τ N).eval.map terminalLeg) =
      (constructorInputIsoTo σ τ N hp A.a).hom ≫
        (SyntaxPolynomial.constructors τ N).eval.map targetLeg
  rw [← CategoryTheory.Category.assoc,constructorInputIso_naturalTo,CategoryTheory.Category.assoc,← CategoryTheory.Functor.map_comp,he]

/-- Mapping and first-sort projection give the same actual structure
morphism. The inverse projection maps are justified by the existing
constructor-polynomial theorem, including arity zero. -/
theorem projected_mapping_strTo
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    (mappedOneSortAlgebraTo σ τ N hp (projectedConstructorAlgebra σ N A)).str =
      (projectedConstructorAlgebra τ N (mappedJointAlgebraTo σ τ N hp A)).str := by
  let sourceProjection := constructorProjection σ N A
  let targetProjection := constructorProjection τ N (mappedJointAlgebraTo σ τ N hp A)
  let a := constructorInputIsoTo σ τ N hp A.a
  let b := oneSortInputIsoTo σ τ N hp A.a.1
  let _ : IsIso sourceProjection := constructorProjection_isIso σ N A
  let _ : IsIso targetProjection := constructorProjection_isIso _ _ _
  have hprojection : K.map sourceProjection ≫ b.hom = a.hom ≫ targetProjection := projection_squareTo σ τ N hp A
  have hs : K.map sourceProjection ≫ K.map (inv sourceProjection) =
      𝟙 (K.obj ((SyntaxPolynomial.constructors σ N).eval.obj A.a)) :=
    (K.map_comp sourceProjection (inv sourceProjection)).symm.trans
      ((congrArg K.map (IsIso.hom_inv_id sourceProjection)).trans (K.map_id _))
  apply (cancel_epi (K.map sourceProjection ≫ b.hom)).mp
  change (K.map sourceProjection ≫ b.hom) ≫
      (b.inv ≫ K.map (inv sourceProjection ≫ A.str.1)) =
    (K.map sourceProjection ≫ b.hom) ≫
      (inv targetProjection ≫ a.inv ≫ K.map A.str.1)
  calc
    _ = K.map A.str.1 := by
      simp only [CategoryTheory.Functor.map_comp,CategoryTheory.Category.assoc,Iso.hom_inv_id_assoc]
      rw [← CategoryTheory.Category.assoc,hs,CategoryTheory.Category.id_comp]
    _ = _ := by
      rw [hprojection]
      simp only [CategoryTheory.Category.assoc,IsIso.hom_inv_id_assoc,Iso.hom_inv_id_assoc]

def projectedMappingIsoTo
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    mappedOneSortAlgebraTo σ τ N hp (projectedConstructorAlgebra σ N A) ≅
      projectedConstructorAlgebra τ N (mappedJointAlgebraTo σ τ N hp A) :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (constructorFunctor τ N).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp,CategoryTheory.Category.comp_id,projected_mapping_strTo])

/-- The normalized source-pair structure and the direct constructor
mapping differ only by the explicit unit comparison. -/
def sourceMappedPairIsoTo
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    Initial.mappedSourcePair id (SyntaxPolynomial.constructors σ N) .unit
      (SyntaxPolynomial.constructors σ N) .unit (SyntaxPolynomial.constructors τ N) .unit
      (mapCoefficients_id _) rfl hp rfl A ≅ mappedJointAlgebraTo σ τ N hp A :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors τ N) .unit).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp,CategoryTheory.Category.comp_id]
    apply Prod.ext
    · rfl
    · simp [Initial.mappedSourcePair,mappedJointAlgebraTo,Polynomial.normalizedComponent,
        Polynomial.component,CategoryTheory.Category.assoc]
      change K.map A.str.2 = terminalComparison K ≫ 𝟙 (⊤_ NumericalTuples.Object) ≫
        inv (terminalComparison K) ≫ K.map A.str.2
      rw [CategoryTheory.Category.id_comp,IsIso.hom_inv_id_assoc])
@[simp] theorem projectedMappingIsoTo_hom_f
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    (projectedMappingIsoTo σ τ N hp A).hom.f = 𝟙 (K.obj A.a.1) := rfl

@[simp] theorem sourceMappedPairIsoTo_hom_f
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    (sourceMappedPairIsoTo σ τ N hp A).hom.f = 𝟙 ((K.prod K).obj A.a) := rfl

@[simp] theorem sourceMappedPairIsoTo_inv_f
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    (sourceMappedPairIsoTo σ τ N hp A).inv.f = 𝟙 ((K.prod K).obj A.a) := rfl

end DirectProjection


private theorem constructors_eq_of_bounded {I : Type} (σ τ : ℕ → I) (n : ℕ)
    (h : ∀ k ≤ n, σ k = τ k) : SyntaxPolynomial.constructors σ n = SyntaxPolynomial.constructors τ n := by
  induction n with
  | zero => simp only [SyntaxPolynomial.constructors,h 0 (Nat.le_refl 0)]
  | succ n ih =>
    have hp := ih (fun k hk => h k (Nat.le_trans hk (Nat.le_succ n)))
    simp only [SyntaxPolynomial.constructors,hp,h (n+1) (Nat.le_refl (n+1))]

/-- The finite constructor polynomial agrees at every used rule arity;
unused coefficient objects are never equated. -/
theorem interpreted_constructor_polynomial {F : PredicateCategory 𝗣𝗔} {N : ℕ}
    (R : RulePresentation F N) :
    (SyntaxPolynomial.constructors (SyntacticDerivation.PolynomialComparison.coefficients R) N).mapCoefficients K.obj =
      SyntaxPolynomial.constructors (SyntacticDerivation.PolynomialComparison.coefficients (interpretedRules R)) N := by
  rw [SyntaxOperationsTransport.mapCoefficients_constructors]
  apply constructors_eq_of_bounded
  intro k hk
  simp only [SyntacticDerivation.PolynomialComparison.coefficients,dite_eq_left hk,interpretedRules]

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordCoherence
