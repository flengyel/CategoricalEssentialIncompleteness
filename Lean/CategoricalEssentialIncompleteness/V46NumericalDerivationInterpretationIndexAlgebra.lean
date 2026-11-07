/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationWordCoherence

/-! # Full algebra comparison after substituting coefficient indices -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.IndexAlgebra
open SyntacticSyntax WordCoherence

section Raw
variable {a b a' b' : SyntaxPolynomial (PredicateCategory 𝗧𝗔)}
  (ha : a = a') (hb : b = b')
  (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))

def rawReindexed : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a' b') where
  a := (A).a
  str := ((eqToIso (congrArg (fun p => (SyntaxPolynomial.eval p).obj (A).a) ha)).inv ≫ (A).str.1,
    (eqToIso (congrArg (fun p => (SyntaxPolynomial.eval p).obj (A).a) hb)).inv ≫ (A).str.2)

def rawReindexedIso : NumericalSyntaxTreeChart.reindexAlgebra ha hb A ≅ rawReindexed ha hb A := by
  cases ha
  cases hb
  refine Endofunctor.Algebra.isoMk (Iso.refl _) ?_
  apply Prod.ext
  · simp [NumericalSyntaxTreeChart.reindexAlgebra,NumericalSyntaxTreeChart.reindexComparison,
      AlgebraTransport.mappedAlgebra,rawReindexed]
    change (𝟙 (a.eval.obj A.a)) ≫ A.str.1 =
      (𝟙 (a.eval.obj A.a)) ≫ (𝟙 (a.eval.obj A.a)) ≫ (𝟙 (a.eval.obj A.a)) ≫ A.str.1
    simp only [CategoryTheory.Category.id_comp]
  · simp [NumericalSyntaxTreeChart.reindexAlgebra,NumericalSyntaxTreeChart.reindexComparison,
      AlgebraTransport.mappedAlgebra,rawReindexed]
    change (𝟙 (b.eval.obj A.a)) ≫ A.str.2 =
      (𝟙 (b.eval.obj A.a)) ≫ (𝟙 (b.eval.obj A.a)) ≫ (𝟙 (b.eval.obj A.a)) ≫ A.str.2
    simp only [CategoryTheory.Category.id_comp]

@[simp] theorem rawReindexedIso_hom_f : (rawReindexedIso ha hb A).hom.f = 𝟙 A.a := by
  cases ha
  cases hb
  rfl
@[simp] theorem rawReindexedIso_inv_f : (rawReindexedIso ha hb A).inv.f = 𝟙 A.a := by
  cases ha
  cases hb
  rfl
end Raw

section Mapping
variable {I : Type} (g : I → NumericalTuples.Object) (p q : SyntaxPolynomial I)
local notation "f" => fun i => NumericalSyntaxTreeChart.E.inverse.obj (g i)
local notation "χ" => fun i => NumericalSyntaxTreeChart.E.counitIso.app (g i)
local notation "hp" => mapCoefficients_comp g NumericalSyntaxTreeChart.E.inverse.obj p
local notation "hq" => mapCoefficients_comp g NumericalSyntaxTreeChart.E.inverse.obj q
local notation "pN" => p.mapCoefficients g
local notation "qN" => q.mapCoefficients g

/-- Inverting the entire structural coherence equation includes both
object-equality legs. -/
theorem coefficient_inverse (r : SyntaxPolynomial I)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    (eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj (((E).prod E).functor.obj A))
      (mapCoefficients_id (r.mapCoefficients g)))).inv ≫
        (SyntaxPolynomialTransport.component E (E).inverse.obj id (fun X => (E).counitIso.app X)
          (r.mapCoefficients g) A).inv =
      (SyntaxPolynomialTransport.component E (fun i => (E).inverse.obj (g i)) g
        (fun i => (E).counitIso.app (g i)) r A).inv ≫
        (E).functor.map (eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj A)
          (mapCoefficients_comp g (E).inverse.obj r))).inv := by
  have he : componentNormalized (E).inverse.obj id (fun X => (E).counitIso.app X)
      (r.mapCoefficients g) (r.mapCoefficients (fun i => (E).inverse.obj (g i)))
      (r.mapCoefficients g) (mapCoefficients_comp g (E).inverse.obj r)
      (mapCoefficients_id (r.mapCoefficients g)) A =
      SyntaxPolynomialTransport.component E (fun i => (E).inverse.obj (g i)) g
        (fun i => (E).counitIso.app (g i)) r A := Iso.ext (coefficient_reindex g r A)
  have hi := congrArg (fun i => i.inv) he
  have hh := congrArg (fun k => k ≫ (E).functor.map
    (eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj A)
      (mapCoefficients_comp g (E).inverse.obj r))).inv) hi
  simpa only [componentNormalized,Iso.trans_inv,Iso.symm_inv,CategoryTheory.Functor.mapIso_hom,
    Category.assoc,← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,CategoryTheory.Functor.map_id,Category.comp_id] using hh

/-- Postcomposing the proved inverse coherence with an arbitrary algebra
operation preserves the full coefficient-index comparison. -/
theorem coefficient_structure (r : SyntaxPolynomial I)
    (X : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) (Z : PredicateCategory 𝗧𝗔)
    (u : ((r.mapCoefficients g).mapCoefficients (E).inverse.obj).eval.obj X ⟶ Z) :
    (SyntaxPolynomialTransport.component E f g χ r X).inv ≫
      (E).functor.map ((eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj X)
        (mapCoefficients_comp g (E).inverse.obj r))).inv ≫ u) =
      (eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj (((E).prod E).functor.obj X))
        (mapCoefficients_id (r.mapCoefficients g)))).inv ≫
        (SyntaxPolynomialTransport.component E (E).inverse.obj id (fun Y => (E).counitIso.app Y)
          (r.mapCoefficients g) X).inv ≫ (E).functor.map u := by
  rw [(E).functor.map_comp, ← Category.assoc, ← coefficient_inverse g r X, Category.assoc]

def standardExplicit (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((pN).mapCoefficients (E).inverse.obj) ((qN).mapCoefficients (E).inverse.obj))) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor pN qN) :=
  Initial.reindexedPairAlgebra (mapCoefficients_id pN) (mapCoefficients_id qN)
    (AlgebraTransport.mappedAlgebra ((E).prod E)
      (SyntaxPolynomialTransport.jointIso E (E).inverse.obj id (fun X => (E).counitIso.app X) pN qN) A)

def templateFunctor :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (p.mapCoefficients f) (q.mapCoefficients f)) ⥤
      Endofunctor.Algebra (SyntaxPolynomial.jointFunctor pN qN) :=
  AlgebraTransport.functor ((E).prod E) (SyntaxPolynomialTransport.jointIso E f g χ p q)

def coefficientMappingIso (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((pN).mapCoefficients (E).inverse.obj) ((qN).mapCoefficients (E).inverse.obj))) :
    standardExplicit g p q A ≅
    (templateFunctor g p q).obj (rawReindexed hp hq A) :=
  Endofunctor.Algebra.isoMk
    (A₀ := standardExplicit g p q A)
    (A₁ := (templateFunctor g p q).obj (rawReindexed hp hq A))
    (Iso.refl (((E).prod E).functor.obj A.a)) (by
    apply Prod.ext
    · change ((pN).eval.map (𝟙 (((E).prod E).functor.obj A.a))) ≫
        ((SyntaxPolynomialTransport.component E f g χ p A.a).inv ≫
          (E).functor.map ((eqToIso (congrArg (fun r => (SyntaxPolynomial.eval r).obj A.a) hp)).inv ≫ A.str.1)) =
      ((eqToIso (congrArg (fun r => (SyntaxPolynomial.eval r).obj (((E).prod E).functor.obj A.a))
        (mapCoefficients_id pN))).inv ≫
          (SyntaxPolynomialTransport.component E (E).inverse.obj id (fun X => (E).counitIso.app X) pN A.a).inv ≫
            (E).functor.map A.str.1) ≫ 𝟙 ((E).functor.obj A.a.1)
      rw [(SyntaxPolynomial.eval pN).map_id, Category.id_comp, Category.comp_id]
      exact coefficient_structure g p A.a A.a.1 A.str.1
    · change ((qN).eval.map (𝟙 (((E).prod E).functor.obj A.a))) ≫
        ((SyntaxPolynomialTransport.component E f g χ q A.a).inv ≫
          (E).functor.map ((eqToIso (congrArg (fun r => (SyntaxPolynomial.eval r).obj A.a) hq)).inv ≫ A.str.2)) =
      ((eqToIso (congrArg (fun r => (SyntaxPolynomial.eval r).obj (((E).prod E).functor.obj A.a))
        (mapCoefficients_id qN))).inv ≫
          (SyntaxPolynomialTransport.component E (E).inverse.obj id (fun X => (E).counitIso.app X) qN A.a).inv ≫
            (E).functor.map A.str.2) ≫ 𝟙 ((E).functor.obj A.a.2)
      rw [(SyntaxPolynomial.eval qN).map_id, Category.id_comp, Category.comp_id]
      exact coefficient_structure g q A.a A.a.2 A.str.2)


@[simp] theorem coefficientMappingIso_hom_f
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((pN).mapCoefficients (E).inverse.obj) ((qN).mapCoefficients (E).inverse.obj))) :
    (coefficientMappingIso g p q A).hom.f = 𝟙 (((E).prod E).functor.obj A.a) := rfl
end Mapping

theorem outputReindex_hom_f {p q p' q' : SyntaxPolynomial NumericalTuples.Object}
    (hp : p = p') (hq : q = q')
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    (Initial.reindexedPairIso hp hq A).hom.f = 𝟙 (A).a := by
  cases hp
  cases hq
  rfl

/-- A word value is compared through its proved numerical presentation
chart, without identifying an arbitrary inverse chart with a scalar. -/
def WordValue (C D : PredicateCategory 𝗧𝗔) (f : (E).functor.obj C ⟶ (E).functor.obj D) : Prop :=
  ∀ x : NumericalTuples.Point ((E).functor.obj C),
    ((NumericalSyntaxTreeChart.wordPresentationIso D).hom.toFun (f.toFun x)).val =
      ((NumericalSyntaxTreeChart.wordPresentationIso C).hom.toFun x).val

theorem reindexPlain_word {a b a' b' : SyntaxPolynomial (PredicateCategory 𝗧𝗔)}
    (ha : a = a') (hb : b = b') :
    WordValue (plainPostfixAlgebra 𝗧𝗔 a b).a.1 (plainPostfixAlgebra 𝗧𝗔 a' b').a.1
      ((E).functor.map (reindexPlainIso ha hb).hom.f.1) := by
  cases ha
  cases hb
  intro x
  have he : (reindexPlainIso (p := a) (q := b) rfl rfl).hom.f.1 = 𝟙 (plainPostfixAlgebra 𝗧𝗔 a b).a.1 := rfl
  rw [he]
  change ((NumericalSyntaxTreeChart.wordPresentationIso (plainPostfixAlgebra 𝗧𝗔 a b).a.1).hom.toFun
      (((E).functor.map (𝟙 (plainPostfixAlgebra 𝗧𝗔 a b).a.1)).toFun x)).val =
    ((NumericalSyntaxTreeChart.wordPresentationIso (plainPostfixAlgebra 𝗧𝗔 a b).a.1).hom.toFun x).val
  rw [CategoryTheory.Functor.map_id]
  rfl

def firstCarrierIso {p q : SyntaxPolynomial NumericalTuples.Object}
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)} (i : A ≅ B) : (A).a.1 ≅ (B).a.1 where
  hom := i.hom.f.1
  inv := i.inv.f.1
  hom_inv_id := congrArg (fun f => f.f.1) i.hom_inv_id
  inv_hom_id := congrArg (fun f => f.f.1) i.inv_hom_id

theorem WordValue.inverse {C D : PredicateCategory 𝗧𝗔} (i : (E).functor.obj C ≅ (E).functor.obj D)
    (h : WordValue C D i.hom) : WordValue D C i.inv := by
  intro y
  have hh := h (i.inv.toFun y)
  have he : i.hom.toFun (i.inv.toFun y) = y :=
    congrArg (fun f => f.toFun y) i.inv_hom_id
  rw [he] at hh
  exact hh.symm

section Arithmetic
variable (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
local notation "pN" => SyntaxPolynomial.mapCoefficients K.obj p
local notation "qN" => SyntaxPolynomial.mapCoefficients K.obj q
local notation "hp" => mapCoefficients_comp K.obj NumericalSyntaxTreeChart.E.inverse.obj p
local notation "hq" => mapCoefficients_comp K.obj NumericalSyntaxTreeChart.E.inverse.obj q
local notation "c" => fun C : PredicateCategory 𝗣𝗔 => Iso.symm (NumericalSyntaxTreeChart.E.counitIso.app (K.obj C))
local notation "A" => NumericalSyntaxTreeChart.rawPairAlgebra pN qN
local notation "B" => plainPostfixAlgebra 𝗧𝗔 (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)

def templateLiteralIso :
    (templateFunctor K.obj p q).obj B ≅
      Initial.mappedLiteralPair id labelMap c p q (p.mapCoefficients labelMap)
        (q.mapCoefficients labelMap) pN qN rfl rfl rfl rfl B :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (SyntaxPolynomial.jointFunctor pN qN).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]
    apply Prod.ext
    · simp [templateFunctor,AlgebraTransport.functor,AlgebraTransport.mappedAlgebra,
        Initial.mappedLiteralPair,Polynomial.normalizedLiteralComponent,SyntaxPolynomialTransport.jointIso]
      rfl
    · simp [templateFunctor,AlgebraTransport.functor,AlgebraTransport.mappedAlgebra,
        Initial.mappedLiteralPair,Polynomial.normalizedLiteralComponent,SyntaxPolynomialTransport.jointIso]
      rfl)

/-- This is an isomorphism of the complete term/formula algebras,
constructed from the structural coefficient equation and raw equality
transport. No constructor equation is a supplied premise. -/
def normalizedTemplateIso : NumericalSyntaxTreeChart.normalizedPair pN qN ≅
    Initial.mappedLiteralPair id labelMap c p q (p.mapCoefficients labelMap)
      (q.mapCoefficients labelMap) pN qN rfl rfl rfl rfl B :=
  Initial.reindexedPairIso (mapCoefficients_id pN) (mapCoefficients_id qN) _ ≪≫
    coefficientMappingIso K.obj p q A ≪≫
      (templateFunctor K.obj p q).mapIso
        ((rawReindexedIso hp hq A).symm ≪≫ reindexPlainIso hp hq) ≪≫
          templateLiteralIso p q

theorem normalizedTemplateIso_f : (normalizedTemplateIso p q).hom.f =
    ((E).prod E).functor.map (reindexPlainIso hp hq).hom.f := by
  simp only [normalizedTemplateIso,Iso.trans_hom,Endofunctor.Algebra.comp_f,
    outputReindex_hom_f,coefficientMappingIso_hom_f,templateLiteralIso,
    Endofunctor.Algebra.isoMk_hom_f,Iso.refl_hom,
    CategoryTheory.Functor.mapIso_hom,templateFunctor,AlgebraTransport.functor,rawReindexedIso_inv_f,
    Iso.symm_hom]
  change ((E).prod E).functor.map (𝟙 (A).a ≫ (reindexPlainIso hp hq).hom.f) = _
  rw [Category.id_comp]

theorem normalizedTemplateIso_word :
    WordValue (A).a.1 (B).a.1 (normalizedTemplateIso p q).hom.f.1 := by
  rw [normalizedTemplateIso_f]
  exact reindexPlain_word hp hq

theorem normalizedTemplateIso_inverse_word :
    WordValue (B).a.1 (A).a.1 (normalizedTemplateIso p q).inv.f.1 :=
  WordValue.inverse (C := (A).a.1) (D := (B).a.1) (firstCarrierIso (normalizedTemplateIso p q)) (normalizedTemplateIso_word p q)

/-- Equality induction changes the whole algebra, including the raw
carrier guards, before concrete constructor polynomials are substituted. -/
def normalizedTemplateIsoTo (pN' qN' : SyntaxPolynomial NumericalTuples.Object)
    (hpN : p.mapCoefficients K.obj = pN') (hqN : q.mapCoefficients K.obj = qN') :
    NumericalSyntaxTreeChart.normalizedPair pN' qN' ≅
      Initial.mappedLiteralPair id labelMap c p q (p.mapCoefficients labelMap)
        (q.mapCoefficients labelMap) pN' qN' rfl rfl hpN hqN B := by
  cases hpN
  cases hqN
  exact normalizedTemplateIso p q

theorem normalizedTemplateIsoTo_word (pN' qN' : SyntaxPolynomial NumericalTuples.Object)
    (hpN : p.mapCoefficients K.obj = pN') (hqN : q.mapCoefficients K.obj = qN') :
    WordValue (NumericalSyntaxTreeChart.rawPairAlgebra pN' qN').a.1 (B).a.1
      (normalizedTemplateIsoTo p q pN' qN' hpN hqN).hom.f.1 := by
  cases hpN
  cases hqN
  exact normalizedTemplateIso_word p q

theorem normalizedTemplateIsoTo_inverse_word (pN' qN' : SyntaxPolynomial NumericalTuples.Object)
    (hpN : p.mapCoefficients K.obj = pN') (hqN : q.mapCoefficients K.obj = qN') :
    WordValue (B).a.1 (NumericalSyntaxTreeChart.rawPairAlgebra pN' qN').a.1
      (normalizedTemplateIsoTo p q pN' qN' hpN hqN).inv.f.1 := by
  cases hpN
  cases hqN
  exact normalizedTemplateIso_inverse_word p q

end Arithmetic

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.IndexAlgebra
