/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonBundle

/-! # Explicit polynomial equalities in the concrete named comparison

Only literal mapCoefficients expression equalities are normalized here.
The carrier comparisons are proved by dependent equality elimination;
there is no assumption that an equivalence counit fixes scalar codes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)

def normalizedComponent (a : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r : SyntaxPolynomial (Total.TotalCategory P))
    (h : Syntax.Polynomial.mapped P a=r) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (F).obj (a.eval.obj X) ≅ r.eval.obj ((FP).obj X) :=
  Syntax.Polynomial.component P a X ≪≫ eqToIso (congrArg (fun p => p.eval.obj ((FP).obj X)) h)

def normalizedJointIso (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s) :
    SyntaxPolynomial.jointFunctor a b ⋙ (FP) ≅ (FP) ⋙ SyntaxPolynomial.jointFunctor r s :=
  Syntax.Polynomial.jointIso P a b ≪≫
    eqToIso (congrArg (fun J => (FP) ⋙ J) (congrArg₂ SyntaxPolynomial.jointFunctor ha hb))

theorem normalizedJointIso_first (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    ((normalizedJointIso P a b r s ha hb).hom.app X).1=(normalizedComponent P a r ha X).hom := by
  cases ha
  cases hb
  rfl

theorem normalizedJointIso_second (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    ((normalizedJointIso P a b r s ha hb).hom.app X).2=(normalizedComponent P b s hb X).hom := by
  cases ha
  cases hb
  rfl

theorem normalizedComponent_product (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    normalizedComponent P (.product a b) (.product r s) (congrArg₂ SyntaxPolynomial.product ha hb) X=
      asIso (prodComparison (F) (a.eval.obj X) (b.eval.obj X)) ≪≫
        prod.mapIso (normalizedComponent P a r ha X) (normalizedComponent P b s hb X) := by
  cases ha
  cases hb
  apply Iso.ext
  simp only [normalizedComponent,Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,
    Iso.refl_hom,Category.comp_id,prod.mapIso_hom]

theorem normalizedComponent_sum (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X=
      (asIso (coprodComparison (F) (a.eval.obj X) (b.eval.obj X))).symm ≪≫
        coprod.mapIso (normalizedComponent P a r ha X) (normalizedComponent P b s hb X) := by
  cases ha
  cases hb
  apply Iso.ext
  simp only [normalizedComponent,Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,
    Iso.refl_hom,Category.comp_id,coprod.mapIso_hom]

theorem normalizedComponent_inl (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (F).map (coprod.inl : a.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) ≫
      (normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X).hom=
        (normalizedComponent P a r ha X).hom ≫
          (coprod.inl : r.eval.obj ((FP).obj X) ⟶ r.eval.obj ((FP).obj X) ⨿ s.eval.obj ((FP).obj X)) := by
  cases ha
  cases hb
  simp only [normalizedComponent,Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,
    Iso.refl_hom,Category.comp_id,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    ← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]

theorem normalizedComponent_inr (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (F).map (coprod.inr : b.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) ≫
      (normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X).hom=
        (normalizedComponent P b s hb X).hom ≫
          (coprod.inr : s.eval.obj ((FP).obj X) ⟶ r.eval.obj ((FP).obj X) ⨿ s.eval.obj ((FP).obj X)) := by
  cases ha
  cases hb
  simp only [normalizedComponent,Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,
    Iso.refl_hom,Category.comp_id,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    ← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]

theorem normalizedComponent_fst (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (normalizedComponent P (.product a b) (.product r s) (congrArg₂ SyntaxPolynomial.product ha hb) X).hom ≫
      (prod.fst : r.eval.obj ((FP).obj X) ⨯ s.eval.obj ((FP).obj X) ⟶ r.eval.obj ((FP).obj X))=
      (F).map (prod.fst : a.eval.obj X ⨯ b.eval.obj X ⟶ a.eval.obj X) ≫
        (normalizedComponent P a r ha X).hom := by
  cases ha
  cases hb
  simp only [normalizedComponent,Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,
    Iso.refl_hom,Category.comp_id,prod.mapIso_hom,Category.assoc,prod.map_fst,asIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (Syntax.Polynomial.component P a X).hom)
      (prodComparison_fst (F) (a.eval.obj X) (b.eval.obj X)))

theorem normalizedComponent_snd (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    (normalizedComponent P (.product a b) (.product r s) (congrArg₂ SyntaxPolynomial.product ha hb) X).hom ≫
      (prod.snd : r.eval.obj ((FP).obj X) ⨯ s.eval.obj ((FP).obj X) ⟶ s.eval.obj ((FP).obj X))=
      (F).map (prod.snd : a.eval.obj X ⨯ b.eval.obj X ⟶ b.eval.obj X) ≫
        (normalizedComponent P b s hb X).hom := by
  cases ha
  cases hb
  simp only [normalizedComponent,Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,
    Iso.refl_hom,Category.comp_id,prod.mapIso_hom,Category.assoc,prod.map_snd,asIso_hom]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (Syntax.Polynomial.component P b X).hom)
      (prodComparison_snd (F) (a.eval.obj X) (b.eval.obj X)))

def powerComponent (X : PredicateCategory 𝗣𝗔) (n : ℕ) :=
  normalizedComponent P (SyntaxPolynomial.power .term n) (SyntaxPolynomial.power .term n)
    (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term n) (X,X)

def constructorComponent (σ : ℕ → PredicateCategory 𝗣𝗔) (X : PredicateCategory 𝗣𝗔) (n : ℕ) :=
  normalizedComponent P (SyntaxPolynomial.constructors σ n)
    (SyntaxPolynomial.constructors (fun i => (F).obj (σ i)) n)
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ n) (X,X)

def symbolComponent (C X : PredicateCategory 𝗣𝗔) (n : ℕ) :=
  normalizedComponent P (.product (.coefficient C) (SyntaxPolynomial.power .term n))
    (.product (.coefficient ((F).obj C)) (SyntaxPolynomial.power .term n))
    (congrArg₂ SyntaxPolynomial.product rfl
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term n)) (X,X)

theorem symbolComponent_snd (C X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (symbolComponent P C X n).hom ≫ prod.snd=
      (F).map (prod.snd : C ⨯ (SyntaxPolynomial.power .term n).eval.obj (X,X) ⟶ _) ≫
        (powerComponent P X n).hom := by
  exact normalizedComponent_snd P (.coefficient C) (SyntaxPolynomial.power .term n)
    (.coefficient ((F).obj C)) (SyntaxPolynomial.power .term n) rfl
    (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term n) (X,X)

theorem constructorComponent_zero (σ : ℕ → PredicateCategory 𝗣𝗔) (X : PredicateCategory 𝗣𝗔) :
    constructorComponent P σ X 0=symbolComponent P (σ 0) X 0 := rfl

theorem constructorComponent_inl (σ : ℕ → PredicateCategory 𝗣𝗔) (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (F).map (coprod.inl : (SyntaxPolynomial.constructors σ n).eval.obj (X,X) ⟶
      (SyntaxPolynomial.constructors σ (n+1)).eval.obj (X,X)) ≫ (constructorComponent P σ X (n+1)).hom=
        (constructorComponent P σ X n).hom ≫ coprod.inl := by
  exact normalizedComponent_inl P (SyntaxPolynomial.constructors σ n)
    (.product (.coefficient (σ (n+1))) (SyntaxPolynomial.power .term (n+1)))
    (SyntaxPolynomial.constructors (fun i => (F).obj (σ i)) n)
    (.product (.coefficient ((F).obj (σ (n+1)))) (SyntaxPolynomial.power .term (n+1)))
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ n)
    (congrArg₂ SyntaxPolynomial.product rfl
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (n+1))) (X,X)

theorem constructorComponent_inr (σ : ℕ → PredicateCategory 𝗣𝗔) (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (F).map (coprod.inr : σ (n+1) ⨯ (SyntaxPolynomial.power .term (n+1)).eval.obj (X,X) ⟶
      (SyntaxPolynomial.constructors σ (n+1)).eval.obj (X,X)) ≫ (constructorComponent P σ X (n+1)).hom=
        (symbolComponent P (σ (n+1)) X (n+1)).hom ≫ coprod.inr := by
  exact normalizedComponent_inr P (SyntaxPolynomial.constructors σ n)
    (.product (.coefficient (σ (n+1))) (SyntaxPolynomial.power .term (n+1)))
    (SyntaxPolynomial.constructors (fun i => (F).obj (σ i)) n)
    (.product (.coefficient ((F).obj (σ (n+1)))) (SyntaxPolynomial.power .term (n+1)))
    (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ n)
    (congrArg₂ SyntaxPolynomial.product rfl
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (n+1))) (X,X)

@[simp] theorem powerComponent_zero (X : PredicateCategory 𝗣𝗔) :
    (powerComponent P X 0).hom=terminalComparison (F) := by
  simp only [powerComponent,normalizedComponent,SyntaxPolynomial.power,
    Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,asIso_hom,Category.comp_id]

@[simp] theorem powerComponent_one (X : PredicateCategory 𝗣𝗔) :
    (powerComponent P X 1).hom=𝟙 ((F).obj X) := by
  simp only [powerComponent,normalizedComponent,SyntaxPolynomial.power,
    Syntax.Polynomial.component,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,Category.comp_id,SyntaxPolynomial.eval]
  rfl

theorem powerComponent_succ (X : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (powerComponent P X (n+2)).hom=
      prodComparison (F) ((SyntaxPolynomial.power .term (n+1)).eval.obj (X,X)) X ≫
        prod.map (powerComponent P X (n+1)).hom (𝟙 _) := by
  have h := congrArg Iso.hom (normalizedComponent_product P
    (SyntaxPolynomial.power .term (n+1)) .term (SyntaxPolynomial.power .term (n+1)) .term
    (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term (n+1)) rfl (X,X))
  simpa only [Iso.trans_hom,asIso_hom,prod.mapIso_hom,normalizedComponent,
    eqToIso_refl,Iso.refl_hom,Category.comp_id,Syntax.Polynomial.component,powerComponent,
    SyntaxPolynomial.power,SyntaxPolynomial.eval,CategoryTheory.Prod.fst] using h

def castHom {p q r s : SyntaxPolynomial (Total.TotalCategory P)} (hp : p=r) (hq : q=s)
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)} (f : A ⟶ B) :
    castAlgebra hp hq A ⟶ castAlgebra hp hq B := by
  cases hp
  cases hq
  exact f

theorem castHom_carrier {p q r s : SyntaxPolynomial (Total.TotalCategory P)} (hp : p=r) (hq : q=s)
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)} (f : A ⟶ B) :
    (castHom P hp hq f).f ≫ eqToHom (castAlgebra_carrier hp hq B)=
      eqToHom (castAlgebra_carrier hp hq A) ≫ f.f := by
  cases hp
  cases hq
  simp only [castHom,castAlgebra,eqToHom_refl,Category.comp_id,Category.id_comp]

theorem normalized_mapped_structure (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b)) :
    (normalizedJointIso P a b r s ha hb).hom.app A.a ≫
      (SyntaxPolynomial.jointFunctor r s).map (eqToHom (castAlgebra_carrier ha hb
        (Syntax.Polynomial.mappedAlgebra P a b A)).symm) ≫
      (castAlgebra ha hb (Syntax.Polynomial.mappedAlgebra P a b A)).str ≫
      eqToHom (castAlgebra_carrier ha hb (Syntax.Polynomial.mappedAlgebra P a b A))=
        (FP).map A.str := by
  cases ha
  cases hb
  simp [normalizedJointIso,castAlgebra]
  exact ⟨congrArg Prod.fst (mapped_structure P a b A),
    congrArg Prod.snd (mapped_structure P a b A)⟩

def castedCarrierIso (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s))
    (k : B ≅ castAlgebra ha hb (Syntax.Polynomial.mappedAlgebra P a b A)) : B.a ≅ (FP).obj A.a :=
  (Endofunctor.Algebra.forget _).mapIso k ≪≫
    eqToIso (castAlgebra_carrier ha hb (Syntax.Polynomial.mappedAlgebra P a b A))

theorem normalized_iso_structure (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s))
    (k : B ≅ castAlgebra ha hb (Syntax.Polynomial.mappedAlgebra P a b A)) :
    (FP).map A.str ≫ (castedCarrierIso P a b r s ha hb A B k).inv=
      (normalizedJointIso P a b r s ha hb).hom.app A.a ≫
        (SyntaxPolynomial.jointFunctor r s).map (castedCarrierIso P a b r s ha hb A B k).inv ≫ B.str := by
  cases ha
  cases hb
  simp only [castedCarrierIso,castAlgebra,eqToIso_refl,
    Iso.trans_refl,normalizedJointIso]
  change (FP).map A.str ≫ k.inv.f =
    (Syntax.Polynomial.jointIso P a b).hom.app A.a ≫
      (SyntaxPolynomial.jointFunctor (Syntax.Polynomial.mapped P a) (Syntax.Polynomial.mapped P b)).map
        k.inv.f ≫ B.str
  calc
    _ = ((Syntax.Polynomial.jointIso P a b).hom.app A.a ≫
      (Syntax.Polynomial.mappedAlgebra P a b A).str) ≫ k.inv.f :=
        congrArg (fun f => f ≫ k.inv.f) (mapped_structure P a b A).symm
    _ = _ := by
      have hk := k.inv.h
      change (SyntaxPolynomial.jointFunctor (Syntax.Polynomial.mapped P a)
        (Syntax.Polynomial.mapped P b)).map k.inv.f ≫ B.str =
        (Syntax.Polynomial.mappedAlgebra P a b A).str ≫ k.inv.f at hk
      exact (Category.assoc _ _ _).trans
        (congrArg (fun f => (Syntax.Polynomial.jointIso P a b).hom.app A.a ≫ f) hk.symm)

def normalizedWordPairIso (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) :
    (Syntax.Raw.wordAlgebra r s).a ≅ (FP).obj (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b).a :=
  eqToIso (congrArg₂ (fun p q => (Syntax.Raw.wordAlgebra p q).a) ha hb).symm ≪≫ plainPairIso P a b

theorem normalizedWordAlgebraIso_carrier (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) :
    ((Endofunctor.Algebra.forget _).mapIso (normalizedWordAlgebraIso P a b r s ha hb)) ≪≫
      eqToIso (castAlgebra_carrier ha hb (Syntax.Polynomial.mappedAlgebra P a b
        (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b)))=
          normalizedWordPairIso P a b r s ha hb := by
  cases ha
  cases hb
  apply Iso.ext
  change (wordAlgebraIso P a b).hom.f ≫ 𝟙 _ = 𝟙 _ ≫ (plainPairIso P a b).hom
  rw [Category.comp_id,Category.id_comp]
  exact wordAlgebraIso_f P a b

theorem normalizedWordPairIso_term_graph (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (word output : ℕ) :
    output∈Total.val ((normalizedWordPairIso P a b r s ha hb).hom.1).hom word ↔
      word∈(Syntax.Raw.uniformWords false r s).support ∧ output=word := by
  cases ha
  cases hb
  simpa only [normalizedWordPairIso,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,Category.id_comp,plainPairIso] using
    wordIso_graph P a b false word output

theorem normalizedWordPairIso_formula_graph (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P)) (ha : Syntax.Polynomial.mapped P a=r)
    (hb : Syntax.Polynomial.mapped P b=s) (word output : ℕ) :
    output∈Total.val ((normalizedWordPairIso P a b r s ha hb).hom.2).hom word ↔
      word∈(Syntax.Raw.uniformWords true r s).support ∧ output=word := by
  cases ha
  cases hb
  simpa only [normalizedWordPairIso,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,Category.id_comp,plainPairIso] using
    wordIso_graph P a b true word output

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
