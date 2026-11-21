/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedPolynomialRepresentation
public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInitial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Constructor-preserving comparison with the original named PA syntax

The functor on predicates is only used with its proved finite-geometry comparison.
Initiality in the larger uniform category is obtained from the uniform word algebra
and its constructed constructor diagram.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family) (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)
local notation "p" => Syntax.Polynomial.mapped P a
local notation "q" => Syntax.Polynomial.mapped P b
local notation "J" => SyntaxPolynomial.jointFunctor p q
local notation "J₀" => SyntaxPolynomial.jointFunctor a b

theorem mapped_structure (A : Endofunctor.Algebra (J₀)) :
    (Syntax.Polynomial.jointIso P a b).hom.app A.a ≫ (Syntax.Polynomial.mappedAlgebra P a b A).str=
      (FP).map A.str := by
  simp only [Syntax.Polynomial.mappedAlgebra,Iso.hom_inv_id_app_assoc]

theorem mappedHom_law {C D : Type*} [Category C] [Category D]
    (H : C ⥤ C) (K : D ⥤ D) (G : C ⥤ D) (e : H ⋙ G ≅ G ⋙ K)
    {A B : Endofunctor.Algebra H} (f : A ⟶ B) :
    K.map (G.map f.f) ≫ (e.inv.app B.a ≫ G.map B.str) =
      (e.inv.app A.a ≫ G.map A.str) ≫ G.map f.f := by
  calc
    _ = (K.map (G.map f.f) ≫ e.inv.app B.a) ≫ G.map B.str := (Category.assoc _ _ _).symm
    _ = (e.inv.app A.a ≫ G.map (H.map f.f)) ≫ G.map B.str :=
      congrArg (fun k => k ≫ G.map B.str) (e.inv.naturality f.f)
    _ = e.inv.app A.a ≫ G.map (H.map f.f ≫ B.str) := by
      rw [G.map_comp,Category.assoc]
    _ = e.inv.app A.a ≫ G.map (A.str ≫ f.f) := congrArg (fun k => e.inv.app A.a ≫ G.map k) f.h
    _ = _ := by rw [G.map_comp,Category.assoc]

def mappedHom {A B : Endofunctor.Algebra (J₀)} (f : A ⟶ B) :
    Syntax.Polynomial.mappedAlgebra P a b A ⟶ Syntax.Polynomial.mappedAlgebra P a b B where
  f := (FP).map f.f
  h := mappedHom_law (J₀) (J) (FP) (Syntax.Polynomial.jointIso P a b) f

def mappedAlgebras : Endofunctor.Algebra (J₀) ⥤ Endofunctor.Algebra (J) where
  obj := Syntax.Polynomial.mappedAlgebra P a b
  map := mappedHom P a b
  map_id A := by
    apply Endofunctor.Algebra.Hom.ext
    exact (FP).map_id A.a
  map_comp f g := by
    apply Endofunctor.Algebra.Hom.ext
    exact (FP).map_comp f.f g.f

def storedPairIso : (Syntax.Raw.wordAlgebra p q).a ≅ (FP).obj (postfixAlgebra 𝗣𝗔 a b).a where
  hom := ((storedWordIso P a b false).hom,(storedWordIso P a b true).hom)
  inv := ((storedWordIso P a b false).inv,(storedWordIso P a b true).inv)
  hom_inv_id := Prod.ext (storedWordIso P a b false).hom_inv_id (storedWordIso P a b true).hom_inv_id
  inv_hom_id := Prod.ext (storedWordIso P a b false).inv_hom_id (storedWordIso P a b true).inv_hom_id

private theorem mapped_support (C : PredicateCategory 𝗣𝗔) (n : ℕ) :
    n∈((F).obj C).obj.support ↔ C.val.Evalb (M := ℕ) ![n] := by
  rw [Syntax.predicateFunctor_object]
  rfl

/-- A literal value equation for each of two operations gives their constructor square
under the constructed polynomial chart. The premises concern operation values, not a
desired comparison diagram. -/
theorem operation_square (X Y Z : PredicateCategory 𝗣𝗔) (X' Y' Z' : Total.TotalCategory P)
    (iX : X' ≅ (F).obj X) (iY : Y' ≅ (F).obj Y) (iZ : Z' ≅ (F).obj Z)
    (hX : ∀ u v,v∈Total.val iX.hom.hom u ↔ u∈X'.obj.support ∧ v=u)
    (hY : ∀ u v,v∈Total.val iY.hom.hom u ↔ u∈Y'.obj.support ∧ v=u)
    (hZ : ∀ u v,v∈Total.val iZ.hom.hom u ↔ u∈Z'.obj.support ∧ v=u)
    (r : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (source : r.eval.obj (X,Y) ⟶ Z)
    (target : Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P r) ⟶ Z')
    (code : ℕ → ℕ)
    (hsource : ∀ u (z : PredicateInterpretation.Obj ℕ (r.eval.obj (X,Y))),
      (baseRepresentation 𝗣𝗔 X Y r).val.Evalb (M := ℕ) ![u,z.val] →
        (((PredicateInterpretation.functor 𝗣𝗔 ℕ).map source) z).val=code u)
    (htarget : ∀ u v,v∈Total.val target.hom u ↔
      u∈(Syntax.Raw.baseObject X' Y' (Syntax.Polynomial.mapped P r)).obj.support ∧ v=code u) :
    (inputIso P X Y X' Y' iX iY r).hom ≫ (F).map source=target ≫ iZ.hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro u hu
  let k := inputIso P X Y X' Y' iX iY r
  obtain ⟨zval,hz⟩ := Part.dom_iff_mem.mp ((Total.total_iff k.hom.hom).mp k.hom.property u hu)
  let z : PredicateInterpretation.Obj ℕ (r.eval.obj (X,Y)) :=
    ⟨zval,(mapped_support P _ zval).mp (Total.val_target k.hom.hom u zval hz)⟩
  have hr := (inputIso_graph P X Y X' Y' iX iY hX hY r u z).mp hz
  have hv : code u∈Total.val ((F).map source).hom zval :=
    (Syntax.predicateFunctor_graph P source zval _).mpr ⟨z,rfl,hsource u z hr⟩
  have hl : code u∈Total.val (k.hom ≫ (F).map source).hom u :=
    (Total.mem_val_comp _ _ u _).mpr ⟨zval,hz,hv⟩
  have ht : code u∈Total.val target.hom u := (htarget u _).mpr ⟨hu,rfl⟩
  have hz' := (hZ _ _).mpr ⟨Total.val_target target.hom u _ ht,rfl⟩
  have hr' : code u∈Total.val (target ≫ iZ.hom).hom u :=
    (Total.mem_val_comp _ _ u _).mpr ⟨_,ht,hz'⟩
  exact (Part.eq_some_iff.mpr hl).trans (Part.eq_some_iff.mpr hr').symm

theorem stored_term_constructor :
    (inputIso P (termCarrier a b) (formulaCarrier a b)
      (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q)
      (storedWordIso P a b false) (storedWordIso P a b true) a).hom ≫
        (F).map (postfixAlgebra 𝗣𝗔 a b).str.1=
      Syntax.Raw.rawWordConstructor p q false ≫ (storedWordIso P a b false).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro u hu
  let k := inputIso P (termCarrier a b) (formulaCarrier a b)
    (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q)
    (storedWordIso P a b false) (storedWordIso P a b true) a
  obtain ⟨zval,hz⟩ := Part.dom_iff_mem.mp ((Total.total_iff k.hom.hom).mp k.hom.property u hu)
  let z : PredicateInterpretation.Obj ℕ (a.eval.obj (termCarrier a b,formulaCarrier a b)) :=
    ⟨zval,(mapped_support P _ zval).mp (Total.val_target k.hom.hom u zval hz)⟩
  have hr := (inputIso_graph P (termCarrier a b) (formulaCarrier a b)
    (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q)
    (storedWordIso P a b false) (storedWordIso P a b true)
    (storedWordIso_graph P a b false) (storedWordIso_graph P a b true) a u z).mp hz
  have hv : Coding.constructor false a u∈Total.val ((F).map (postfixAlgebra 𝗣𝗔 a b).str.1).hom zval :=
    (Syntax.predicateFunctor_graph P (postfixAlgebra 𝗣𝗔 a b).str.1 zval _).mpr
      ⟨z,rfl,postfixTerm_value 𝗣𝗔 ℕ a b u z hr⟩
  have hleft : Coding.constructor false a u∈Total.val
      (k.hom ≫ (F).map (postfixAlgebra 𝗣𝗔 a b).str.1).hom u :=
    (Total.mem_val_comp _ _ u _).mpr ⟨zval,hz,hv⟩
  have hc : Coding.constructor false a u∈Total.val (Syntax.Raw.rawWordConstructor p q false).hom u :=
    (Syntax.Raw.rawWordConstructor_graph p q false u _).mpr
      ⟨hu,(Syntax.Raw.wordAlgebra_mapped_constructor a false u).symm⟩
  have hout := Total.val_target (Syntax.Raw.rawWordConstructor p q false).hom u _ hc
  have hright : Coding.constructor false a u∈Total.val
      (Syntax.Raw.rawWordConstructor p q false ≫ (storedWordIso P a b false).hom).hom u :=
    (Total.mem_val_comp _ _ u _).mpr ⟨_,hc,(storedWordIso_graph P a b false _ _).mpr ⟨hout,rfl⟩⟩
  exact (Part.eq_some_iff.mpr hleft).trans (Part.eq_some_iff.mpr hright).symm

theorem stored_formula_constructor :
    (inputIso P (termCarrier a b) (formulaCarrier a b)
      (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q)
      (storedWordIso P a b false) (storedWordIso P a b true) b).hom ≫
        (F).map (postfixAlgebra 𝗣𝗔 a b).str.2=
      Syntax.Raw.rawWordConstructor p q true ≫ (storedWordIso P a b true).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro u hu
  let k := inputIso P (termCarrier a b) (formulaCarrier a b)
    (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q)
    (storedWordIso P a b false) (storedWordIso P a b true) b
  obtain ⟨zval,hz⟩ := Part.dom_iff_mem.mp ((Total.total_iff k.hom.hom).mp k.hom.property u hu)
  let z : PredicateInterpretation.Obj ℕ (b.eval.obj (termCarrier a b,formulaCarrier a b)) :=
    ⟨zval,(mapped_support P _ zval).mp (Total.val_target k.hom.hom u zval hz)⟩
  have hr := (inputIso_graph P (termCarrier a b) (formulaCarrier a b)
    (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q)
    (storedWordIso P a b false) (storedWordIso P a b true)
    (storedWordIso_graph P a b false) (storedWordIso_graph P a b true) b u z).mp hz
  have hv : Coding.constructor true b u∈Total.val ((F).map (postfixAlgebra 𝗣𝗔 a b).str.2).hom zval :=
    (Syntax.predicateFunctor_graph P (postfixAlgebra 𝗣𝗔 a b).str.2 zval _).mpr
      ⟨z,rfl,postfixFormula_value 𝗣𝗔 ℕ a b u z hr⟩
  have hleft : Coding.constructor true b u∈Total.val
      (k.hom ≫ (F).map (postfixAlgebra 𝗣𝗔 a b).str.2).hom u :=
    (Total.mem_val_comp _ _ u _).mpr ⟨zval,hz,hv⟩
  have hc : Coding.constructor true b u∈Total.val (Syntax.Raw.rawWordConstructor p q true).hom u :=
    (Syntax.Raw.rawWordConstructor_graph p q true u _).mpr
      ⟨hu,(Syntax.Raw.wordAlgebra_mapped_constructor b true u).symm⟩
  have hout := Total.val_target (Syntax.Raw.rawWordConstructor p q true).hom u _ hc
  have hright : Coding.constructor true b u∈Total.val
      (Syntax.Raw.rawWordConstructor p q true ≫ (storedWordIso P a b true).hom).hom u :=
    (Total.mem_val_comp _ _ u _).mpr ⟨_,hc,(storedWordIso_graph P a b true _ _).mpr ⟨hout,rfl⟩⟩
  exact (Part.eq_some_iff.mpr hleft).trans (Part.eq_some_iff.mpr hright).symm

def storedAlgebraIso : Syntax.Raw.wordAlgebra p q ≅
    Syntax.Polynomial.mappedAlgebra P a b (postfixAlgebra 𝗣𝗔 a b) := by
  refine Endofunctor.Algebra.isoMk (storedPairIso P a b) ?_
  apply Prod.ext
  · change (p).eval.map (storedPairIso P a b).hom ≫
        ((Syntax.Polynomial.component P a (termCarrier a b,formulaCarrier a b)).inv ≫
          (F).map (postfixAlgebra 𝗣𝗔 a b).str.1) =
      ((Syntax.Raw.baseComparison (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q) p).inv ≫
        Syntax.Raw.rawWordConstructor p q false) ≫ (storedWordIso P a b false).hom
    apply (cancel_epi (Syntax.Raw.baseComparison
      (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q) p).hom).mp
    simpa only [inputIso,storedPairIso,Iso.trans_hom,Iso.symm_hom,
      Functor.mapIso_hom,Category.assoc,Iso.hom_inv_id_assoc] using stored_term_constructor P a b
  · change (q).eval.map (storedPairIso P a b).hom ≫
        ((Syntax.Polynomial.component P b (termCarrier a b,formulaCarrier a b)).inv ≫
          (F).map (postfixAlgebra 𝗣𝗔 a b).str.2) =
      ((Syntax.Raw.baseComparison (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q) q).inv ≫
        Syntax.Raw.rawWordConstructor p q true) ≫ (storedWordIso P a b true).hom
    apply (cancel_epi (Syntax.Raw.baseComparison
      (Syntax.Raw.wordObject false p q) (Syntax.Raw.wordObject true p q) q).hom).mp
    simpa only [inputIso,storedPairIso,Iso.trans_hom,Iso.symm_hom,
      Functor.mapIso_hom,Category.assoc,Iso.hom_inv_id_assoc] using stored_formula_constructor P a b

/-- Conjugation uses the proved stored/plain algebra isomorphism. -/
def wordAlgebraIso : Syntax.Raw.wordAlgebra p q ≅
    Syntax.Polynomial.mappedAlgebra P a b (plainPostfixAlgebra 𝗣𝗔 a b) :=
  storedAlgebraIso P a b ≪≫ (mappedAlgebras P a b).mapIso (plainAlgebraIso 𝗣𝗔 a b)

private theorem toPlain_graph (formula : Bool) (word output : ℕ) :
    output∈Total.val ((F).map (Postfix.plainCarrierIso 𝗣𝗔 formula a b).hom).hom word ↔
      (Postfix.carrier formula a b).val.Evalb (M := ℕ) ![word] ∧ output=word := by
  rw [Syntax.predicateFunctor_graph]
  have hfix (x : PredicateInterpretation.Obj ℕ (Postfix.carrier formula a b)) :
      (((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (Postfix.plainCarrierIso 𝗣𝗔 formula a b).hom) x).val=x.val := by
    have h := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ
      (Postfix.toPlainMorphism 𝗣𝗔 formula a b) x
      ((PredicateInterpretation.functor 𝗣𝗔 ℕ).map (Postfix.plainCarrierIso 𝗣𝗔 formula a b).hom x)).mp rfl
    exact ((GraphMorphism.identityGraph_eval _ _ _).mp h).2
  constructor
  · rintro ⟨x,rfl,hm⟩
    exact ⟨x.property,hm.symm.trans (hfix x)⟩
  · rintro ⟨hw,he⟩
    subst output
    exact ⟨⟨word,hw⟩,rfl,hfix _⟩

def plainPairIso : (Syntax.Raw.wordAlgebra p q).a ≅ (FP).obj (plainPostfixAlgebra 𝗣𝗔 a b).a where
  hom := ((wordIso P a b false).hom,(wordIso P a b true).hom)
  inv := ((wordIso P a b false).inv,(wordIso P a b true).inv)
  hom_inv_id := Prod.ext (wordIso P a b false).hom_inv_id (wordIso P a b true).hom_inv_id
  inv_hom_id := Prod.ext (wordIso P a b false).inv_hom_id (wordIso P a b true).inv_hom_id

private theorem stored_then_plain (formula : Bool) :
    (storedWordIso P a b formula).hom ≫ (F).map (Postfix.plainCarrierIso 𝗣𝗔 formula a b).hom=
      (wordIso P a b formula).hom := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro word hw
  change Total.val ((storedWordIso P a b formula).hom.hom ≫
    ((F).map (Postfix.plainCarrierIso 𝗣𝗔 formula a b).hom).hom) word =
      Total.val (wordIso P a b formula).hom.hom word
  have hs : (Postfix.carrier formula a b).val.Evalb (M := ℕ) ![word] :=
    (mapped_support P _ word).mp
      (Total.val_target (storedWordIso P a b formula).hom.hom word word
        ((storedWordIso_graph P a b formula word word).mpr ⟨hw,rfl⟩))
  apply Part.ext
  intro output
  rw [Total.val_comp]
  simp only [Part.mem_bind_iff,storedWordIso_graph,toPlain_graph,wordIso_graph]
  change word∈(Syntax.Raw.uniformWords formula p q).support at hw
  constructor
  · rintro ⟨v,⟨_,hv⟩,_,ho⟩
    subst v
    exact ⟨hw,ho⟩
  · rintro ⟨_,ho⟩
    exact ⟨word,⟨hw,rfl⟩,hs,ho⟩

/-- The already constructed algebra isomorphism has the literal
numeric-identity word charts as its two carrier components. -/
theorem wordAlgebraIso_f : (wordAlgebraIso P a b).hom.f=(plainPairIso P a b).hom := by
  apply Prod.ext
  · change (storedWordIso P a b false).hom ≫ (F).map (Postfix.plainCarrierIso 𝗣𝗔 false a b).hom=_
    exact stored_then_plain P a b false
  · change (storedWordIso P a b true).hom ≫ (F).map (Postfix.plainCarrierIso 𝗣𝗔 true a b).hom=_
    exact stored_then_plain P a b true

theorem wordAlgebraIso_inverse_f : (wordAlgebraIso P a b).inv.f=(plainPairIso P a b).inv := by
  have hi : (wordAlgebraIso P a b).inv.f ≫ (plainPairIso P a b).hom=𝟙 _ := by
    rw [← wordAlgebraIso_f]
    exact congrArg Endofunctor.Algebra.Hom.f (wordAlgebraIso P a b).inv_hom_id
  calc
    _ = (wordAlgebraIso P a b).inv.f ≫
        ((plainPairIso P a b).hom ≫ (plainPairIso P a b).inv) := by
      rw [Iso.hom_inv_id,Category.comp_id]
    _ = _ := by rw [← Category.assoc,hi,Category.id_comp]

def mappedPlainInitial : IsInitial (Syntax.Polynomial.mappedAlgebra P a b (plainPostfixAlgebra 𝗣𝗔 a b)) :=
  (Syntax.Raw.wordInitial p q).ofIso (wordAlgebraIso P a b)

def mappedPlainWithParametersInitial (R : Total.TotalCategory P) :
    IsInitial (SyntaxPolynomial.algebraWithParameters p q
      (Syntax.Polynomial.mappedAlgebra P a b (plainPostfixAlgebra 𝗣𝗔 a b)) R) :=
  (Syntax.Raw.wordWithParametersInitial R p q).ofIso
    (parameterAlgebraIso p q R (wordAlgebraIso P a b))

/-- Equality follows from the constructed uniform universal property,
not from a purported preservation of initiality by the predicate functor. -/
theorem mapped_fold (B : Endofunctor.Algebra (J₀)) :
    (wordAlgebraIso P a b).hom ≫ mappedHom P a b ((plainPostfixInitial 𝗣𝗔 a b).to B)=
      (Syntax.Raw.wordInitial p q).to (Syntax.Polynomial.mappedAlgebra P a b B) :=
  (Syntax.Raw.wordInitial p q).hom_ext _ _

theorem mapped_fold_underlying (B : Endofunctor.Algebra (J₀)) :
    (wordAlgebraIso P a b).hom.f ≫ (FP).map ((plainPostfixInitial 𝗣𝗔 a b).to B).f=
      ((Syntax.Raw.wordInitial p q).to (Syntax.Polynomial.mappedAlgebra P a b B)).f :=
  congrArg Endofunctor.Algebra.Hom.f (mapped_fold P a b B)

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
