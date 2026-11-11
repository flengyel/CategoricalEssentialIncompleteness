/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstants
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawActionGraphs
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawBase

/-! # The actual constant-family polynomial comparison square

Every chart is constructed. Parameter insertion at recursive leaves,
ordered product projections, sum injections and the canonical
parameterComparison are compared as morphisms, not as bare carriers.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family}

def explicitFamilyIso (R A : Total.TotalCategory P) : constantObject R A ≅ constantFamily R A :=
  Over.isoMk (explicitProductIso R A) (explicitProductIso_fst R A)

def explicitFamilyMap (R : Total.TotalCategory P) {A B : Total.TotalCategory P} (f : A ⟶ B) :
    constantObject R A ⟶ constantObject R B :=
  Over.homMk (Total.totalPair (Total.totalFst R A) (Total.totalSnd R A ≫ f))
    (Total.totalPair_fst _ _)

theorem explicitFamilyMap_natural (R : Total.TotalCategory P) {A B : Total.TotalCategory P} (f : A ⟶ B) :
    explicitFamilyMap R f ≫ (explicitFamilyIso R B).hom=
      (explicitFamilyIso R A).hom ≫ (constantFamilyFunctor R).map f := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp [explicitFamilyMap,explicitFamilyIso,constantFamilyFunctor,Category.assoc,explicitProductIso_fst]
  · have hr : (explicitProductIso R B).hom ≫ prod.snd=Total.totalSnd R B :=
      (Total.productIsLimit R B).conePointUniqueUpToIso_hom_comp
        (limit.isLimit (Limits.pair R B)) ⟨WalkingPair.right⟩
    have hl : (explicitProductIso R A).hom ≫ prod.snd=Total.totalSnd R A :=
      (Total.productIsLimit R A).conePointUniqueUpToIso_hom_comp
        (limit.isLimit (Limits.pair R A)) ⟨WalkingPair.right⟩
    change (Total.totalPair (Total.totalFst R A) (Total.totalSnd R A ≫ f) ≫
      (explicitProductIso R B).hom) ≫ prod.snd =
      ((explicitProductIso R A).hom ≫ prod.map (𝟙 R) f) ≫ prod.snd
    rw [Category.assoc,hr,Total.totalPair_snd,
      Category.assoc,prod.map_snd,← Category.assoc,hl]

theorem explicitFamilyMap_graph (R : Total.TotalCategory P) {A B : Total.TotalCategory P} (f : A ⟶ B) (r u m : ℕ) :
    m ∈ Total.val (explicitFamilyMap R f).left.hom (Nat.pair r u) ↔
      r ∈ R.obj.support ∧ ∃ v,v ∈ Total.val f.hom u ∧ m=Nat.pair r v := by
  change m∈Total.val (Total.partialPair (Total.partialFst R.obj A.obj)
    (Total.partialSnd R.obj A.obj ≫ f.hom)) (Nat.pair r u) ↔ _
  simp only [Total.mem_partialPair,Total.mem_val_comp,Total.mem_partialFst,
    Total.mem_partialSnd,Total.product,Set.mem_ofPred_eq,Nat.unpair_pair]
  constructor
  · rintro ⟨r',⟨⟨hr,_⟩,rfl⟩,v,⟨u',⟨_,rfl⟩,hv⟩,he⟩
    exact ⟨hr,v,hv,he.symm⟩
  · rintro ⟨hr,v,hv,rfl⟩
    have hu := Total.val_source f.hom u v hv
    exact ⟨r,⟨⟨hr,hu⟩,rfl⟩,v,⟨u,⟨⟨hr,hu⟩,rfl⟩,hv⟩,rfl⟩

def liftIso (R A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantObject R (baseObject A B p) ≅ object R (constantObject R A) (constantObject R B) p :=
  (coefficientExplicitIso R (constantObject R A) (constantObject R B) (baseObject A B p)).symm ≪≫
    constantRawIso R A B (constantObject R A) (constantObject R B) p

theorem liftIso_value (R A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) (n : ℕ)
    (hn : n ∈ (constantObject R (baseObject A B p)).left.obj.support) :
    Total.val (liftIso R A B p).hom.left.hom n=Part.some (constantLiftCode p n) := by
  change Total.val ((coefficientExplicitIso R (constantObject R A) (constantObject R B) (baseObject A B p)).inv.left.hom ≫
    (constantForward R A B (constantObject R A) (constantObject R B) p).left.hom) n=_
  have he : Total.val (coefficientExplicitIso R (constantObject R A) (constantObject R B) (baseObject A B p)).inv.left.hom n=
      Part.some n := Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)
  rw [Total.val_comp,he,Part.bind_some]
  exact constantForward_value R A B (constantObject R A) (constantObject R B) p n hn

private theorem mapFst_value (R C D : Total.TotalCategory P) (n : ℕ)
    (hn : n ∈ (constantObject R (Total.totalProduct C D)).left.obj.support) :
    Total.val (explicitFamilyMap R (Total.totalFst C D)).left.hom n=
      Part.some (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1) := by
  apply Part.eq_some_iff.mpr
  simpa only [Nat.pair_unpair] using
    (explicitFamilyMap_graph R (Total.totalFst C D) (Nat.unpair n).1 (Nat.unpair n).2 _).mpr
      ⟨hn.1,_,(Total.mem_partialFst _ _ _ _).mpr ⟨hn.2,rfl⟩,rfl⟩

private theorem mapSnd_value (R C D : Total.TotalCategory P) (n : ℕ)
    (hn : n ∈ (constantObject R (Total.totalProduct C D)).left.obj.support) :
    Total.val (explicitFamilyMap R (Total.totalSnd C D)).left.hom n=
      Part.some (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2) := by
  apply Part.eq_some_iff.mpr
  simpa only [Nat.pair_unpair] using
    (explicitFamilyMap_graph R (Total.totalSnd C D) (Nat.unpair n).1 (Nat.unpair n).2 _).mpr
      ⟨hn.1,_,(Total.mem_partialSnd _ _ _ _).mpr ⟨hn.2,rfl⟩,rfl⟩

theorem liftIso_product_fst (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (liftIso R A B (.product a b)).hom ≫ productFst R (constantObject R A) (constantObject R B) a b=
      explicitFamilyMap R (Total.totalFst (baseObject A B a) (baseObject A B b)) ≫ (liftIso R A B a).hom := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have ha : Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1 ∈
      (constantObject R (baseObject A B a)).left.obj.support := by
    change (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)).1∈R.obj.support ∧
      (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)).2∈
        (carrier A.obj B.obj a).support
    simpa only [Nat.unpair_pair] using And.intro hn.1 hn.2.1
  have hla := constantLift_supported R A B a hn.1 hn.2.1
  have hlb := constantLift_supported R A B b hn.1 hn.2.2
  change Total.val ((liftIso R A B (.product a b)).hom.left.hom ≫
    (productFst R (constantObject R A) (constantObject R B) a b).left.hom) n =
    Total.val ((explicitFamilyMap R (Total.totalFst (baseObject A B a) (baseObject A B b))).left.hom ≫
      (liftIso R A B a).hom.left.hom) n
  rw [Total.val_comp,liftIso_value R A B (.product a b) n hn,Part.bind_some,
    Total.val_comp,mapFst_value R (baseObject A B a) (baseObject A B b) n hn,Part.bind_some,
    liftIso_value R A B a _ ha]
  exact (Part.eq_some_iff.mpr ((productFst_graph R (constantObject R A) (constantObject R B) a b
    (Nat.unpair n).1 (constantLift a (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)
    (constantLift b (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2) _).mpr
      ⟨hla,hlb,by simp only [constantLiftCode,Nat.unpair_pair]⟩))

theorem liftIso_product_snd (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    (liftIso R A B (.product a b)).hom ≫ productSnd R (constantObject R A) (constantObject R B) a b=
      explicitFamilyMap R (Total.totalSnd (baseObject A B a) (baseObject A B b)) ≫ (liftIso R A B b).hom := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hb : Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2 ∈
      (constantObject R (baseObject A B b)).left.obj.support := by
    change (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2)).1∈R.obj.support ∧
      (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2)).2∈
        (carrier A.obj B.obj b).support
    simpa only [Nat.unpair_pair] using And.intro hn.1 hn.2.2
  have hla := constantLift_supported R A B a hn.1 hn.2.1
  have hlb := constantLift_supported R A B b hn.1 hn.2.2
  change Total.val ((liftIso R A B (.product a b)).hom.left.hom ≫
    (productSnd R (constantObject R A) (constantObject R B) a b).left.hom) n =
    Total.val ((explicitFamilyMap R (Total.totalSnd (baseObject A B a) (baseObject A B b))).left.hom ≫
      (liftIso R A B b).hom.left.hom) n
  rw [Total.val_comp,liftIso_value R A B (.product a b) n hn,Part.bind_some,
    Total.val_comp,mapSnd_value R (baseObject A B a) (baseObject A B b) n hn,Part.bind_some,
    liftIso_value R A B b _ hb]
  exact (Part.eq_some_iff.mpr ((productSnd_graph R (constantObject R A) (constantObject R B) a b
    (Nat.unpair n).1 (constantLift a (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)
    (constantLift b (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).2) _).mpr
      ⟨hla,hlb,by simp only [constantLiftCode,Nat.unpair_pair]⟩))

theorem liftIso_sum_inl (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b)) ≫ (liftIso R A B (.sum a b)).hom=
      (liftIso R A B a).hom ≫ sumInl R (constantObject R A) (constantObject R B) a b := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hm : Total.val (explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b))).left.hom n=
      Part.some (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 0)) := by
    apply Part.eq_some_iff.mpr
    simpa only [Nat.pair_unpair] using
      (explicitFamilyMap_graph R _ (Nat.unpair n).1 (Nat.unpair n).2 _).mpr
        ⟨hn.1,_,(Total.mem_totalFromFunction (fun n => Nat.pair n 0)
          (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
          (taggedInl_supported (baseObject A B a) (baseObject A B b)) _ _).mpr ⟨hn.2,rfl⟩,rfl⟩
  have hs : Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 0) ∈
      (constantObject R (baseObject A B (.sum a b))).left.obj.support := by
    change (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 0))).1∈R.obj.support ∧
      (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 0))).2∈
        (taggedSum (baseObject A B a).obj (baseObject A B b).obj).support
    rw [Nat.unpair_pair]
    exact ⟨hn.1,taggedInl_supported (baseObject A B a) (baseObject A B b) _ hn.2⟩
  change Total.val ((explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b))).left.hom ≫
    (liftIso R A B (.sum a b)).hom.left.hom) n =
    Total.val ((liftIso R A B a).hom.left.hom ≫
      (sumInl R (constantObject R A) (constantObject R B) a b).left.hom) n
  rw [Total.val_comp,hm,Part.bind_some,liftIso_value R A B (.sum a b) _ hs,
    Total.val_comp,liftIso_value R A B a n hn,Part.bind_some]
  symm
  apply Part.eq_some_iff.mpr
  apply (sumInl_graph R (constantObject R A) (constantObject R B) a b (Nat.unpair n).1
    (constantLift a (Nat.unpair n).1 (Nat.unpair n).2) _).mpr
  exact ⟨constantLift_supported R A B a hn.1 hn.2,by simp only [constantLiftCode,constantLift_inl,Nat.unpair_pair]⟩

theorem liftIso_sum_inr (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b)) ≫ (liftIso R A B (.sum a b)).hom=
      (liftIso R A B b).hom ≫ sumInr R (constantObject R A) (constantObject R B) a b := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hm : Total.val (explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b))).left.hom n=
      Part.some (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 1)) := by
    apply Part.eq_some_iff.mpr
    simpa only [Nat.pair_unpair] using
      (explicitFamilyMap_graph R _ (Nat.unpair n).1 (Nat.unpair n).2 _).mpr
        ⟨hn.1,_,(Total.mem_totalFromFunction (fun n => Nat.pair n 1)
          (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
          (taggedInr_supported (baseObject A B a) (baseObject A B b)) _ _).mpr ⟨hn.2,rfl⟩,rfl⟩
  have hs : Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 1) ∈
      (constantObject R (baseObject A B (.sum a b))).left.obj.support := by
    change (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 1))).1∈R.obj.support ∧
      (Nat.unpair (Nat.pair (Nat.unpair n).1 (Nat.pair (Nat.unpair n).2 1))).2∈
        (taggedSum (baseObject A B a).obj (baseObject A B b).obj).support
    rw [Nat.unpair_pair]
    exact ⟨hn.1,taggedInr_supported (baseObject A B a) (baseObject A B b) _ hn.2⟩
  change Total.val ((explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b))).left.hom ≫
    (liftIso R A B (.sum a b)).hom.left.hom) n =
    Total.val ((liftIso R A B b).hom.left.hom ≫
      (sumInr R (constantObject R A) (constantObject R B) a b).left.hom) n
  rw [Total.val_comp,hm,Part.bind_some,liftIso_value R A B (.sum a b) _ hs,
    Total.val_comp,liftIso_value R A B b n hn,Part.bind_some]
  symm
  apply Part.eq_some_iff.mpr
  apply (sumInr_graph R (constantObject R A) (constantObject R B) a b (Nat.unpair n).1
    (constantLift b (Nat.unpair n).1 (Nat.unpair n).2) _).mpr
  exact ⟨constantLift_supported R A B b hn.1 hn.2,by simp only [constantLiftCode,constantLift_inr,Nat.unpair_pair]⟩

def constantPolynomialLeft (R A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantObject R (baseObject A B p) ⟶ constantFamily R (p.eval.obj (A,B)) :=
  (liftIso R A B p).hom ≫
    rawAction R (constantObject R A) (constantObject R B) (constantFamily R A) (constantFamily R B)
      (explicitFamilyIso R A).hom (explicitFamilyIso R B).hom p ≫
    (comparison R (constantFamily R A) (constantFamily R B) p).hom ≫
    SyntaxPolynomial.parameterComparison R (A,B) p

def constantPolynomialRight (R A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantObject R (baseObject A B p) ⟶ constantFamily R (p.eval.obj (A,B)) :=
  (explicitFamilyIso R (baseObject A B p)).hom ≫
    (constantFamilyFunctor R).map (baseComparison A B p).hom

theorem constantPolynomialLeft_direct (R A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantPolynomialLeft R A B p=(liftIso R A B p).hom ≫
      (comparison R (constantObject R A) (constantObject R B) p).hom ≫
      (p.withParameters R).eval.map ((explicitFamilyIso R A).hom,(explicitFamilyIso R B).hom) ≫
      SyntaxPolynomial.parameterComparison R (A,B) p := by
  have h := rawAction_comparison R (constantObject R A) (constantObject R B)
    (constantFamily R A) (constantFamily R B) (explicitFamilyIso R A).hom (explicitFamilyIso R B).hom p
  simpa only [constantPolynomialLeft,Category.assoc] using
    congrArg (fun k => (liftIso R A B p).hom ≫ k ≫ SyntaxPolynomial.parameterComparison R (A,B) p) h

private theorem constant_product_ext {R A B : Total.TotalCategory P} {Z : Over R}
    {f g : Z ⟶ constantFamily R (A ⨯ B)}
    (hf : f ≫ (constantFamilyFunctor R).map prod.fst=g ≫ (constantFamilyFunctor R).map prod.fst)
    (hg : f ≫ (constantFamilyFunctor R).map prod.snd=g ≫ (constantFamilyFunctor R).map prod.snd) : f=g := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact f.w.trans g.w.symm
  · apply prod.hom_ext
    · simpa [constantFamilyFunctor,Category.assoc] using congrArg (fun k => k.left ≫ prod.snd) hf
    · simpa [constantFamilyFunctor,Category.assoc] using congrArg (fun k => k.left ≫ prod.snd) hg

private theorem constant_terminal_ext {R : Total.TotalCategory P} {Z : Over R}
    (f g : Z ⟶ constantFamily R (⊤_ (Total.TotalCategory P))) : f=g := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact f.w.trans g.w.symm
  · exact terminal.hom_ext _ _

private theorem constantProductComparison_fst (R A B : Total.TotalCategory P) :
    constantProductComparison R A B ≫ (constantFamilyFunctor R).map prod.fst=prod.fst := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp [constantProductComparison,constantFamilyFunctor,constantFamily]
    exact (prod.fst : constantFamily R A ⨯ constantFamily R B ⟶ constantFamily R A).w.symm
  · simp [constantProductComparison,constantFamilyFunctor,constantFamily]

private theorem constantProductComparison_snd (R A B : Total.TotalCategory P) :
    constantProductComparison R A B ≫ (constantFamilyFunctor R).map prod.snd=prod.snd := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp [constantProductComparison,constantFamilyFunctor,constantFamily]
    exact (prod.snd : constantFamily R A ⨯ constantFamily R B ⟶ constantFamily R B).w.symm
  · simp [constantProductComparison,constantFamilyFunctor,constantFamily]

private theorem productChart_fst_post {R:Total.TotalCategory P} {X Y:Over R}
    {a b:SyntaxPolynomial (Total.TotalCategory P)} {Z:Over R} (h:object R X Y a ⟶ Z) :
    (productIso R X Y a b).hom ≫ prod.fst ≫ h = productFst R X Y a b ≫ h := by
  rw [← Category.assoc,productIso_fst]

private theorem productChart_snd_post {R:Total.TotalCategory P} {X Y:Over R}
    {a b:SyntaxPolynomial (Total.TotalCategory P)} {Z:Over R} (h:object R X Y b ⟶ Z) :
    (productIso R X Y a b).hom ≫ prod.snd ≫ h = productSnd R X Y a b ≫ h := by
  rw [← Category.assoc,productIso_snd]

private theorem sumChart_inl_post {R:Total.TotalCategory P} {X Y:Over R}
    {a b:SyntaxPolynomial (Total.TotalCategory P)} {Z:Over R}
    (h:(object R X Y a ⨿ object R X Y b) ⟶ Z) :
    sumInl R X Y a b ≫ (sumIso R X Y a b).hom ≫ h = coprod.inl ≫ h := by
  rw [← Category.assoc,sumIso_inl]

private theorem sumChart_inr_post {R:Total.TotalCategory P} {X Y:Over R}
    {a b:SyntaxPolynomial (Total.TotalCategory P)} {Z:Over R}
    (h:(object R X Y a ⨿ object R X Y b) ⟶ Z) :
    sumInr R X Y a b ≫ (sumIso R X Y a b).hom ≫ h = coprod.inr ≫ h := by
  rw [← Category.assoc,sumIso_inr]

private theorem tripleProduct_fst {R:Total.TotalCategory P}
    {A₀ B₀ A₁ B₁ A₂ B₂ A₃ B₃:Over R}
    (f₁:A₀⟶A₁) (g₁:B₀⟶B₁) (f₂:A₁⟶A₂) (g₂:B₁⟶B₂) (f₃:A₂⟶A₃) (g₃:B₂⟶B₃) :
    prod.map f₁ g₁ ≫ prod.map f₂ g₂ ≫ prod.map f₃ g₃ ≫ prod.fst = prod.fst ≫ f₁ ≫ f₂ ≫ f₃ := by
  rw [prod.map_fst,prod.map_fst_assoc,prod.map_fst_assoc]

private theorem tripleProduct_snd {R:Total.TotalCategory P}
    {A₀ B₀ A₁ B₁ A₂ B₂ A₃ B₃:Over R}
    (f₁:A₀⟶A₁) (g₁:B₀⟶B₁) (f₂:A₁⟶A₂) (g₂:B₁⟶B₂) (f₃:A₂⟶A₃) (g₃:B₂⟶B₃) :
    prod.map f₁ g₁ ≫ prod.map f₂ g₂ ≫ prod.map f₃ g₃ ≫ prod.snd = prod.snd ≫ g₁ ≫ g₂ ≫ g₃ := by
  rw [prod.map_snd,prod.map_snd_assoc,prod.map_snd_assoc]

private theorem left_product_fst (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    constantPolynomialLeft R A B (.product a b) ≫ (constantFamilyFunctor R).map prod.fst=
      explicitFamilyMap R (Total.totalFst (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialLeft R A B a := by
  rw [constantPolynomialLeft_direct,constantPolynomialLeft_direct]
  simp only [SyntaxPolynomial.parameterComparison,SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,comparison,Iso.trans_hom,prod.mapIso_hom,Category.assoc,
    constantProductComparison_fst]
  let ka := (a.withParameters R).eval.map
    (show (constantObject R A,constantObject R B) ⟶ (constantFamily R A,constantFamily R B) from
      ((explicitFamilyIso R A).hom,(explicitFamilyIso R B).hom))
  let kb := (b.withParameters R).eval.map
    (show (constantObject R A,constantObject R B) ⟶ (constantFamily R A,constantFamily R B) from
      ((explicitFamilyIso R A).hom,(explicitFamilyIso R B).hom))
  have ht := tripleProduct_fst
    (comparison R (constantObject R A) (constantObject R B) a).hom
    (comparison R (constantObject R A) (constantObject R B) b).hom ka kb
    (SyntaxPolynomial.parameterComparison R (A,B) a) (SyntaxPolynomial.parameterComparison R (A,B) b)
  have hfirst := congrArg (fun k => (liftIso R A B (.product a b)).hom ≫
    (productIso R (constantObject R A) (constantObject R B) a b).hom ≫ k) ht
  have hc := productChart_fst_post (R:=R) (X:=constantObject R A) (Y:=constantObject R B)
    (a:=a) (b:=b) ((comparison R (constantObject R A) (constantObject R B) a).hom ≫
      ka ≫ SyntaxPolynomial.parameterComparison R (A,B) a)
  have hmiddle := congrArg (fun k => (liftIso R A B (.product a b)).hom ≫ k) hc
  have hlast := congrArg (fun k => k ≫
    (comparison R (constantObject R A) (constantObject R B) a).hom ≫ ka ≫
    SyntaxPolynomial.parameterComparison R (A,B) a) (liftIso_product_fst R A B a b)
  simp only [Category.assoc] at hfirst hmiddle hlast
  exact hfirst.trans (hmiddle.trans hlast)

private theorem left_product_snd (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    constantPolynomialLeft R A B (.product a b) ≫ (constantFamilyFunctor R).map prod.snd=
      explicitFamilyMap R (Total.totalSnd (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialLeft R A B b := by
  rw [constantPolynomialLeft_direct,constantPolynomialLeft_direct]
  simp only [SyntaxPolynomial.parameterComparison,SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,comparison,Iso.trans_hom,prod.mapIso_hom,Category.assoc,
    constantProductComparison_snd]
  let ka := (a.withParameters R).eval.map
    (show (constantObject R A,constantObject R B) ⟶ (constantFamily R A,constantFamily R B) from
      ((explicitFamilyIso R A).hom,(explicitFamilyIso R B).hom))
  let kb := (b.withParameters R).eval.map
    (show (constantObject R A,constantObject R B) ⟶ (constantFamily R A,constantFamily R B) from
      ((explicitFamilyIso R A).hom,(explicitFamilyIso R B).hom))
  have ht := tripleProduct_snd
    (comparison R (constantObject R A) (constantObject R B) a).hom
    (comparison R (constantObject R A) (constantObject R B) b).hom ka kb
    (SyntaxPolynomial.parameterComparison R (A,B) a) (SyntaxPolynomial.parameterComparison R (A,B) b)
  have hfirst := congrArg (fun k => (liftIso R A B (.product a b)).hom ≫
    (productIso R (constantObject R A) (constantObject R B) a b).hom ≫ k) ht
  have hc := productChart_snd_post (R:=R) (X:=constantObject R A) (Y:=constantObject R B)
    (a:=a) (b:=b) ((comparison R (constantObject R A) (constantObject R B) b).hom ≫
      kb ≫ SyntaxPolynomial.parameterComparison R (A,B) b)
  have hmiddle := congrArg (fun k => (liftIso R A B (.product a b)).hom ≫ k) hc
  have hlast := congrArg (fun k => k ≫
    (comparison R (constantObject R A) (constantObject R B) b).hom ≫ kb ≫
    SyntaxPolynomial.parameterComparison R (A,B) b) (liftIso_product_snd R A B a b)
  simp only [Category.assoc] at hfirst hmiddle hlast
  exact hfirst.trans (hmiddle.trans hlast)

private theorem right_product_fst (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    constantPolynomialRight R A B (.product a b) ≫ (constantFamilyFunctor R).map prod.fst=
      explicitFamilyMap R (Total.totalFst (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialRight R A B a := by
  simp only [constantPolynomialRight,Category.assoc,← CategoryTheory.Functor.map_comp,baseComparison_product_fst]
  rw [CategoryTheory.Functor.map_comp,← Category.assoc,← explicitFamilyMap_natural]
  simp only [Category.assoc]

private theorem right_product_snd (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    constantPolynomialRight R A B (.product a b) ≫ (constantFamilyFunctor R).map prod.snd=
      explicitFamilyMap R (Total.totalSnd (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialRight R A B b := by
  simp only [constantPolynomialRight,Category.assoc,← CategoryTheory.Functor.map_comp,baseComparison_product_snd]
  rw [CategoryTheory.Functor.map_comp,← Category.assoc,← explicitFamilyMap_natural]
  simp only [Category.assoc]

private theorem left_sum_inl (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialLeft R A B (.sum a b)=
      constantPolynomialLeft R A B a ≫ (constantFamilyFunctor R).map coprod.inl := by
  rw [constantPolynomialLeft_direct,constantPolynomialLeft_direct]
  rw [← Category.assoc,liftIso_sum_inl]
  simp only [Category.assoc,comparison,Iso.trans_hom,coprod.mapIso_hom,sumChart_inl_post,
    SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.parameterComparison,coprod.inl_map_assoc,
    constantCoproductComparison,coprod.inl_desc]

private theorem left_sum_inr (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialLeft R A B (.sum a b)=
      constantPolynomialLeft R A B b ≫ (constantFamilyFunctor R).map coprod.inr := by
  rw [constantPolynomialLeft_direct,constantPolynomialLeft_direct]
  rw [← Category.assoc,liftIso_sum_inr]
  simp only [Category.assoc,comparison,Iso.trans_hom,coprod.mapIso_hom,sumChart_inr_post,
    SyntaxPolynomial.withParameters,SyntaxPolynomial.eval,SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.parameterComparison,coprod.inr_map_assoc,
    constantCoproductComparison,coprod.inr_desc]

private theorem right_sum_inl (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialRight R A B (.sum a b)=
      constantPolynomialRight R A B a ≫ (constantFamilyFunctor R).map coprod.inl := by
  have h := explicitFamilyMap_natural R (taggedInl (baseObject A B a) (baseObject A B b))
  calc
    _ = (explicitFamilyIso R (baseObject A B a)).hom ≫
        (constantFamilyFunctor R).map (taggedInl (baseObject A B a) (baseObject A B b)) ≫
        (constantFamilyFunctor R).map (baseComparison A B (.sum a b)).hom := by
      simpa only [constantPolynomialRight,taggedSumObject,baseObject,carrier,Category.assoc] using
        congrArg (fun k => k ≫ (constantFamilyFunctor R).map (baseComparison A B (.sum a b)).hom) h
    _ = _ := by
      have he := congrArg (constantFamilyFunctor R).map (baseComparison_sum_inl A B a b)
      simpa only [constantPolynomialRight,Category.assoc,CategoryTheory.Functor.map_comp] using
        congrArg (fun k => (explicitFamilyIso R (baseObject A B a)).hom ≫ k) he

private theorem right_sum_inr (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P)) :
    explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b)) ≫ constantPolynomialRight R A B (.sum a b)=
      constantPolynomialRight R A B b ≫ (constantFamilyFunctor R).map coprod.inr := by
  have h := explicitFamilyMap_natural R (taggedInr (baseObject A B a) (baseObject A B b))
  calc
    _ = (explicitFamilyIso R (baseObject A B b)).hom ≫
        (constantFamilyFunctor R).map (taggedInr (baseObject A B a) (baseObject A B b)) ≫
        (constantFamilyFunctor R).map (baseComparison A B (.sum a b)).hom := by
      simpa only [constantPolynomialRight,taggedSumObject,baseObject,carrier,Category.assoc] using
        congrArg (fun k => k ≫ (constantFamilyFunctor R).map (baseComparison A B (.sum a b)).hom) h
    _ = _ := by
      have he := congrArg (constantFamilyFunctor R).map (baseComparison_sum_inr A B a b)
      simpa only [constantPolynomialRight,Category.assoc,CategoryTheory.Functor.map_comp] using
        congrArg (fun k => (explicitFamilyIso R (baseObject A B b)).hom ≫ k) he

private theorem constant_sum_ext (R A B : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    {Z : Over R} (f g : constantObject R (baseObject A B (.sum a b)) ⟶ Z)
    (hl : explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b)) ≫ f=
      explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b)) ≫ g)
    (hr : explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b)) ≫ f=
      explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b)) ≫ g) : f=g := by
  apply (cancel_epi (liftIso R A B (.sum a b)).inv).mp
  apply sum_hom_ext R (constantObject R A) (constantObject R B) a b
  · apply (cancel_epi (liftIso R A B a).hom).mp
    have he := congrArg (fun k => k ≫ (liftIso R A B (.sum a b)).inv) (liftIso_sum_inl R A B a b)
    have hi : (liftIso R A B a).hom ≫ sumInl R (constantObject R A) (constantObject R B) a b ≫
        (liftIso R A B (.sum a b)).inv = explicitFamilyMap R (taggedInl (baseObject A B a) (baseObject A B b)) := by
      simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using he.symm
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ f) hi).trans (hl.trans (congrArg (fun k => k ≫ g) hi).symm)
  · apply (cancel_epi (liftIso R A B b).hom).mp
    have he := congrArg (fun k => k ≫ (liftIso R A B (.sum a b)).inv) (liftIso_sum_inr R A B a b)
    have hi : (liftIso R A B b).hom ≫ sumInr R (constantObject R A) (constantObject R B) a b ≫
        (liftIso R A B (.sum a b)).inv = explicitFamilyMap R (taggedInr (baseObject A B a) (baseObject A B b)) := by
      simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using he.symm
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ f) hi).trans (hr.trans (congrArg (fun k => k ≫ g) hi).symm)

private theorem liftIso_term_strip (R A B : Total.TotalCategory P) :
    (liftIso R A B .term).hom ≫ (termIso R (constantObject R A) (constantObject R B)).hom=𝟙 (constantObject R A) := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  change Total.val ((liftIso R A B .term).hom.left.hom ≫
    (termIso R (constantObject R A) (constantObject R B)).hom.left.hom) n =
      Total.supportIdentity (constantObject R A).left.obj.support n
  rw [Total.val_comp,liftIso_value R A B .term n hn,Part.bind_some]
  apply (Part.eq_some_iff.mpr ?_).trans
    (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ n n).mpr ⟨hn,rfl⟩)).symm
  apply (termIso_hom_graph R (constantObject R A) (constantObject R B) _ n).mpr
  simp only [constantLiftCode,constantLift,Nat.unpair_pair,Nat.pair_unpair]
  exact ⟨(Total.mem_partialFst _ _ n _).mpr ⟨hn,rfl⟩,by trivial⟩

private theorem liftIso_coefficient_strip (R A B C : Total.TotalCategory P) :
    (liftIso R A B (.coefficient C)).hom ≫
      (coefficientExplicitIso R (constantObject R A) (constantObject R B) C).hom=𝟙 (constantObject R C) := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  change Total.val ((liftIso R A B (.coefficient C)).hom.left.hom ≫
    (coefficientExplicitIso R (constantObject R A) (constantObject R B) C).hom.left.hom) n =
      Total.supportIdentity (constantObject R C).left.obj.support n
  rw [Total.val_comp,liftIso_value R A B (.coefficient C) n hn,Part.bind_some]
  simp only [constantLiftCode,constantLift,Nat.pair_unpair]
  rfl

/-- The full diagram with the printed parameterComparison is proved for
every finite polynomial and arbitrary coefficient and parameter carriers. -/
theorem constantPolynomialSquare (R A B : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) :
    constantPolynomialLeft R A B p=constantPolynomialRight R A B p := by
  induction p with
  | term =>
      rw [constantPolynomialLeft_direct]
      change (liftIso R A B .term).hom ≫ (termIso R (constantObject R A) (constantObject R B)).hom ≫
        (explicitFamilyIso R A).hom ≫ 𝟙 (constantFamily R A) =
          (explicitFamilyIso R A).hom ≫ (constantFamilyFunctor R).map (𝟙 A)
      rw [Category.comp_id,CategoryTheory.Functor.map_id]
      change (liftIso R A B .term).hom ≫ (termIso R (constantObject R A) (constantObject R B)).hom ≫
        (explicitFamilyIso R A).hom = (explicitFamilyIso R A).hom ≫ 𝟙 (constantFamily R A)
      rw [Category.comp_id,← Category.assoc,liftIso_term_strip]
      change 𝟙 (constantObject R A) ≫ (explicitFamilyIso R A).hom = (explicitFamilyIso R A).hom
      exact Category.id_comp _
  | formula =>
      rw [constantPolynomialLeft_direct]
      have hs : (liftIso R A B .formula).hom ≫
          (formulaIso R (constantObject R A) (constantObject R B)).hom = 𝟙 (constantObject R B) := by
        change (liftIso R B A .term).hom ≫
          (termIso R (constantObject R B) (constantObject R A)).hom = 𝟙 (constantObject R B)
        exact liftIso_term_strip R B A
      change (liftIso R A B .formula).hom ≫ (formulaIso R (constantObject R A) (constantObject R B)).hom ≫
        (explicitFamilyIso R B).hom ≫ 𝟙 (constantFamily R B) =
          (explicitFamilyIso R B).hom ≫ (constantFamilyFunctor R).map (𝟙 B)
      rw [Category.comp_id,CategoryTheory.Functor.map_id]
      change (liftIso R A B .formula).hom ≫ (formulaIso R (constantObject R A) (constantObject R B)).hom ≫
        (explicitFamilyIso R B).hom = (explicitFamilyIso R B).hom ≫ 𝟙 (constantFamily R B)
      rw [Category.comp_id,← Category.assoc,hs]
      change 𝟙 (constantObject R B) ≫ (explicitFamilyIso R B).hom = (explicitFamilyIso R B).hom
      exact Category.id_comp _
  | coefficient C =>
      rw [constantPolynomialLeft_direct]
      change (liftIso R A B (.coefficient C)).hom ≫
        ((coefficientExplicitIso R (constantObject R A) (constantObject R B) C).hom ≫
          (explicitFamilyIso R C).hom) ≫ 𝟙 (constantFamily R C) ≫ 𝟙 (constantFamily R C) =
            (explicitFamilyIso R C).hom ≫ (constantFamilyFunctor R).map (𝟙 C)
      simp only [CategoryTheory.Functor.map_id,Category.comp_id]
      rw [← Category.assoc,liftIso_coefficient_strip]
      change 𝟙 (constantObject R C) ≫ (explicitFamilyIso R C).hom =
        (explicitFamilyIso R C).hom ≫ 𝟙 (constantFamily R C)
      rw [Category.id_comp,Category.comp_id]
  | unit => exact constant_terminal_ext _ _
  | product a b ia ib =>
      apply constant_product_ext
      · rw [left_product_fst,right_product_fst,ia]
      · rw [left_product_snd,right_product_snd,ib]
  | sum a b ia ib =>
      apply constant_sum_ext R A B a b
      · rw [left_sum_inl,right_sum_inl,ia]
      · rw [left_sum_inr,right_sum_inr,ib]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
