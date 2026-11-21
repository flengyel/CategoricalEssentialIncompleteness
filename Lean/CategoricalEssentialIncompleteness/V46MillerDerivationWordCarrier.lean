/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationInitial
public import CategoricalEssentialIncompleteness.V46MillerTotalRegular

/-! # Successful derivations carried by their original word alone

The successful pullback is compared with its monomorphic image in the ordinary-tree
carrier. Its image predicate existentially hides the pullback and conclusion
witnesses. Both algebra constructors and conclusions are transported through the
proved isomorphism.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)

instance treeInclusion_mono : Mono (treeInclusion R) := by
  change Mono (pullback.fst (validatorFold R).f (coprod.inr : F ⟶ OptionSyntax.obj F))
  infer_instance

def successfulWordObject : Total.TotalCategory P := Total.imageObject (treeInclusion R)

theorem successfulWord_mem (word : ℕ) : word∈(successfulWordObject R).obj.support ↔
    ∃ proofCode,word∈Total.val (treeInclusion R).hom proofCode := by
  change word∈Total.support (Ranges.range (treeInclusion R).hom) ↔ _
  rw [Total.support_range]
  rfl

def wordInclusion : successfulWordObject R ⟶ (ordinaryTree R).a :=
  Total.imageInclusion (treeInclusion R)

theorem wordInclusion_graph (word output : ℕ) :
    output∈Total.val (wordInclusion R).hom word ↔
      word∈(successfulWordObject R).obj.support ∧ output=word := by
  change output ∈ Total.val (Ranges.range (treeInclusion R).hom).hom word ↔
    word ∈ Total.support (Ranges.range (treeInclusion R).hom) ∧ output=word
  exact Total.mem_val_idem _ word output

instance wordQuotient_isIso : IsIso (Total.imageQuotient (treeInclusion R)) := by
  let : Mono (Total.imageQuotient (treeInclusion R)) :=
    mono_of_mono_fac (Total.image_factorization (treeInclusion R))
  exact isIso_of_mono_of_strongEpi _

/-- The inverse translates a successful original word to the selected
pullback carrier. Its membership witnesses are not syntax labels. -/
def successfulWordIso : successfulWordObject R ≅ (derivationAlgebra R).a.left :=
  (asIso (Total.imageQuotient (treeInclusion R))).symm

theorem successfulWordIso_tree : (successfulWordIso R).hom ≫ treeInclusion R=wordInclusion R := by
  rw [← Total.image_factorization (treeInclusion R)]
  change inv (Total.imageQuotient (treeInclusion R)) ≫
    (Total.imageQuotient (treeInclusion R) ≫ wordInclusion R)=wordInclusion R
  rw [IsIso.inv_hom_id_assoc]

theorem successfulWordIso_inverse_tree :
    (successfulWordIso R).inv ≫ wordInclusion R=treeInclusion R :=
  Total.image_factorization (treeInclusion R)

private theorem inverse_graph {X Y : Total.TotalCategory P} (i : X ≅ Y) (x y : ℕ) :
    x∈Total.val i.inv.hom y ↔ y∈Total.val i.hom.hom x := by
  constructor
  · intro hx
    have hy := Total.val_source i.inv.hom y x hx
    have he : y∈Total.val (i.inv ≫ i.hom).hom y := by
      rw [i.inv_hom_id]
      exact (Total.mem_supportIdentity _ y y).mpr ⟨hy,rfl⟩
    obtain ⟨x',hx',hy'⟩ := (Total.mem_val_comp _ _ y y).mp he
    exact Part.mem_unique hx' hx ▸ hy'
  · intro hy
    have hx := Total.val_source i.hom.hom x y hy
    have he : x∈Total.val (i.hom ≫ i.inv).hom x := by
      rw [i.hom_inv_id]
      exact (Total.mem_supportIdentity _ x x).mpr ⟨hx,rfl⟩
    obtain ⟨y',hy',hx'⟩ := (Total.mem_val_comp _ _ x x).mp he
    exact Part.mem_unique hy' hy ▸ hx'

theorem successfulWordIso_graph (word proofCode : ℕ) :
    proofCode∈Total.val (successfulWordIso R).hom.hom word ↔
      word∈Total.val (treeInclusion R).hom proofCode := by
  exact inverse_graph (asIso (Total.imageQuotient (treeInclusion R))) proofCode word

def wordConclusion : successfulWordObject R ⟶ F :=
  (successfulWordIso R).hom ≫ conclusion R

theorem wordConclusion_graph (word formula : ℕ) :
    formula∈Total.val (wordConclusion R).hom word ↔
      ∃ proofCode,word∈Total.val (treeInclusion R).hom proofCode ∧
        formula∈Total.val (conclusion R).hom proofCode := by
  change formula ∈ Total.val ((successfulWordIso R).hom.hom ≫ (conclusion R).hom) word ↔ _
  rw [Total.mem_val_comp]
  simp only [successfulWordIso_graph]

private theorem pullback_graph {W X Y Z : Total.TotalCategory P}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x y : ℕ) :
    (∃ w,x∈Total.val a.hom w ∧ y∈Total.val b.hom w) ↔
      ∃ output,output∈Total.val f.hom x ∧ output∈Total.val g.hom y := by
  constructor
  · rintro ⟨w,ha,hb⟩
    obtain ⟨output,hf⟩ := Part.dom_iff_mem.mp ((Total.total_iff f.hom).mp f.property x
      (Total.val_target a.hom w x ha))
    have hh : output∈Total.val (b ≫ g).hom w := by
      rw [← h.w]
      exact (Total.mem_val_comp _ _ w output).mpr ⟨x,ha,hf⟩
    obtain ⟨y',hb',hg⟩ := (Total.mem_val_comp _ _ w output).mp hh
    exact ⟨output,hf,Part.mem_unique hb' hb ▸ hg⟩
  · rintro ⟨output,hf,hg⟩
    exact Total.pullback_lifts_elements h x y output hf hg

/-- Direct validation graph on the original input word. The existential
output and conclusion witnesses remain inside this graph predicate. -/
theorem wordConclusion_validated (word formula : ℕ) :
    formula∈Total.val (wordConclusion R).hom word ↔
      ∃ output,output∈Total.val (validatorFold R).f.hom word ∧
        output∈Total.val (coprod.inr : F ⟶ OptionSyntax.obj F).hom formula := by
  exact (wordConclusion_graph R word formula).trans
    (pullback_graph (successful_pullback R) word formula)

theorem successfulWord_validated (word : ℕ) : word∈(successfulWordObject R).obj.support ↔
    ∃ formula output,output∈Total.val (validatorFold R).f.hom word ∧
      output∈Total.val (coprod.inr : F ⟶ OptionSyntax.obj F).hom formula := by
  constructor
  · intro hw
    obtain ⟨formula,hf⟩ := Part.dom_iff_mem.mp
      ((Total.total_iff (wordConclusion R).hom).mp (wordConclusion R).property word hw)
    exact ⟨formula,(wordConclusion_validated R word formula).mp hf⟩
  · rintro ⟨formula,output,hv,hi⟩
    exact Total.val_source (wordConclusion R).hom word formula
      ((wordConclusion_validated R word formula).mpr ⟨output,hv,hi⟩)

def wordOverIso : Over.mk (wordConclusion R) ≅ (derivationAlgebra R).a :=
  Over.isoMk (successfulWordIso R) rfl

def wordAlgebra : Endofunctor.Algebra R.inference where
  a := Over.mk (wordConclusion R)
  str := R.inference.map (wordOverIso R).hom ≫ (derivationAlgebra R).str ≫ (wordOverIso R).inv

def wordAlgebraIso : wordAlgebra R ≅ derivationAlgebra R :=
  Endofunctor.Algebra.isoMk (wordOverIso R) (by simp [wordAlgebra,Category.assoc])

def wordInitial : IsInitial (wordAlgebra R) :=
  (derivationInitial R).ofIso (wordAlgebraIso R).symm

theorem word_constructor_tree :
    (wordAlgebra R).str.left ≫ wordInclusion R=
      InputGeometry.forget R (wordAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map (wordInclusion R) ≫ (ordinaryTree R).str := by
  have hcancel : (wordOverIso R).inv.left ≫ wordInclusion R=treeInclusion R :=
    successfulWordIso_inverse_tree R
  change ((R.inference.map (wordOverIso R).hom).left ≫ ((derivationAlgebra R).str.left ≫
    (wordOverIso R).inv.left)) ≫ wordInclusion R=_
  rw [Category.assoc,Category.assoc,hcancel,constructor_tree]
  have he := congrArg (fun k => k ≫
      (PolynomialComparison.ordinary R).map (treeInclusion R) ≫ (ordinaryTree R).str)
    (InputGeometry.forget_natural R (wordOverIso R).hom)
  have hi : (PolynomialComparison.ordinary R).map (wordOverIso R).hom.left ≫
      (PolynomialComparison.ordinary R).map (treeInclusion R)=
        (PolynomialComparison.ordinary R).map (wordInclusion R) := by
    rw [← Functor.map_comp]
    exact congrArg (PolynomialComparison.ordinary R).map (successfulWordIso_tree R)
  simp only [Category.assoc] at he
  have hi' := congrArg (fun k => InputGeometry.forget R (wordAlgebra R).a ≫
    (k ≫ (ordinaryTree R).str)) hi
  simp only [Category.assoc] at hi'
  exact he.trans hi' 

/-- The chart retains the original rule label and the ordered children;
it only forgets their premise-matching witnesses. -/
def wordInputChart : (R.inference.obj (wordAlgebra R).a).left ⟶
    (⟨Syntax.Raw.carrier
      (Syntax.Raw.uniformWords false (treePolynomial R) .unit)
      (Syntax.Raw.uniformWords true (treePolynomial R) .unit) (treePolynomial R)⟩ : Total.TotalCategory P) :=
  InputGeometry.forget R (wordAlgebra R).a ≫
    (PolynomialComparison.ordinary R).map (wordInclusion R) ≫ (ordinaryInputIso R).inv

theorem word_constructor_code :
    (wordAlgebra R).str.left ≫ wordInclusion R=
      wordInputChart R ≫ Syntax.Raw.rawWordConstructor (treePolynomial R) .unit false := by
  rw [word_constructor_tree,← ordinaryInputIso_constructor R]
  simp only [wordInputChart,Category.assoc,Iso.inv_hom_id_assoc]

theorem word_constructor_value (input u word : ℕ)
    (hu : u∈Total.val (wordInputChart R).hom input)
    (hw : word∈Total.val (wordAlgebra R).str.left.hom input) :
    word=SyntacticSyntax.Coding.constructor false (Syntax.Raw.skeleton (treePolynomial R)) u := by
  have him : word∈Total.val ((wordAlgebra R).str.left ≫ wordInclusion R).hom input :=
    (Total.mem_val_comp _ _ input word).mpr ⟨word,hw,
      (wordInclusion_graph R word word).mpr ⟨Total.val_target _ _ _ hw,rfl⟩⟩
  rw [word_constructor_code] at him
  obtain ⟨u',hu',hc⟩ := (Total.mem_val_comp _ _ input word).mp him
  have he : u'=u := Part.mem_unique hu' hu
  exact ((Syntax.Raw.rawWordConstructor_graph (treePolynomial R) .unit false u' word).mp hc).2.trans
    (congrArg (SyntacticSyntax.Coding.constructor false (Syntax.Raw.skeleton (treePolynomial R))) he)

def wordFold (B : Endofunctor.Algebra R.inference) : wordAlgebra R ⟶ B :=
  (wordInitial R).to B

theorem wordFold_conclusion (B : Endofunctor.Algebra R.inference) :
    (wordFold R B).f.left ≫ B.a.hom=wordConclusion R := Over.w _

theorem wordFold_constructor (B : Endofunctor.Algebra R.inference) :
    (wordAlgebra R).str ≫ (wordFold R B).f=R.inference.map (wordFold R B).f ≫ B.str :=
  (wordFold R B).h.symm

theorem wordFold_unique (B : Endofunctor.Algebra R.inference) (f : wordAlgebra R ⟶ B) :
    f=wordFold R B := (wordInitial R).hom_ext _ _

theorem wordFold_underlying_unique (B : Endofunctor.Algebra R.inference)
    (f : successfulWordObject R ⟶ B.a.left)
    (hf : f ≫ B.a.hom=wordConclusion R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str=
      (wordAlgebra R).str ≫ Over.homMk f hf) : f=(wordFold R B).f.left := by
  exact congrArg (fun h : wordAlgebra R ⟶ B => h.f.left)
    ((wordInitial R).hom_ext (⟨Over.homMk f hf,hc⟩ : wordAlgebra R ⟶ B) (wordFold R B))

def wordConstructor (i : Fin (N+1)) : R.ruleObject (wordAlgebra R).a i ⟶ successfulWordObject R :=
  Sigma.ι (R.ruleObject (wordAlgebra R).a) i ≫ (wordAlgebra R).str.left

@[reassoc] theorem wordConstructor_conclusion (i : Fin (N+1)) :
    wordConstructor R i ≫ wordConclusion R=R.ruleConclusion (wordAlgebra R).a i := by
  change (Sigma.ι (R.ruleObject (wordAlgebra R).a) i ≫ (wordAlgebra R).str.left) ≫
    (wordAlgebra R).a.hom = _
  erw [Category.assoc,Over.w (wordAlgebra R).str]
  exact Sigma.ι_comp_desc _ i

def wordNullary : R.instances 0 ⟶ successfulWordObject R :=
  R.nullaryRule (wordAlgebra R).a ≫ wordConstructor R 0

@[reassoc] theorem wordNullary_conclusion : wordNullary R ≫ wordConclusion R=R.conclusion 0 := by
  rw [wordNullary,Category.assoc,wordConstructor_conclusion]
  simpa only [Category.assoc,Category.id_comp,RulePresentation.ruleConclusion] using
    congrArg (fun k => k ≫ R.conclusion 0) (R.nullaryRule_fst (wordAlgebra R).a)

end CategoricalEssentialIncompleteness.V46.Miller.Derivation
