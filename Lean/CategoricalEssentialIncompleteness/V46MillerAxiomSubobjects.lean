/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxPresentation
public import CategoricalEssentialIncompleteness.V46MillerTotalRegular
public import CategoricalEssentialIncompleteness.V46MillerFiniteAxiomProofs
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # Uniform external axiom subobjects and finite axiom supports

The axiom set is an arbitrary uniformly enumerable set of natural codes. Only the
sentence carrier is a PA predicate. Its intersection with the axiom set is formed in
the uniform total splitting; the external axiom set is never represented by an assumed
PA formula. All inclusions below are guarded identity maps on their supports.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.AxiomSubobjects
variable {P : Uniform.Family}

def identityMap (X Y : Total.TotalCategory P) (h : X.obj.support ⊆ Y.obj.support) : X ⟶ Y :=
  ⟨Total.totalFromFunction id Computable.id h,Total.totalFromFunction_total _ _ _⟩

theorem identityMap_graph (X Y : Total.TotalCategory P) (h : X.obj.support ⊆ Y.obj.support)
    (n m : ℕ) : m ∈ Total.val (identityMap X Y h).hom n ↔ n ∈ X.obj.support ∧ m=n :=
  Total.mem_totalFromFunction id Computable.id h n m

private instance identityMap_mono (X Y : Total.TotalCategory P) (h : X.obj.support ⊆ Y.obj.support) :
    Mono (identityMap X Y h) := by
  let : Mono (identityMap X Y h).hom :=
    Total.mono_of_total_injective _ (identityMap X Y h).property (by
      intro n n' m hn hn'
      exact ((identityMap_graph X Y h n m).mp hn).2.symm.trans
        ((identityMap_graph X Y h n' m).mp hn').2)
  exact ⟨fun u v huv => by
    apply WideSubcategory.hom_ext
    apply (cancel_mono (identityMap X Y h).hom).mp
    exact congrArg (fun k => k.hom) huv⟩

theorem identity_graph_ext {X Y : Total.TotalCategory P} (f g : X ⟶ Y)
    (hf : ∀ n m,m ∈ Total.val f.hom n ↔ n ∈ X.obj.support ∧ m=n)
    (hg : ∀ n m,m ∈ Total.val g.hom n ↔ n ∈ X.obj.support ∧ m=n) : f=g := by
  apply WideSubcategory.hom_ext
  apply Total.val_injective
  funext n
  apply Part.ext
  intro m
  exact (hf n m).trans (hg n m).symm

theorem identity_graph_comp {X Y Z : Total.TotalCategory P} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : ∀ n m,m ∈ Total.val f.hom n ↔ n ∈ X.obj.support ∧ m=n)
    (hg : ∀ n m,m ∈ Total.val g.hom n ↔ n ∈ Y.obj.support ∧ m=n)
    (n m : ℕ) : m ∈ Total.val (f ≫ g).hom n ↔ n ∈ X.obj.support ∧ m=n := by
  change m ∈ Total.val (f.hom ≫ g.hom) n ↔ n ∈ X.obj.support ∧ m=n
  rw [Total.mem_val_comp]
  constructor
  · rintro ⟨u,hu,hm⟩
    obtain ⟨hn,he⟩ := (hf n u).mp hu
    subst u
    exact ⟨hn,((hg n m).mp hm).2⟩
  · rintro ⟨hn,he⟩
    subst m
    have hf' := (hf n n).mpr ⟨hn,rfl⟩
    exact ⟨n,hf',(hg n n).mpr ⟨Total.val_target f.hom n n hf',rfl⟩⟩

theorem identity_graph_id (X : Total.TotalCategory P) (n m : ℕ) :
    m ∈ Total.val (𝟙 X : X ⟶ X).hom n ↔ n ∈ X.obj.support ∧ m=n :=
  Total.mem_supportIdentity X.obj.support n m

def supportIso (X Y : Total.TotalCategory P) (h : ∀ n,n ∈ X.obj.support ↔ n ∈ Y.obj.support) :
    X ≅ Y where
  hom := identityMap X Y (fun n hn => (h n).mp hn)
  inv := identityMap Y X (fun n hn => (h n).mpr hn)
  hom_inv_id := identity_graph_ext _ _
    (identity_graph_comp _ _ (identityMap_graph _ _ _) (identityMap_graph _ _ _))
    (identity_graph_id X)
  inv_hom_id := identity_graph_ext _ _
    (identity_graph_comp _ _ (identityMap_graph _ _ _) (identityMap_graph _ _ _))
    (identity_graph_id Y)

/-- Standard support of the predicate interpretation, with its original scalar code. -/
theorem mapped_support (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔) (n : ℕ) :
    n ∈ ((Syntax.predicateFunctor P).obj S).obj.support ↔ S.val.Evalb (M := ℕ) ![n] := by
  rw [Syntax.predicateFunctor_object]
  rfl

theorem mapped_finite_support (P : Uniform.Family) (L : List ℕ) (n : ℕ) :
    n ∈ ((Syntax.predicateFunctor P).obj (finiteCarrier L)).obj.support ↔ n ∈ L :=
  (mapped_support P (finiteCarrier L) n).trans (finiteCarrier_eval L n)

/-- The sentence guard is retained even when the external code set has other members. -/
def axiomSupport (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔) (A : Set ℕ) : Set ℕ :=
  A ∩ ((Syntax.predicateFunctor P).obj S).obj.support

theorem axiomSupport_enumerable (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) :
    Uniform.Enumerable P (· ∈ axiomSupport P S A) :=
  hA.and ((Syntax.predicateFunctor P).obj S).obj.enumerable

def axiomIdem (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) :
    Idem ((Syntax.predicateFunctor P).obj S).obj :=
  Total.relativeIdem (axiomSupport P S A) (axiomSupport_enumerable P S A hA)
    (fun _ hn => hn.2)

def axCarrier (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) : Total.TotalCategory P :=
  ⟨Total.subcarrier (axiomIdem P S A hA)⟩

theorem axCarrier_support (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (n : ℕ) :
    n ∈ (axCarrier P S A hA).obj.support ↔ n ∈ A ∧ S.val.Evalb (M := ℕ) ![n] := by
  change n ∈ Total.support (axiomIdem P S A hA) ↔ _
  rw [axiomIdem,Total.support_relativeIdem]
  exact and_congr_right (fun _ => mapped_support P S n)

def axiomInclusion (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) :
    axCarrier P S A hA ⟶ (Syntax.predicateFunctor P).obj S :=
  ⟨Total.into (axiomIdem P S A hA),Total.into_total _⟩

theorem axiomInclusion_graph (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (n m : ℕ) :
    m ∈ Total.val (axiomInclusion P S A hA).hom n ↔
      n ∈ A ∧ S.val.Evalb (M := ℕ) ![n] ∧ m=n := by
  change m ∈ Total.val (axiomIdem P S A hA).hom n ↔ _
  rw [Total.mem_val_idem]
  exact (and_congr_left (fun _ => axCarrier_support P S A hA n)).trans and_assoc

private theorem axiomInclusion_identity (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (n m : ℕ) :
    m ∈ Total.val (axiomInclusion P S A hA).hom n ↔
      n ∈ (axCarrier P S A hA).obj.support ∧ m=n :=
  Total.mem_val_idem (axiomIdem P S A hA) n m

instance axiomInclusion_mono (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) : Mono (axiomInclusion P S A hA) where
  right_cancellation u v he := by
    apply WideSubcategory.hom_ext
    apply (cancel_mono (Total.into (axiomIdem P S A hA))).mp
    exact congrArg (fun k => k.hom) he

def axiomSubobject (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) : Subobject ((Syntax.predicateFunctor P).obj S) :=
  Subobject.mk (axiomInclusion P S A hA)

/-- Only this finite source is represented by a PA predicate. -/
def finiteIntoAxioms (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (L : List ℕ)
    (hLA : ∀ n ∈ L,n ∈ A) (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) :
    (Syntax.predicateFunctor P).obj (finiteCarrier L) ⟶ axCarrier P S A hA :=
  identityMap _ _ (fun n hn => (axCarrier_support P S A hA n).mpr
    ⟨hLA n ((mapped_finite_support P L n).mp hn),hLS n ((mapped_finite_support P L n).mp hn)⟩)

theorem finiteIntoAxioms_graph (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (L : List ℕ)
    (hLA : ∀ n ∈ L,n ∈ A) (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) (n m : ℕ) :
    m ∈ Total.val (finiteIntoAxioms P S A hA L hLA hLS).hom n ↔ n ∈ L ∧ m=n :=
  (identityMap_graph _ _ _ n m).trans (and_congr_left (fun _ => mapped_finite_support P L n))

def finiteIntoSentence (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔) (L : List ℕ)
    (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) :
    (Syntax.predicateFunctor P).obj (finiteCarrier L) ⟶ (Syntax.predicateFunctor P).obj S :=
  identityMap _ _ (fun n hn => (mapped_support P S n).mpr
    (hLS n ((mapped_finite_support P L n).mp hn)))

theorem finiteIntoSentence_graph (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔) (L : List ℕ)
    (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) (n m : ℕ) :
    m ∈ Total.val (finiteIntoSentence P S L hLS).hom n ↔ n ∈ L ∧ m=n :=
  (identityMap_graph _ _ _ n m).trans (and_congr_left (fun _ => mapped_finite_support P L n))

instance finiteIntoSentence_mono (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔) (L : List ℕ)
    (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) : Mono (finiteIntoSentence P S L hLS) :=
  identityMap_mono _ _ _

theorem finiteIntoAxioms_fac (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (L : List ℕ)
    (hLA : ∀ n ∈ L,n ∈ A) (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) :
    finiteIntoAxioms P S A hA L hLA hLS ≫ axiomInclusion P S A hA = finiteIntoSentence P S L hLS :=
  identity_graph_ext _ _
    (identity_graph_comp _ _ (identityMap_graph _ _ _) (axiomInclusion_identity P S A hA))
    (identityMap_graph _ _ _)

theorem finiteSubobject_le (P : Uniform.Family) (S : PredicateCategory 𝗣𝗔)
    (A : Set ℕ) (hA : Uniform.Enumerable P (· ∈ A)) (L : List ℕ)
    (hLA : ∀ n ∈ L,n ∈ A) (hLS : ∀ n ∈ L,S.val.Evalb (M := ℕ) ![n]) :
    Subobject.mk (finiteIntoSentence P S L hLS) ≤ axiomSubobject P S A hA :=
  Subobject.mk_le_mk_of_comm (finiteIntoAxioms P S A hA L hLA hLS)
    (finiteIntoAxioms_fac P S A hA L hLA hLS)

/-- The range of an arbitrary axiom morphism, with no injective-program choice. -/
def imageCodes {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) : Set ℕ :=
  {n | ∃ x,n ∈ Total.val a.hom x}

theorem imageCodes_enumerable {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) : Uniform.Enumerable P (· ∈ imageCodes a) :=
  (Total.support_re (Ranges.range a.hom)).of_eq (fun n => by rw [Total.support_range]; rfl)

theorem imageCodes_sentence {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) (n : ℕ) (hn : n ∈ imageCodes a) :
    S.val.Evalb (M := ℕ) ![n] := by
  obtain ⟨x,hx⟩ := hn
  exact (mapped_support P S n).mp (Total.val_target a.hom x n hx)

/-- This is a chart of uniform objects, with identity scalar programs in both directions. -/
def imageCarrierIso {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) :
    axCarrier P S (imageCodes a) (imageCodes_enumerable a) ≅ Total.imageObject a :=
  supportIso _ _ (fun n => by
    rw [axCarrier_support]
    change (n ∈ imageCodes a ∧ S.val.Evalb (M := ℕ) ![n]) ↔ n ∈ Total.support (Ranges.range a.hom)
    rw [Total.support_range]
    exact ⟨fun hn => hn.1,fun hn => ⟨hn,imageCodes_sentence a n hn⟩⟩)

theorem imageCarrierIso_graph {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) (n m : ℕ) :
    m ∈ Total.val (imageCarrierIso a).hom.hom n ↔ n ∈ imageCodes a ∧ m=n := by
  change m ∈ Total.val (identityMap _ _ _).hom n ↔ _
  rw [identityMap_graph,axCarrier_support]
  exact ⟨fun hn => ⟨hn.1.1,hn.2⟩,fun hn => ⟨⟨hn.1,imageCodes_sentence a n hn.1⟩,hn.2⟩⟩

theorem imageCarrierIso_inverse_graph {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) (n m : ℕ) :
    m ∈ Total.val (imageCarrierIso a).inv.hom n ↔ n ∈ imageCodes a ∧ m=n := by
  change m ∈ Total.val (identityMap _ _ _).hom n ↔ _
  rw [identityMap_graph]
  change (n ∈ Total.support (Ranges.range a.hom) ∧ m=n) ↔ _
  rw [Total.support_range]
  rfl

theorem imageCarrierIso_inclusion {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) :
    (imageCarrierIso a).hom ≫ Total.imageInclusion a =
      axiomInclusion P S (imageCodes a) (imageCodes_enumerable a) :=
  identity_graph_ext _ _
    (identity_graph_comp _ _ (identityMap_graph _ _ _)
      (fun n m => Total.mem_val_idem (Ranges.range a.hom) n m))
    (axiomInclusion_identity P S (imageCodes a) (imageCodes_enumerable a))

theorem image_subobject_eq {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) :
    axiomSubobject P S (imageCodes a) (imageCodes_enumerable a) = Subobject.mk (Total.imageInclusion a) :=
  Subobject.mk_eq_mk_of_comm _ _ (imageCarrierIso a) (imageCarrierIso_inclusion a)

private theorem imageQuotient_mono {X Y : Total.TotalCategory P} (a : X ⟶ Y) [Mono a] :
    Mono (Total.imageQuotient a) where
  right_cancellation u v he := by
    apply (cancel_mono a).mp
    have hh := congrArg (fun k => k ≫ Total.imageInclusion a) he
    simpa only [Category.assoc,Total.image_factorization] using hh

theorem imageQuotient_isIso {X Y : Total.TotalCategory P} (a : X ⟶ Y) [Mono a] :
    IsIso (Total.imageQuotient a) := by
  let := imageQuotient_mono a
  exact isIso_of_regularEpi_of_mono _
    (Total.regularEpiOfSurjective _ (Total.imageQuotient_surjective a))

/-- A given axiom monomorphism is represented by its image code set. -/
def monoPresentation {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] :
    X ≅ axCarrier P S (imageCodes a) (imageCodes_enumerable a) := by
  letI := imageQuotient_isIso a
  exact asIso (Total.imageQuotient a) ≪≫ (imageCarrierIso a).symm

theorem monoPresentation_inclusion {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] :
    (monoPresentation a).hom ≫ axiomInclusion P S (imageCodes a) (imageCodes_enumerable a) = a := by
  calc
    (monoPresentation a).hom ≫ axiomInclusion P S (imageCodes a) (imageCodes_enumerable a) =
        (monoPresentation a).hom ≫ (imageCarrierIso a).hom ≫ Total.imageInclusion a := by
          rw [imageCarrierIso_inclusion]
    _ = Total.imageQuotient a ≫ Total.imageInclusion a := by
          simp only [monoPresentation,Iso.trans_hom,Iso.symm_hom,asIso_hom,Category.assoc,
            Iso.inv_hom_id_assoc]
    _ = a := Total.image_factorization a

private theorem post_identity_graph {X Y Z : Total.TotalCategory P} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : ∀ n m,m ∈ Total.val g.hom n ↔ n ∈ Y.obj.support ∧ m=n) (n m : ℕ) :
    m ∈ Total.val (f ≫ g).hom n ↔ m ∈ Total.val f.hom n := by
  change m ∈ Total.val (f.hom ≫ g.hom) n ↔ m ∈ Total.val f.hom n
  rw [Total.mem_val_comp]
  constructor
  · rintro ⟨u,hu,hm⟩
    exact ((hg u m).mp hm).2.symm ▸ hu
  · intro hm
    exact ⟨m,hm,(hg m m).mpr ⟨Total.val_target f.hom n m hm,rfl⟩⟩

theorem monoPresentation_graph {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] (n m : ℕ) :
    m ∈ Total.val (monoPresentation a).hom.hom n ↔ m ∈ Total.val a.hom n := by
  have h := post_identity_graph (monoPresentation a).hom
    (axiomInclusion P S (imageCodes a) (imageCodes_enumerable a))
    (axiomInclusion_identity P S (imageCodes a) (imageCodes_enumerable a)) n m
  rw [monoPresentation_inclusion] at h
  exact h.symm

private theorem iso_reverse_graph {X Y : Total.TotalCategory P} (i : X ≅ Y) (n m : ℕ) :
    n ∈ Total.val i.inv.hom m ↔ m ∈ Total.val i.hom.hom n := by
  constructor
  · intro hn
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff i.hom.hom).mp i.hom.property n
      (Total.val_target i.inv.hom m n hn))
    have hc : v ∈ Total.val (i.inv ≫ i.hom).hom m :=
      (Total.mem_val_comp _ _ m v).mpr ⟨n,hn,hv⟩
    rw [i.inv_hom_id] at hc
    have he := (identity_graph_id Y m v).mp hc
    exact he.2 ▸ hv
  · intro hm
    obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp ((Total.total_iff i.inv.hom).mp i.inv.property m
      (Total.val_target i.hom.hom n m hm))
    have hc : u ∈ Total.val (i.hom ≫ i.inv).hom n :=
      (Total.mem_val_comp _ _ n u).mpr ⟨m,hm,hu⟩
    rw [i.hom_inv_id] at hc
    have he := (identity_graph_id X n u).mp hc
    exact he.2 ▸ hu

theorem monoPresentation_inverse_graph {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] (n m : ℕ) :
    n ∈ Total.val (monoPresentation a).inv.hom m ↔ m ∈ Total.val a.hom n :=
  (iso_reverse_graph (monoPresentation a) n m).trans (monoPresentation_graph a n m)

theorem mono_subobject_eq {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a] :
    Subobject.mk a = axiomSubobject P S (imageCodes a) (imageCodes_enumerable a) :=
  Subobject.mk_eq_mk_of_comm _ _ (monoPresentation a) (monoPresentation_inclusion a)

/-- An inclusion of code supports supplies a uniform identity map; no proof-word
preimage is selected. This also applies when the target is a theorem image. -/
def supportInclusion (X Y : Total.TotalCategory P) (hXY : X.obj.support ⊆ Y.obj.support) : X ⟶ Y :=
  identityMap X Y hXY

theorem supportInclusion_graph (X Y : Total.TotalCategory P) (hXY : X.obj.support ⊆ Y.obj.support)
    (n m : ℕ) : m ∈ Total.val (supportInclusion X Y hXY).hom n ↔ n ∈ X.obj.support ∧ m=n :=
  identityMap_graph X Y hXY n m

instance supportInclusion_mono (X Y : Total.TotalCategory P) (hXY : X.obj.support ⊆ Y.obj.support) :
    Mono (supportInclusion X Y hXY) := identityMap_mono X Y hXY

/-- Finite axioms factor through the original given monomorphism by its
proved image chart. This inverse is used only for a monomorphism. -/
def finiteIntoGivenMono {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a]
    (L : List ℕ) (hL : ∀ n ∈ L,n ∈ imageCodes a) :
    (Syntax.predicateFunctor P).obj (finiteCarrier L) ⟶ X :=
  finiteIntoAxioms P S (imageCodes a) (imageCodes_enumerable a) L hL
    (fun n hn => imageCodes_sentence a n (hL n hn)) ≫ (monoPresentation a).inv

theorem finiteIntoGivenMono_fac {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a]
    (L : List ℕ) (hL : ∀ n ∈ L,n ∈ imageCodes a) :
    finiteIntoGivenMono a L hL ≫ a =
      finiteIntoSentence P S L (fun n hn => imageCodes_sentence a n (hL n hn)) := by
  have hi : (monoPresentation a).inv ≫ a =
      axiomInclusion P S (imageCodes a) (imageCodes_enumerable a) :=
    (Iso.inv_comp_eq (monoPresentation a)).mpr (monoPresentation_inclusion a).symm
  rw [finiteIntoGivenMono,Category.assoc,hi]
  exact finiteIntoAxioms_fac P S (imageCodes a) (imageCodes_enumerable a) L hL
    (fun n hn => imageCodes_sentence a n (hL n hn))

theorem finiteSubobject_le_givenMono {X : Total.TotalCategory P} {S : PredicateCategory 𝗣𝗔}
    (a : X ⟶ (Syntax.predicateFunctor P).obj S) [Mono a]
    (L : List ℕ) (hL : ∀ n ∈ L,n ∈ imageCodes a) :
    Subobject.mk (finiteIntoSentence P S L (fun n hn => imageCodes_sentence a n (hL n hn))) ≤
      Subobject.mk a :=
  Subobject.mk_le_mk_of_comm (finiteIntoGivenMono a L hL) (finiteIntoGivenMono_fac a L hL)

end CategoricalEssentialIncompleteness.V46.Miller.AxiomSubobjects
