/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PredicateInterpretationCoproducts
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationDomain
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesLimits
public import CategoricalEssentialIncompleteness.V46Ultrapower
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Images
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Preservation of the finite and regular predicate constructions -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PredicateInterpretation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem map_inclusion_val {C D : PredicateCategory T}
    (h : T ⊢ inclusionSentence C D) (x : Obj M C) :
    ((functor T M).map (representedArrow T (GraphMorphism.inclusion h)) x).val = x.val := by
  exact ((GraphMorphism.identityGraph_eval C _ _).mp
    (value_graph T M (GraphMorphism.inclusion h) x)).2

instance map_inclusion_mono {C D : PredicateCategory T}
    (h : T ⊢ inclusionSentence C D) :
    Mono ((functor T M).map (representedArrow T (GraphMorphism.inclusion h))) := by
  apply (mono_iff_injective _).mpr
  intro x y hxy
  apply Subtype.ext
  simpa only [map_inclusion_val] using congrArg Subtype.val hxy

/-- The existential image predicate is interpreted as the set-theoretic
image of the represented graph on the whole model. -/
theorem imageCarrier_iff_range {C D : PredicateCategory T} (f : GraphMorphism T C D)
    (y : Obj M D) :
    (imageCarrier f.graph).val.Evalb ![y.val] ↔
      y ∈ Set.range ((functor T M).map (representedArrow T f)) := by
  rw [imageCarrier_eval]
  constructor
  · rintro ⟨x, hxy⟩
    exact ⟨⟨x, (f.support_model M x y.val hxy).1⟩,
      (map_class_eq_iff T M f _ y).mpr hxy⟩
  · rintro ⟨x, hxy⟩
    exact ⟨x.val, (map_class_eq_iff T M f x y).mp hxy⟩

/-- The image comparison is over the interpreted codomain. Its construction
uses the actual represented witness section and inclusion. -/
theorem preserves_regularImage {C D : PredicateCategory T} (f : C ⟶ D) :
    ∃ e : (functor T M).obj (image f) ≅ image ((functor T M).map f),
      e.hom ≫ image.ι ((functor T M).map f) = (functor T M).map (image.ι f) := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep f
  let e := representedArrow T g.corestriction
  let m := representedArrow T (GraphMorphism.inclusion g.imageInclusionProof)
  let : IsSplitEpi e := g.corestriction.isSplitEpi_of_surjective g.corestriction_surjective
  let a := image.isoStrongEpiMono e m g.image_factor
  let b := image.isoStrongEpiMono ((functor T M).map e) ((functor T M).map m)
    (by rw [← (functor T M).map_comp, g.image_factor])
  refine ⟨((functor T M).mapIso a).symm ≪≫ b, ?_⟩
  have hb : b.hom ≫ image.ι ((functor T M).map (representedArrow T g)) =
      (functor T M).map m := image.isoStrongEpiMono_hom_comp_ι _ _ _
  have ha : a.inv ≫ m = image.ι (representedArrow T g) :=
    image.isoStrongEpiMono_inv_comp_mono _ _ _
  change (functor T M).map a.inv ≫ b.hom ≫ image.ι _ = _
  rw [hb, ← (functor T M).map_comp, ha]
  rfl

def regularImageIso {C D : PredicateCategory T} (f : C ⟶ D) :
    (functor T M).obj (image f) ≅ image ((functor T M).map f) :=
  Classical.choose (preserves_regularImage T M f)

@[simp, reassoc] theorem regularImageIso_hom_ι {C D : PredicateCategory T} (f : C ⟶ D) :
    (regularImageIso T M f).hom ≫ image.ι ((functor T M).map f) =
      (functor T M).map (image.ι f) :=
  Classical.choose_spec (preserves_regularImage T M f)

/-- The terminal predicate is interpreted as a singleton. -/
def mappedTerminalIsTerminal : IsTerminal ((functor T M).obj terminalCarrier) :=
  IsTerminal.ofUniqueHom
    (fun X => ↾fun _ => ⟨0, (terminalCarrier_eval (0 : M)).mpr rfl⟩)
    (by
      intro X f
      apply ConcreteCategory.hom_ext
      intro x
      apply Subtype.ext
      exact (terminalCarrier_eval _).mp (f x).property)

instance preservesTerminal :
    PreservesLimit (Functor.empty.{0} (PredicateCategory T)) (functor T M) :=
  preservesLimit_of_preserves_limit_cone (terminalIsTerminal T)
    ((isLimitMapConeEmptyConeEquiv (functor T M) terminalCarrier).symm
      (mappedTerminalIsTerminal T M))

/-- Arithmetic pairing identifies a product predicate with the actual
Cartesian product of its two interpreted carriers. -/
def productCoding (C D : Carrier) : Obj M C × Obj M D → Obj M (productCarrier C D) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact fun p => ⟨Arithmetic.pair p.1.val p.2.val,
    (productCarrier_eval C D _).mpr ⟨p.1.val, p.2.val, rfl, p.1.property, p.2.property⟩⟩

theorem productCoding_bijective (C D : Carrier) :
    Function.Bijective (productCoding T M C D) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  constructor
  · intro x y h
    have he := (pair_eq_pair_iff _ _ _ _).mp (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)
  · intro z
    obtain ⟨x, y, he, hc, hd⟩ := (productCarrier_eval C D z.val).mp z.property
    exact ⟨(⟨x, hc⟩, ⟨y, hd⟩), Subtype.ext he.symm⟩

def productEquiv (C D : Carrier) : Obj M C × Obj M D ≃ Obj M (productCarrier C D) :=
  Equiv.ofBijective (productCoding T M C D) (productCoding_bijective T M C D)

@[simp] theorem map_productFst (C D : PredicateCategory T) (p : Obj M C × Obj M D) :
    (functor T M).map (representedArrow T (productFst T C D)) (productCoding T M C D p) = p.1 := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply (map_class_eq_iff T M _ _ _).mpr
  exact (productFst_eval T C D _ _).mpr ⟨p.2.val, rfl, p.1.property, p.2.property⟩

@[simp] theorem map_productSnd (C D : PredicateCategory T) (p : Obj M C × Obj M D) :
    (functor T M).map (representedArrow T (productSnd T C D)) (productCoding T M C D p) = p.2 := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply (map_class_eq_iff T M _ _ _).mpr
  exact (productSnd_eval T C D _ _).mpr ⟨p.1.val, rfl, p.1.property, p.2.property⟩

def mappedProductIsLimit (C D : PredicateCategory T) :
    IsLimit ((functor T M).mapCone (BinaryFan.mk (representedArrow T (productFst T C D))
      (representedArrow T (productSnd T C D)))) := by
  refine (isLimitMapConeBinaryFanEquiv _ _ _).symm ?_
  refine BinaryFan.IsLimit.mk _ (fun f g => ↾fun x => productCoding T M C D (f x, g x))
    ?_ ?_ ?_
  · intro E f g
    apply ConcreteCategory.hom_ext
    intro x
    exact map_productFst T M C D (f x, g x)
  · intro E f g
    apply ConcreteCategory.hom_ext
    intro x
    exact map_productSnd T M C D (f x, g x)
  · intro E f g m hmf hmg
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨p, hp⟩ := (productCoding_bijective T M C D).surjective (m x)
    have hf := ConcreteCategory.congr_hom hmf x
    have hg := ConcreteCategory.congr_hom hmg x
    change (functor T M).map (representedArrow T (productFst T C D)) (m x) = f x at hf
    change (functor T M).map (representedArrow T (productSnd T C D)) (m x) = g x at hg
    rw [← hp, map_productFst] at hf
    rw [← hp, map_productSnd] at hg
    exact hp.symm.trans (congrArg (productCoding T M C D) (Prod.ext hf hg))

instance preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (functor T M) where
  preservesLimit {K} := by
    have : PreservesLimit (CategoryTheory.Limits.pair (K.obj ⟨WalkingPair.left⟩)
        (K.obj ⟨WalkingPair.right⟩)) (functor T M) :=
      preservesLimit_of_preserves_limit_cone (productIsLimit T _ _)
        (mappedProductIsLimit T M _ _)
    exact preservesLimit_of_iso_diagram (functor T M) (diagramIsoPair K).symm

instance preservesFiniteProducts : PreservesFiniteProducts (functor T M) := by
  let := preservesLimitsOfShape_pempty_of_preservesTerminal (functor T M)
  exact PreservesFiniteProducts.of_preserves_binary_and_terminal (functor T M)

/-- The equalizer predicate is interpreted as equality of the actual
functions obtained from the quotient graphs. -/
def mappedEqualizerIsLimit {C D : PredicateCategory T} (f g : C ⟶ D) :
    IsLimit ((functor T M).mapCone
      (Fork.ofι (equalizerInclusion T f g) (equalizer_condition T f g))) := by
  refine (isLimitMapConeForkEquiv _ _).symm ?_
  apply Types.typeEqualizerOfUnique
  intro x hx
  have hf := (map_eq_iff_relation T M f x ((functor T M).map f x)).mp rfl
  have hg := (map_eq_iff_relation T M g x ((functor T M).map f x)).mp hx.symm
  let y : Obj M (equalizerCarrier T f g) :=
    ⟨x.val, (equalizerCarrier_eval T f g M x.val).mpr ⟨_, hf, hg⟩⟩
  have hy : (functor T M).map (equalizerInclusion T f g) y = x := by
    apply (map_eq_iff_relation T M _ y x).mpr
    exact (equalizerInclusion_eval T f g M y.val x.val).mpr ⟨y.property, rfl⟩
  refine ⟨y, hy, ?_⟩
  intro z hz
  apply Subtype.ext
  have he := congrArg Subtype.val (hz.trans hy.symm)
  simpa only [equalizerInclusion, map_inclusion_val] using he

instance preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair (functor T M) where
  preservesLimit {K} := by
    have : PreservesLimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) (functor T M) :=
      preservesLimit_of_preserves_limit_cone (equalizerIsLimit T _ _)
        (mappedEqualizerIsLimit T M _ _)
    exact preservesLimit_of_iso_diagram (functor T M) (diagramIsoParallelPair K).symm

instance preservesFiniteLimits : PreservesFiniteLimits (functor T M) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (functor T M)

/-- Proposition 6.4 in the arbitrary predicate presentation: all finite
limits, all finite coproducts and the actual regular images are preserved. -/
theorem regular : PreservesFiniteLimits (functor T M) ∧
    PreservesFiniteCoproducts (functor T M) ∧
    ∀ (C D : PredicateCategory T) (f : C ⟶ D),
      ∃ e : (functor T M).obj (image f) ≅ image ((functor T M).map f),
        e.hom ≫ image.ι ((functor T M).map f) = (functor T M).map (image.ι f) :=
  ⟨inferInstance, inferInstance, fun _ _ f => preserves_regularImage T M f⟩

instance totalPreservesFiniteLimits : PreservesFiniteLimits (totalFunctor T M) := by
  dsimp [totalFunctor]
  infer_instance

instance totalPreservesFiniteCoproducts : PreservesFiniteCoproducts (totalFunctor T M) := by
  dsimp [totalFunctor]
  infer_instance

/-- Equivalences preserve the actual chosen regular images over their
codomains, by mapping the strong-epi/mono factorization. -/
def inverseImageIso {X Y : TotalSplit T} (f : X ⟶ Y) :
    (predicateEquivalence T).inverse.obj (image f) ≅
      image ((predicateEquivalence T).inverse.map f) :=
  image.isoStrongEpiMono ((predicateEquivalence T).inverse.map (factorThruImage f))
    ((predicateEquivalence T).inverse.map (image.ι f))
    (by rw [← Functor.map_comp, image.fac])

@[simp, reassoc] theorem inverseImageIso_hom_ι {X Y : TotalSplit T} (f : X ⟶ Y) :
    (inverseImageIso T f).hom ≫ image.ι ((predicateEquivalence T).inverse.map f) =
      (predicateEquivalence T).inverse.map (image.ι f) :=
  image.isoStrongEpiMono_hom_comp_ι _ _ _

/-- The regular image comparison on every object of the total restriction
splitting, not only on the selected predicate presentations. -/
def totalRegularImageIso {X Y : TotalSplit T} (f : X ⟶ Y) :
    (totalFunctor T M).obj (image f) ≅ image ((totalFunctor T M).map f) :=
  (functor T M).mapIso (inverseImageIso T f) ≪≫
    regularImageIso T M ((predicateEquivalence T).inverse.map f)

@[simp, reassoc] theorem totalRegularImageIso_hom_ι {X Y : TotalSplit T} (f : X ⟶ Y) :
    (totalRegularImageIso T M f).hom ≫ image.ι ((totalFunctor T M).map f) =
      (totalFunctor T M).map (image.ι f) := by
  change (functor T M).map (inverseImageIso T f).hom ≫
    (regularImageIso T M ((predicateEquivalence T).inverse.map f)).hom ≫ image.ι _ = _
  rw [regularImageIso_hom_ι, ← Functor.map_comp, inverseImageIso_hom_ι]
  rfl

/-- Proposition 6.4 on the actual total restriction splitting. -/
theorem total_regular : PreservesFiniteLimits (totalFunctor T M) ∧
    PreservesFiniteCoproducts (totalFunctor T M) ∧
    ∀ (X Y : TotalSplit T) (f : X ⟶ Y),
      ∃ e : (totalFunctor T M).obj (image f) ≅ image ((totalFunctor T M).map f),
        e.hom ≫ image.ι ((totalFunctor T M).map f) = (totalFunctor T M).map (image.ι f) :=
  ⟨inferInstance, inferInstance,
    fun _ _ f => ⟨totalRegularImageIso T M f, totalRegularImageIso_hom_ι T M f⟩⟩

instance canonicalPreservesFiniteLimits : PreservesFiniteLimits (canonicalDomainFunctor T M) :=
  preservesFiniteLimits_of_natIso (totalCanonicalComparison T M)

instance canonicalPreservesFiniteCoproducts :
    PreservesFiniteCoproducts (canonicalDomainFunctor T M) where
  preserves _n := preservesColimitsOfShape_of_natIso (totalCanonicalComparison T M)

private theorem map_conjugate {A : Type*} [Category A] {G H : A ⥤ Type}
    (η : G ≅ H) {X Y : A} (f : X ⟶ Y) :
    H.map f = η.inv.app X ≫ G.map f ≫ η.hom.app Y := by
  symm
  rw [η.hom.naturality, ← Category.assoc,
    η.inv_hom_id_app, Category.id_comp]

/-- Image preservation is transported through the actual canonical-domain
comparison by conjugating the mapped image factorization. -/
theorem preserves_canonical_regularImage {X Y : TotalSplit T} (f : X ⟶ Y) :
    ∃ e : (canonicalDomainFunctor T M).obj (image f) ≅
      image ((canonicalDomainFunctor T M).map f),
      e.hom ≫ image.ι ((canonicalDomainFunctor T M).map f) =
        (canonicalDomainFunctor T M).map (image.ι f) := by
  let G := totalFunctor T M
  let H := canonicalDomainFunctor T M
  let η := totalCanonicalComparison T M
  let i := totalRegularImageIso T M f
  have hleft : G.map (factorThruImage f) ≫ i.hom = factorThruImage (G.map f) := by
    apply (cancel_mono (image.ι (G.map f))).mp
    rw [Category.assoc, totalRegularImageIso_hom_ι, ← G.map_comp, image.fac, image.fac]
  have he : G.map (factorThruImage f) = factorThruImage (G.map f) ≫ i.inv := by
    rw [← hleft, Category.assoc, i.hom_inv_id, Category.comp_id]
  let : Epi (G.map (factorThruImage f)) := by rw [he]; infer_instance
  let : StrongEpi (G.map (factorThruImage f)) := strongEpi_of_epi _
  let : Mono (G.map (image.ι f)) := by
    rw [← totalRegularImageIso_hom_ι T M f]
    infer_instance
  let : StrongEpi (H.map (factorThruImage f)) := by
    rw [map_conjugate η]
    infer_instance
  let : Mono (H.map (image.ι f)) := by
    rw [map_conjugate η]
    infer_instance
  refine ⟨image.isoStrongEpiMono (H.map (factorThruImage f)) (H.map (image.ι f))
    (by rw [← H.map_comp, image.fac]), ?_⟩
  exact image.isoStrongEpiMono_hom_comp_ι _ _ _

def canonicalRegularImageIso {X Y : TotalSplit T} (f : X ⟶ Y) :
    (canonicalDomainFunctor T M).obj (image f) ≅
      image ((canonicalDomainFunctor T M).map f) :=
  Classical.choose (preserves_canonical_regularImage T M f)

@[simp, reassoc] theorem canonicalRegularImageIso_hom_ι {X Y : TotalSplit T} (f : X ⟶ Y) :
    (canonicalRegularImageIso T M f).hom ≫ image.ι ((canonicalDomainFunctor T M).map f) =
      (canonicalDomainFunctor T M).map (image.ι f) :=
  Classical.choose_spec (preserves_canonical_regularImage T M f)

/-- Proposition 6.4 for the literal chosen domain splitting of the existing
model interpretation, including every total-split object and morphism. -/
theorem canonical_regular : PreservesFiniteLimits (canonicalDomainFunctor T M) ∧
    PreservesFiniteCoproducts (canonicalDomainFunctor T M) ∧
    ∀ (X Y : TotalSplit T) (f : X ⟶ Y),
      ∃ e : (canonicalDomainFunctor T M).obj (image f) ≅
          image ((canonicalDomainFunctor T M).map f),
        e.hom ≫ image.ι ((canonicalDomainFunctor T M).map f) =
          (canonicalDomainFunctor T M).map (image.ι f) :=
  ⟨inferInstance, inferInstance,
    fun _ _ f => ⟨canonicalRegularImageIso T M f, canonicalRegularImageIso_hom_ι T M f⟩⟩

end CategoricalEssentialIncompleteness.V46.PredicateInterpretation
