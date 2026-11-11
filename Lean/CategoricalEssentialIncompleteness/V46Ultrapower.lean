/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Images
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The ultrapower functor on sets and its finite categorical constructions -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Filter

namespace CategoricalEssentialIncompleteness.V46.Ultrapower

variable {I : Type u} (U : Ultrafilter I)

/-- Functions modulo equality on a member of the ultrafilter. -/
abbrev Obj (X : Type u) : Type u := Germ (U : Filter I) X

/-- Coordinatewise action on functions. -/
def functor : Type u ⥤ Type u where
  obj := Obj U
  map f := ↾(Germ.map f)
  map_id X := by
    ext x
    exact congrFun Germ.map_id x
  map_comp f g := by
    ext x
    exact (Germ.map_map g f x).symm

@[simp] theorem map_representative {X Y : Type u} (f : X ⟶ Y) (x : I → X) :
    (functor U).map f (Germ.ofFun x) = Germ.ofFun (fun i => f (x i)) := rfl

/-- Coordinatewise injectivity descends to ultrapowers. -/
theorem map_injective {X Y : Type u} (f : X → Y) (hf : Function.Injective f) :
    Function.Injective (Germ.map f : Obj U X → Obj U Y) := by
  intro x y h
  induction x using Germ.inductionOn with | _ x =>
    induction y using Germ.inductionOn with | _ y =>
      apply Germ.coe_eq.mpr
      have he := Germ.coe_eq.mp h
      exact he.mono (fun _ hxy => hf hxy)

/-- Choice of a preimage in each coordinate proves preservation of surjections. -/
theorem map_surjective {X Y : Type u} (f : X → Y) (hf : Function.Surjective f) :
    Function.Surjective (Germ.map f : Obj U X → Obj U Y) := by
  intro y
  induction y using Germ.inductionOn with | _ y =>
    refine ⟨Germ.ofFun (fun i => Classical.choose (hf (y i))), ?_⟩
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun i => Classical.choose_spec (hf (y i)))

instance map_mono {X Y : Type u} (f : X ⟶ Y) [Mono f] : Mono ((functor U).map f) :=
  (mono_iff_injective _).mpr
    (map_injective U f ((mono_iff_injective f).mp inferInstance))

instance map_epi {X Y : Type u} (f : X ⟶ Y) [Epi f] : Epi ((functor U).map f) :=
  (epi_iff_surjective _).mpr
    (map_surjective U f ((epi_iff_surjective f).mp inferInstance))

instance map_strongEpi {X Y : Type u} (f : X ⟶ Y) [Epi f] :
    StrongEpi ((functor U).map f) := strongEpi_of_epi _

/-- A germ belongs to an interpreted subset precisely when it has a
representative lying in that subset at every coordinate. -/
theorem subtype_range {X : Type u} (p : X → Prop) (x : Obj U X) :
    x ∈ Set.range (Germ.map (Subtype.val : {y // p y} → X)) ↔ Germ.LiftPred p x := by
  classical
  induction x using Germ.inductionOn with | _ x =>
    constructor
    · rintro ⟨y, hy⟩
      induction y using Germ.inductionOn with | _ y =>
        have he := Germ.coe_eq.mp hy
        exact he.mono (fun i hi => hi ▸ (y i).property)
    · intro hx
      obtain ⟨i, hi⟩ := hx.exists
      let fallback : {y // p y} := ⟨x i, hi⟩
      let y : I → {z // p z} := fun j => if hj : p (x j) then ⟨x j, hj⟩ else fallback
      refine ⟨Germ.ofFun y, Germ.coe_eq.mpr ?_⟩
      filter_upwards [hx] with j hj
      simp [y, hj]

/-- The predicate comparison includes empty subsets; no inhabitedness
assumption on the subset is made. -/
def subtypeEquiv {X : Type u} (p : X → Prop) :
    Obj U {x // p x} ≃ {x : Obj U X // Germ.LiftPred p x} :=
  Equiv.ofBijective
    (fun x => ⟨Germ.map Subtype.val x, (subtype_range U p _).mp ⟨x, rfl⟩⟩)
    ⟨fun x y h => map_injective U Subtype.val Subtype.val_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨y, hy⟩ := (subtype_range U p x.val).mpr x.property
        exact ⟨y, Subtype.ext hy⟩⟩

@[simp] theorem subtypeEquiv_val {X : Type u} (p : X → Prop) (x : Obj U {x // p x}) :
    (subtypeEquiv U p x).val = Germ.map Subtype.val x := rfl

/-- The subset comparison commutes with every function preserving the
two predicates, not merely with chosen elements. -/
theorem subtypeEquiv_naturality {X Y : Type u} (p : X → Prop) (q : Y → Prop)
    (f : X → Y) (hf : ∀ x, p x → q (f x)) (a : Obj U {x // p x}) :
    (subtypeEquiv U q (Germ.map (fun x : {x // p x} => ⟨f x.val, hf x.val x.property⟩) a)).val =
      Germ.map f (subtypeEquiv U p a).val := by
  induction a using Germ.inductionOn with | _ a => rfl

/-- The canonical comparison for a finite family of products. -/
def productComparison {J : Type} (X : J → Type u) :
    Obj U (∀ j, X j) → ∀ j, Obj U (X j) :=
  fun x j => Germ.map (fun a => a j) x

theorem productComparison_bijective {J : Type} [Finite J] (X : J → Type u) :
    Function.Bijective (productComparison U X) := by
  constructor
  · intro x y h
    induction x using Germ.inductionOn with | _ x =>
      induction y using Germ.inductionOn with | _ y =>
        apply Germ.coe_eq.mpr
        have he : ∀ j, ∀ᶠ i in (U : Filter I), x i j = y i j :=
          fun j => Germ.coe_eq.mp (congrFun h j)
        filter_upwards [Filter.eventually_all.mpr he] with i hi
        exact funext hi
  · intro x
    refine ⟨Germ.ofFun (fun i j => Quotient.out (x j) i), ?_⟩
    funext j
    exact Quotient.out_eq (x j)

def productEquiv {J : Type} [Finite J] (X : J → Type u) :
    Obj U (∀ j, X j) ≃ (∀ j, Obj U (X j)) :=
  Equiv.ofBijective (productComparison U X) (productComparison_bijective U X)

/-- Finite coproducts are interpreted by the unique tag holding on a
member of the ultrafilter. -/
def coproductComparison {J : Type} (X : J → Type u) :
    (Σ j, Obj U (X j)) → Obj U (Σ j, X j) :=
  fun x => Germ.map (Sigma.mk x.1) x.2

theorem coproductComparison_bijective {J : Type} [Finite J] (X : J → Type u) :
    Function.Bijective (coproductComparison U X) := by
  classical
  constructor
  · rintro ⟨j, x⟩ ⟨k, y⟩ h
    induction x using Germ.inductionOn with | _ x =>
      induction y using Germ.inductionOn with | _ y =>
        have he := Germ.coe_eq.mp h
        obtain ⟨i, hi⟩ := he.exists
        have hjk : j = k := congrArg Sigma.fst hi
        subst k
        apply congrArg (Sigma.mk j)
        apply Germ.coe_eq.mpr
        exact he.mono (fun _ hxy => eq_of_heq (Sigma.mk.inj hxy).2)
  · intro x
    induction x using Germ.inductionOn with | _ x =>
      have ht : ∀ᶠ i in (U : Filter I), ∃ j, (x i).1 = j :=
        Eventually.of_forall (fun i => ⟨(x i).1, rfl⟩)
      obtain ⟨j, hj⟩ := Ultrafilter.eventually_exists_iff.mp ht
      obtain ⟨i, hi⟩ := hj.exists
      let fallback : X j := hi ▸ (x i).2
      let y : I → X j := fun k => if hk : (x k).1 = j then hk ▸ (x k).2 else fallback
      refine ⟨⟨j, Germ.ofFun y⟩, Germ.coe_eq.mpr ?_⟩
      filter_upwards [hj] with k hk
      change Sigma.mk j (y k) = x k
      dsimp [y]
      rw [dite_eq_left hk]
      cases hk
      rfl

def coproductEquiv {J : Type} [Finite J] (X : J → Type u) :
    (Σ j, Obj U (X j)) ≃ Obj U (Σ j, X j) :=
  Equiv.ofBijective (coproductComparison U X) (coproductComparison_bijective U X)

/-- The map of a finite product cone remains a product cone. -/
def mappedProductIsLimit {J : Type} [Finite J] (X : J → Type u) :
    IsLimit ((functor U).mapCone (Types.productLimitCone X).cone) where
  lift s := ↾fun x => (productEquiv U X).symm (fun j => s.π.app ⟨j⟩ x)
  fac s j := by
    rcases j with ⟨j⟩
    ext x
    exact congrFun ((productEquiv U X).apply_symm_apply (fun k => s.π.app ⟨k⟩ x)) j
  uniq s m hm := by
    ext x
    apply (productComparison_bijective U X).injective
    funext j
    have he := ConcreteCategory.congr_hom (hm ⟨j⟩) x
    exact he.trans (congrFun ((productEquiv U X).apply_symm_apply
      (fun k => s.π.app ⟨k⟩ x)) j).symm

instance preservesFiniteProducts : PreservesFiniteProducts (functor U) where
  preserves n := ⟨fun {K} => by
    let X : Fin n → Type u := fun j => K.obj ⟨j⟩
    have : PreservesLimit (Discrete.functor X) (functor U) :=
      preservesLimit_of_preserves_limit_cone (Types.productLimitCone X).isLimit
        (mappedProductIsLimit U X)
    exact preservesLimit_of_iso_diagram (functor U)
      (Discrete.natIso (fun j => Iso.refl (K.obj j)) : Discrete.functor X ≅ K)⟩

theorem equalizer_predicate {X Y : Type u} (f g : X → Y) (x : Obj U X) :
    Germ.map f x = Germ.map g x ↔ Germ.LiftPred (fun y => f y = g y) x := by
  induction x using Germ.inductionOn with | _ x =>
    exact Germ.coe_eq

/-- Equality on an ultrafilter-large set permits replacement of the
other coordinates by a point of the equalizer. -/
def mappedEqualizerIsLimit {X Y : Type u} (f g : X ⟶ Y) :
    IsLimit ((functor U).mapCone (Types.equalizerLimit (g := f) (h := g)).cone) := by
  let w : (↾(Subtype.val : {x : X // f x = g x} → X)) ≫ f =
      (↾(Subtype.val : {x : X // f x = g x} → X)) ≫ g := by
    ext x
    exact x.property
  change IsLimit ((functor U).mapCone (Fork.ofι _ w))
  refine (isLimitMapConeForkEquiv (functor U) w).symm ?_
  apply Types.typeEqualizerOfUnique
  intro x hx
  obtain ⟨y, hy⟩ := (subtype_range U (fun x : X => f x = g x) x).mpr
    ((equalizer_predicate U f g x).mp hx)
  refine ⟨y, hy, ?_⟩
  intro z hz
  exact map_injective U Subtype.val Subtype.val_injective (hz.trans hy.symm)

instance preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair (functor U) where
  preservesLimit {K} := by
    have : PreservesLimit (parallelPair (K.map WalkingParallelPairHom.left)
        (K.map WalkingParallelPairHom.right)) (functor U) :=
      preservesLimit_of_preserves_limit_cone
        (Types.equalizerLimit (g := K.map WalkingParallelPairHom.left)
          (h := K.map WalkingParallelPairHom.right)).isLimit
        (mappedEqualizerIsLimit U _ _)
    exact preservesLimit_of_iso_diagram (functor U) (diagramIsoParallelPair K).symm

instance preservesFiniteLimits : PreservesFiniteLimits (functor U) :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts (functor U)

/-- The canonical finite coproduct cofan is still a coproduct after
coordinatewise interpretation. -/
def mappedCoproductIsColimit {J : Type} [Finite J] (X : J → Type u) :
    IsColimit ((functor U).mapCocone (Types.coproductColimitCocone X).cocone) := by
  refine (isColimitMapCoconeCofanMkEquiv (functor U) X
    (fun j => ↾(Sigma.mk j))).symm ?_
  apply Classical.choice
  apply (Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mpr
  exact coproductComparison_bijective U X

instance preservesFiniteCoproducts : PreservesFiniteCoproducts (functor U) where
  preserves n := ⟨fun {K} => by
    let X : Fin n → Type u := fun j => K.obj ⟨j⟩
    have : PreservesColimit (Discrete.functor X) (functor U) :=
      preservesColimit_of_preserves_colimit_cocone
        (Types.coproductColimitCocone X).isColimit (mappedCoproductIsColimit U X)
    exact preservesColimit_of_iso_diagram (functor U)
      (Discrete.natIso (fun j => Iso.refl (K.obj j)) : Discrete.functor X ≅ K)⟩

/-- The ordinary surjection--inclusion factorization of a function. -/
def typeStrongEpiMono {X Y : Type u} (f : X ⟶ Y) : StrongEpiMonoFactorisation f := by
  let e : X ⟶ Set.range f := ↾(Set.rangeFactorization f)
  have he : Function.Surjective e := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  letI : Epi e := (epi_iff_surjective e).mpr he
  letI : StrongEpi e := strongEpi_of_epi e
  exact
    { I := Set.range f
      m := ↾(Subtype.val : Set.range f → Y)
      m_mono := (mono_iff_injective _).mpr Subtype.val_injective
      e := e
      fac := rfl }

instance typeHasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations (Type u) :=
  HasStrongEpiMonoFactorisations.mk typeStrongEpiMono

/-- The interpreted surjection--inclusion factorization is a regular
image factorization. The isomorphism is over the interpreted codomain. -/
def regularImageIso {X Y : Type u} (f : X ⟶ Y) :
    (functor U).obj (image f) ≅ image ((functor U).map f) :=
  image.isoStrongEpiMono ((functor U).map (factorThruImage f))
    ((functor U).map (image.ι f)) (by rw [← (functor U).map_comp, image.fac])

@[simp, reassoc] theorem regularImageIso_hom_ι {X Y : Type u} (f : X ⟶ Y) :
    (regularImageIso U f).hom ≫ image.ι ((functor U).map f) =
      (functor U).map (image.ι f) :=
  image.isoStrongEpiMono_hom_comp_ι _ _ _

/-- Lemma 6.7: the ultrapower functor on sets preserves finite limits,
finite coproducts and regular images, including empty carriers. -/
theorem regular : PreservesFiniteLimits (functor U) ∧
    PreservesFiniteCoproducts (functor U) ∧
    ∀ (X Y : Type u) (f : X ⟶ Y),
      ∃ e : (functor U).obj (image f) ≅ image ((functor U).map f),
        e.hom ≫ image.ι ((functor U).map f) = (functor U).map (image.ι f) :=
  ⟨inferInstance, inferInstance, fun _ _ f => ⟨regularImageIso U f, regularImageIso_hom_ι U f⟩⟩

end CategoricalEssentialIncompleteness.V46.Ultrapower
