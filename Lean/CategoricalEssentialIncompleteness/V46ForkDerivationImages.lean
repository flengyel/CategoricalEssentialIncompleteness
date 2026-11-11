/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationInitial
public import CategoricalEssentialIncompleteness.V46ForkDerivationDiagram
public import CategoricalEssentialIncompleteness.V46ForkAxiomClosure
public import CategoricalEssentialIncompleteness.EffectiveForkRegular
public import CategoricalEssentialIncompleteness.V46RegularImage
public import CategoricalEssentialIncompleteness.V46RegularEquivalence
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # The concrete fork derivation image and its endpoint extensions

The initial algebra is the constructed algebra on the existing finite-proof
object. Its regular image is compared to the existing conclusion range.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkDerivationImages

open EffectiveFork (V)
local notation "E" => EffectiveFork.Total
local notation "S" => ForkDerivation.sentenceObject

/-- This is the conclusion of the constructed inference algebra. -/
abbrev conclusion (a b : Idem V) := (ForkDerivation.inferenceAlgebra a b).a.hom

/-- The old proof object and conclusion are retained by the construction. -/
theorem conclusion_hom (a b : Idem V) :
    (conclusion a b).hom = ForkSyntax.conclusion a b := rfl

def theoremRange (a b : Idem V) : Idem ForkSyntax.S :=
  Ranges.range (conclusion a b).hom

theorem theoremRange_eq_t0 (a b : Idem V) :
    theoremRange a b = ForkSyntax.t0 a b := by
  exact congrArg Ranges.range (conclusion_hom a b)

def theoremObject (a b : Idem V) : E := EffectiveFork.imageObject (conclusion a b)

def theoremInclusion (a b : Idem V) : theoremObject a b ⟶ S :=
  EffectiveFork.imageInclusion (conclusion a b)

instance theoremInclusion_mono (a b : Idem V) : Mono (theoremInclusion a b) := by
  dsimp only [theoremInclusion]
  infer_instance

def theoremSubobject (a b : Idem V) : Subobject S :=
  imageSubobject (conclusion a b)

theorem theoremObject_domain (a b : Idem V) :
    (theoremObject a b).obj = EffectiveFork.domainObject (theoremRange a b) := rfl

theorem theoremInclusion_hom (a b : Idem V) :
    (theoremInclusion a b).hom =
      EffectiveFork.domainInclusion (theoremRange a b) := rfl

private def explicitImageIso {X Y : E} (f : X ⟶ Y) :
    image f ≅ EffectiveFork.imageObject f :=
  IsImage.isoExt (Image.isImage f) (EffectiveFork.imageIsImage f)

private theorem explicitImageIso_hom {X Y : E} (f : X ⟶ Y) :
    (explicitImageIso f).hom ≫ EffectiveFork.imageInclusion f = image.ι f :=
  IsImage.isoExt_hom_m (Image.isImage f) (EffectiveFork.imageIsImage f)

private theorem explicitImageIso_inv {X Y : E} (f : X ⟶ Y) :
    (explicitImageIso f).inv ≫ image.ι f = EffectiveFork.imageInclusion f :=
  IsImage.isoExt_inv_m (Image.isImage f) (EffectiveFork.imageIsImage f)

/-- The canonical regular image is the actual c.e. domain subfunctor of
the partial identity given by the conclusion range. -/
theorem theoremSubobject_eq_domain (a b : Idem V) :
    theoremSubobject a b = Subobject.mk (theoremInclusion a b) :=
  Subobject.mk_eq_mk_of_comm _ _ (explicitImageIso (conclusion a b))
    (explicitImageIso_hom (conclusion a b))

private theorem closed_of_iso {C : Type u} [Category.{v} C]
    {F U W : C} (H : Over F ⥤ Over F)
    (m : U ⟶ F) (n : W ⟶ F) (e : U ≅ W)
    (he : e.hom ≫ n = m) (hm : ClosedUnder H m) : ClosedUnder H n := by
  obtain ⟨α⟩ := hm
  let ε : Over.mk m ≅ Over.mk n := Over.isoMk e he
  exact ⟨H.map ε.inv ≫ α ≫ ε.hom⟩

/-- Theorem A.5 is applied to the constructed concrete initial algebra;
its initiality is supplied by its proved universal property. -/
theorem least_theorem_image (a b : Idem V) :
    ClosedUnder (ForkDerivation.rules a b).inference (image.ι (conclusion a b)) ∧
      ∀ {U : E} (m : U ⟶ S) [Mono m],
        ClosedUnder (ForkDerivation.rules a b).inference m →
          ∃ w : image (conclusion a b) ⟶ U,
            w ≫ m = image.ι (conclusion a b) :=
  (ForkDerivation.rules a b).least_theorem_subobject
    (ForkDerivation.inferenceAlgebra a b) (ForkDerivation.inferenceInitial a b)

/-- The ordinary image subobject is least among the subobjects closed
under the displayed finite inference signature. -/
theorem theoremSubobject_isLeast (a b : Idem V) :
    IsLeast {P : Subobject S |
      ClosedUnder (ForkDerivation.rules a b).inference P.arrow}
      (theoremSubobject a b) := by
  have h := least_theorem_image a b
  constructor
  · exact closed_of_iso _ _ _ (imageSubobjectIso (conclusion a b)).symm
      (imageSubobject_arrow' (conclusion a b)) h.1
  · intro P hP
    obtain ⟨w,hw⟩ := h.2 P.arrow hP
    apply Subobject.le_of_comm ((imageSubobjectIso (conclusion a b)).hom ≫ w)
    rw [Category.assoc,hw,imageSubobject_arrow]

/-- Leastness holds on the actual domain inclusion of the existing
partial identity, rather than only on an isomorphic image carrier. -/
theorem theoremInclusion_least (a b : Idem V) :
    ClosedUnder (ForkDerivation.rules a b).inference (theoremInclusion a b) ∧
      ∀ {U : E} (m : U ⟶ S) [Mono m],
        ClosedUnder (ForkDerivation.rules a b).inference m →
          ∃ w : theoremObject a b ⟶ U, w ≫ m = theoremInclusion a b := by
  have h := least_theorem_image a b
  constructor
  · exact closed_of_iso _ _ _ (explicitImageIso (conclusion a b))
      (explicitImageIso_hom (conclusion a b)) h.1
  · intro U m _ hm
    obtain ⟨w,hw⟩ := h.2 m hm
    refine ⟨(explicitImageIso (conclusion a b)).inv ≫ w,?_⟩
    rw [Category.assoc,hw]
    exact explicitImageIso_inv (conclusion a b)

/-- In particular every actual logical or atomic nullary rule concludes
in the constructed image. Its axiom tag and parameters remain available. -/
theorem image_contains_axioms (a b : Idem V) :
    ∃ w : (ForkDerivation.rules a b).instances 0 ⟶ image (conclusion a b),
      w ≫ image.ι (conclusion a b) = (ForkDerivation.rules a b).conclusion 0 := by
  obtain ⟨α⟩ := (least_theorem_image a b).1
  exact (ForkDerivation.rules a b).closed_contains_nullary _ α

private theorem domainRetraction_restriction {X : EffectiveFork.Object} (e : Idem X) :
    rst (EffectiveFork.domainRetraction e) = e.hom := by
  calc
    _ = rst (EffectiveFork.domainRetraction e ≫ EffectiveFork.domainInclusion e) :=
      (rst_comp_of_isTotal _ (EffectiveFork.domainInclusion_total e)).symm
    _ = rst e.hom := congrArg rst (EffectiveFork.retraction_inclusion e)
    _ = e.hom := e.restriction

/-- Lemma A.7 identifies the partial identity of the regular image with
the actual conclusion range in the effective partial fork category. -/
theorem range_regular_image (a b : Idem V) :
    (theoremRange a b).hom =
      EffectiveFork.domainRetraction (theoremRange a b) ≫ (theoremInclusion a b).hom := by
  have hr : EffectiveFork.domainRetraction (theoremRange a b) ≫
      (theoremInclusion a b).hom =
      rst (EffectiveFork.domainRetraction (theoremRange a b)) :=
    (EffectiveFork.retraction_inclusion (theoremRange a b)).trans
      (domainRetraction_restriction (theoremRange a b)).symm
  have h := LocalConnectedness.V46.range_regularImage
    (EffectiveFork.imageQuotient (conclusion a b)) (theoremInclusion a b)
    (EffectiveFork.domainRetraction (theoremRange a b))
    (EffectiveFork.inclusion_retraction (theoremRange a b)) hr
  have hf : (EffectiveFork.imageQuotient (conclusion a b)).hom ≫
      (theoremInclusion a b).hom = (conclusion a b).hom :=
    congrArg (fun f => f.hom) (EffectiveFork.image_factorization (conclusion a b))
  rw [hf] at h
  exact h

/-- The existing finite-proof leastness describes the components of the
same image identified by concrete initiality above. -/
theorem component_theory_isLeast (a b : Idem V) :
    IsLeast {e | ForkSyntax.IsTheory a b e} (theoremRange a b) := by
  rw [theoremRange_eq_t0]
  exact ForkSyntax.t0_isLeast a b

theorem center_theorem_codes (a b : Idem V) (n : ℕ) :
    n ∈ (theoremObject a b).obj.center.support ↔
      ForkSyntax.Formula.decode n ∈ ForkSyntax.Theorems
        (EnumerableCarriers.support (EffectiveFork.centerIdem a))
        (EnumerableCarriers.support (EffectiveFork.centerIdem b)) :=
  ForkSyntax.center_t0 a b n

theorem left_theorem_codes (a b : Idem V) (n : ℕ) :
    n ∈ (theoremObject a b).obj.left.support ↔
      ForkSyntax.Formula.decode n ∈ ForkSyntax.Theorems
        (EnumerableCarriers.support (EffectiveFork.leftIdem a))
        (EnumerableCarriers.support (EffectiveFork.leftIdem b)) :=
  ForkSyntax.left_t0 a b n

theorem right_theorem_codes (a b : Idem V) (n : ℕ) :
    n ∈ (theoremObject a b).obj.right.support ↔
      ForkSyntax.Formula.decode n ∈ ForkSyntax.Theorems
        (EnumerableCarriers.support (EffectiveFork.rightIdem a))
        (EnumerableCarriers.support (EffectiveFork.rightIdem b)) :=
  ForkSyntax.right_t0 a b n

/-- Theorem 9.4, with its concrete initial image, component leastness,
the two atomic bounds and consistency. -/
theorem proof_presentation (a b : Idem V) (hd : a ⊓ b = ⊥) :
    IsLeast {P : Subobject S |
      ClosedUnder (ForkDerivation.rules a b).inference P.arrow}
      (theoremSubobject a b) ∧
    IsLeast {e | ForkSyntax.IsTheory a b e} (theoremRange a b) ∧
      a ≤ Idem.pull ForkSyntax.theta (theoremRange a b) ∧
      b ≤ Idem.pull ForkSyntax.theta (Idem.pull ForkSyntax.nu (theoremRange a b)) ∧
      theoremRange a b ⊓ Idem.pull ForkSyntax.nu (theoremRange a b) = ⊥ := by
  refine ⟨theoremSubobject_isLeast a b,component_theory_isLeast a b,?_,?_,?_⟩
  · rw [theoremRange_eq_t0]
    exact ForkSyntax.positive_inclusion a b
  · rw [theoremRange_eq_t0]
    exact ForkSyntax.negative_inclusion a b
  · rw [theoremRange_eq_t0]
    exact ForkSyntax.t0_consistency a b hd

def categoricalTheory : Idem ForkSyntax.S :=
  theoremRange
    (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair0)
    (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair1)

theorem categoricalTheory_eq : categoricalTheory = ForkSyntax.categoricalTheory :=
  theoremRange_eq_t0 _ _

theorem endpoint_theorem_codes (i : Bool) :
    ForkSyntax.endpointTheory i categoricalTheory =
      ForkSyntax.endpointTheory i ForkSyntax.categoricalTheory :=
  congrArg (ForkSyntax.endpointTheory i) categoricalTheory_eq

/-- An arbitrary c.e. endpoint extension is quantified directly. No
extension at the other two components is part of its data. -/
theorem endpoint_ce_extension_incomplete (i : Bool) (T : Set ℕ)
    (hT : REPred (· ∈ T))
    (hext : EnumerableCarriers.support (ForkSyntax.endpointTheory i categoricalTheory) ⊆ T)
    (hc : ∀ n : ℕ, n ∈ T → ForkSyntax.negCode n ∉ T) :
    ∃ n : ℕ, n ∉ T ∧ ForkSyntax.negCode n ∉ T := by
  apply ForkSyntax.endpoint_ce_extension_incomplete i T hT _ hc
  exact (congrArg EnumerableCarriers.support (endpoint_theorem_codes i)) ▸ hext

/-- Corollary 9.6 for the deductive closure of an arbitrary c.e. axiom
set in the selected endpoint language. -/
theorem endpoint_axiom_extension_incomplete (i : Bool) (A : Set ℕ)
    (hA : REPred (· ∈ A))
    (hext : EnumerableCarriers.support (ForkSyntax.endpointTheory i categoricalTheory) ⊆
      ForkAxiomClosure.theoremCodes A)
    (hc : ∀ p : ForkSyntax.Formula,
      ¬(ForkAxiomClosure.Derives A p ∧ ForkAxiomClosure.Derives A (.neg p))) :
    ∃ p : ForkSyntax.Formula,
      ¬ForkAxiomClosure.Derives A p ∧ ¬ForkAxiomClosure.Derives A (.neg p) := by
  apply ForkAxiomClosure.endpoint_axiom_extension_incomplete i A hA _ hc
  exact (congrArg EnumerableCarriers.support (endpoint_theorem_codes i)) ▸ hext

namespace LiteralDiagram

local notation "D" => ForkDerivation.Diagram.Object
local notation "F" => ForkDerivation.Diagram.realization
local notation "LS" => ForkDerivation.Diagram.sentences

/-- The conclusion belongs to the constructed algebra in the literal
walking-span category of numerical carriers. -/
abbrev conclusion (a b : Idem V) :=
  (ForkDerivation.Diagram.inferenceAlgebra a b).a.hom

theorem conclusion_realization (a b : Idem V) :
    conclusion a b = (F).map (ForkDerivation.conclusion a b) :=
  ForkDerivation.Diagram.inference_conclusion a b

def theoremSubobject (a b : Idem V) : Subobject LS :=
  imageSubobject (conclusion a b)

/-- The target is the realization of the old explicit conclusion image,
including its actual effective-fork image carrier. -/
def theoremObject (a b : Idem V) : D :=
  (F).obj (EffectiveFork.imageObject (ForkDerivation.conclusion a b))

def theoremInclusion (a b : Idem V) : theoremObject a b ⟶ LS :=
  (F).map (EffectiveFork.imageInclusion (ForkDerivation.conclusion a b))

instance theoremInclusion_mono (a b : Idem V) : Mono (theoremInclusion a b) := by
  dsimp only [theoremInclusion]
  infer_instance

private instance realizedImageQuotient_regularEpi (a b : Idem V) :
    IsRegularEpi ((F).map (EffectiveFork.imageQuotient (ForkDerivation.conclusion a b))) :=
  (RegularEquivalence.regularEpi_iff ForkDerivation.Diagram.equivalence _).mpr
    (inferInstance : IsRegularEpi (EffectiveFork.imageQuotient (ForkDerivation.conclusion a b)))

theorem realized_image_factorization (a b : Idem V) :
    (F).map (EffectiveFork.imageQuotient (ForkDerivation.conclusion a b)) ≫
      theoremInclusion a b = conclusion a b := by
  exact (CategoryTheory.Functor.map_comp (F) _ _).symm.trans
    ((congrArg (fun f => (F).map f)
      (EffectiveFork.image_factorization (ForkDerivation.conclusion a b))).trans
        (conclusion_realization a b).symm)

/-- Equivalence preserves the actual regular-epi/mono factorization.
No stronger hypothesis on arbitrary epimorphisms is needed. -/
def imageIso (a b : Idem V) : image (conclusion a b) ≅ theoremObject a b :=
  (image.isoStrongEpiMono
    ((F).map (EffectiveFork.imageQuotient (ForkDerivation.conclusion a b)))
    (theoremInclusion a b) (realized_image_factorization a b)).symm

@[reassoc] theorem imageIso_hom_inclusion (a b : Idem V) :
    (imageIso a b).hom ≫ theoremInclusion a b = image.ι (conclusion a b) :=
  image.isoStrongEpiMono_inv_comp_mono _ _ (realized_image_factorization a b)

@[reassoc] theorem imageIso_inv_image (a b : Idem V) :
    (imageIso a b).inv ≫ image.ι (conclusion a b) = theoremInclusion a b :=
  image.isoStrongEpiMono_hom_comp_ι _ _ (realized_image_factorization a b)

/-- The two literal numerical subfunctors coincide as subobjects of the
actual realized formula diagram. The inclusion triangle is proved above. -/
theorem theoremSubobject_eq_realizedImage (a b : Idem V) :
    theoremSubobject a b = Subobject.mk (theoremInclusion a b) :=
  Subobject.mk_eq_mk_of_comm _ _ (imageIso a b) (imageIso_hom_inclusion a b)

/-- The realized old image is the literal diagram of the existing t0
domain, with the original component theorem sets. -/
theorem theoremObject_eq_t0_domain (a b : Idem V) :
    theoremObject a b =
      (F).obj (⟨EffectiveFork.domainObject (ForkSyntax.t0 a b)⟩ : EffectiveFork.Total) := rfl

theorem theoremInclusion_eq_t0_domain (a b : Idem V) :
    theoremInclusion a b = (F).map
      (⟨EffectiveFork.domainInclusion (ForkSyntax.t0 a b),
        EffectiveFork.domainInclusion_total (ForkSyntax.t0 a b)⟩ :
        (⟨EffectiveFork.domainObject (ForkSyntax.t0 a b)⟩ : EffectiveFork.Total) ⟶
          ForkDerivation.sentenceObject) := rfl

/-- The actual literal-diagram initiality supplies Theorem A.5, for
arbitrary monic numerical subfunctors and their natural rule operations. -/
theorem least_theorem_image (a b : Idem V) :
    ClosedUnder (ForkDerivation.Diagram.rules a b).inference
        (image.ι (conclusion a b)) ∧
      ∀ {U : D} (m : U ⟶ LS) [Mono m],
        ClosedUnder (ForkDerivation.Diagram.rules a b).inference m →
          ∃ w : image (conclusion a b) ⟶ U,
            w ≫ m = image.ι (conclusion a b) :=
  (ForkDerivation.Diagram.rules a b).least_theorem_subobject
    (ForkDerivation.Diagram.inferenceAlgebra a b)
    (ForkDerivation.Diagram.inferenceInitial a b)

theorem theoremSubobject_isLeast (a b : Idem V) :
    IsLeast {P : Subobject LS |
      ClosedUnder (ForkDerivation.Diagram.rules a b).inference P.arrow}
      (theoremSubobject a b) := by
  have h := least_theorem_image a b
  constructor
  · exact closed_of_iso _ _ _ (imageSubobjectIso (conclusion a b)).symm
      (imageSubobject_arrow' (conclusion a b)) h.1
  · intro P hP
    obtain ⟨w,hw⟩ := h.2 P.arrow hP
    apply Subobject.le_of_comm ((imageSubobjectIso (conclusion a b)).hom ≫ w)
    rw [Category.assoc,hw,imageSubobject_arrow]

theorem theoremInclusion_least (a b : Idem V) :
    ClosedUnder (ForkDerivation.Diagram.rules a b).inference (theoremInclusion a b) ∧
      ∀ {U : D} (m : U ⟶ LS) [Mono m],
        ClosedUnder (ForkDerivation.Diagram.rules a b).inference m →
          ∃ w : theoremObject a b ⟶ U, w ≫ m = theoremInclusion a b := by
  have h := least_theorem_image a b
  constructor
  · exact closed_of_iso _ _ _ (imageIso a b) (imageIso_hom_inclusion a b) h.1
  · intro U m _ hm
    obtain ⟨w,hw⟩ := h.2 m hm
    refine ⟨(imageIso a b).inv ≫ w,?_⟩
    rw [Category.assoc,hw]
    exact imageIso_inv_image a b

private def shapedRuleIso (a b : Idem V) :
    (ForkDerivation.Diagram.rules a b).inference ≅ ForkDerivation.Diagram.shapedH a b :=
  ForkInference.inferenceIso (ForkDerivation.Diagram.lambda a b)
    ForkDerivation.Diagram.implication ≪≫ ForkDerivation.Diagram.shapedInferenceIso a b

/-- The displayed Fin5 axiom shape and the inference signature have the
same closed subobjects, by the constructed constructor-preserving iso. -/
theorem closed_shaped_iff (a b : Idem V) {U : D} (m : U ⟶ LS) :
    ClosedUnder (ForkDerivation.Diagram.rules a b).inference m ↔
      ClosedUnder (ForkDerivation.Diagram.shapedH a b) m := by
  constructor
  · rintro ⟨α⟩
    exact ⟨(shapedRuleIso a b).inv.app (Over.mk m) ≫ α⟩
  · rintro ⟨α⟩
    exact ⟨(shapedRuleIso a b).hom.app (Over.mk m) ≫ α⟩

/-- Leastness for the actual printed H on literal numerical diagrams. -/
theorem shaped_least_theorem_image (a b : Idem V) :
    ClosedUnder (ForkDerivation.Diagram.shapedH a b) (image.ι (conclusion a b)) ∧
      ∀ {U : D} (m : U ⟶ LS) [Mono m],
        ClosedUnder (ForkDerivation.Diagram.shapedH a b) m →
          ∃ w : image (conclusion a b) ⟶ U,
            w ≫ m = image.ι (conclusion a b) := by
  have h := least_theorem_image a b
  refine ⟨(closed_shaped_iff a b _).mp h.1,?_⟩
  intro U m _ hm
  exact h.2 m ((closed_shaped_iff a b m).mpr hm)

theorem shaped_theoremSubobject_isLeast (a b : Idem V) :
    IsLeast {P : Subobject LS |
      ClosedUnder (ForkDerivation.Diagram.shapedH a b) P.arrow}
      (theoremSubobject a b) := by
  have h := shaped_least_theorem_image a b
  constructor
  · exact closed_of_iso _ _ _ (imageSubobjectIso (conclusion a b)).symm
      (imageSubobject_arrow' (conclusion a b)) h.1
  · intro P hP
    obtain ⟨w,hw⟩ := h.2 P.arrow hP
    apply Subobject.le_of_comm ((imageSubobjectIso (conclusion a b)).hom ≫ w)
    rw [Category.assoc,hw,imageSubobject_arrow]

theorem shaped_theoremInclusion_least (a b : Idem V) :
    ClosedUnder (ForkDerivation.Diagram.shapedH a b) (theoremInclusion a b) ∧
      ∀ {U : D} (m : U ⟶ LS) [Mono m],
        ClosedUnder (ForkDerivation.Diagram.shapedH a b) m →
          ∃ w : theoremObject a b ⟶ U, w ≫ m = theoremInclusion a b := by
  have h := shaped_least_theorem_image a b
  constructor
  · exact closed_of_iso _ _ _ (imageIso a b) (imageIso_hom_inclusion a b) h.1
  · intro U m _ hm
    obtain ⟨w,hw⟩ := h.2 m hm
    refine ⟨(imageIso a b).inv ≫ w,?_⟩
    rw [Category.assoc,hw]
    exact imageIso_inv_image a b

end LiteralDiagram

end CategoricalEssentialIncompleteness.V46.ForkDerivationImages
