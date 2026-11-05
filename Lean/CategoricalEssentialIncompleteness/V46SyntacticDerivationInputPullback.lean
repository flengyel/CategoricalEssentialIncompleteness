import CategoricalEssentialIncompleteness.V46SyntacticDerivationRules

/-! The positive literal matching carrier has the actual pullback universal property. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.RuleInput
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {A B F : Carrier}
variable (p : GraphMorphism T A F) (q : GraphMorphism T B F)

/-- A matching input is an actual subobject of the literal ordered product. -/
theorem toProductProof : T ⊢ inclusionSentence (carrier p q) (productCarrier A B) := by
  apply complete.{0} T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  rw [models_iff, inclusionSentence_eval]
  intro u hu
  obtain ⟨hA, hB, _⟩ := carrier_components p q u hu
  exact (productCarrier_eval A B u).mpr
    ⟨π₁ u, π₂ u, (pair_unpair u).symm, hA, hB⟩

def toProduct : @Quiver.Hom (PredicateCategory T) inferInstance
    (carrier p q) (productCarrier A B) :=
  representedArrow T (GraphMorphism.inclusion (toProductProof p q))

instance toProduct_mono : Mono (toProduct p q) := by
  dsimp [toProduct]
  infer_instance

@[simp, reassoc] theorem toProduct_label :
    toProduct p q ≫ representedArrow T (productFst T A B) =
      representedArrow T (label p q) := by
  apply hom_ext T
  intro M _ hM u r
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  simp only [toProduct, relation_comp, relation_class, productFst_eval,
    GraphMorphism.inclusion, GraphMorphism.identityGraph_eval]
  change (∃ v : M, ((carrier p q).val.Evalb ![u] ∧ v = u) ∧
      ∃ d : M, v = Arithmetic.pair r d ∧ A.val.Evalb ![r] ∧ B.val.Evalb ![d]) ↔
    (labelGraph p q).val.Evalb ![u, r]
  rw [labelGraph_eval]
  constructor
  · rintro ⟨v, ⟨hu, rfl⟩, d, he, _, _⟩
    exact ⟨hu, by simp only [he, pi₁_pair]⟩
  · rintro ⟨hu, rfl⟩
    obtain ⟨hA, hB, _⟩ := carrier_components p q u hu
    exact ⟨u, ⟨hu, rfl⟩, π₂ u, (pair_unpair u).symm, hA, hB⟩

@[simp, reassoc] theorem toProduct_children :
    toProduct p q ≫ representedArrow T (productSnd T A B) =
      representedArrow T (children p q) := by
  apply hom_ext T
  intro M _ hM u d
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  simp only [toProduct, relation_comp, relation_class, productSnd_eval,
    GraphMorphism.inclusion, GraphMorphism.identityGraph_eval]
  change (∃ v : M, ((carrier p q).val.Evalb ![u] ∧ v = u) ∧
      ∃ r : M, v = Arithmetic.pair r d ∧ A.val.Evalb ![r] ∧ B.val.Evalb ![d]) ↔
    (childrenGraph p q).val.Evalb ![u, d]
  rw [childrenGraph_eval]
  constructor
  · rintro ⟨v, ⟨hu, rfl⟩, r, he, _, _⟩
    exact ⟨hu, by simp only [he, pi₂_pair]⟩
  · rintro ⟨hu, rfl⟩
    obtain ⟨hA, hB, _⟩ := carrier_components p q u hu
    exact ⟨u, ⟨hu, rfl⟩, π₁ u, (pair_unpair u).symm, hA, hB⟩

/-- Both projections jointly determine a morphism into the literal matching carrier. -/
theorem hom_ext {X : PredicateCategory T} (f g : X ⟶ (carrier p q : PredicateCategory T))
    (h₁ : f ≫ representedArrow T (label p q) = g ≫ representedArrow T (label p q))
    (h₂ : f ≫ representedArrow T (children p q) = g ≫ representedArrow T (children p q)) :
    f = g := by
  apply (cancel_mono (toProduct p q)).mp
  apply BinaryFan.IsLimit.hom_ext (productIsLimit T A B)
  · change (f ≫ toProduct p q) ≫ representedArrow T (productFst T A B) =
      (g ≫ toProduct p q) ≫ representedArrow T (productFst T A B)
    calc
      _ = f ≫ representedArrow T (label p q) := by
        simpa only [Category.assoc] using congrArg (fun k => f ≫ k) (toProduct_label p q)
      _ = g ≫ representedArrow T (label p q) := h₁
      _ = _ := by
        simpa only [Category.assoc] using
          (congrArg (fun k => g ≫ k) (toProduct_label p q)).symm
  · change (f ≫ toProduct p q) ≫ representedArrow T (productSnd T A B) =
      (g ≫ toProduct p q) ≫ representedArrow T (productSnd T A B)
    calc
      _ = f ≫ representedArrow T (children p q) := by
        simpa only [Category.assoc] using congrArg (fun k => f ≫ k) (toProduct_children p q)
      _ = g ≫ representedArrow T (children p q) := h₂
      _ = _ := by
        simpa only [Category.assoc] using
          (congrArg (fun k => g ≫ k) (toProduct_children p q)).symm

variable {X : PredicateCategory T} (a : X ⟶ (A : PredicateCategory T))
variable (b : X ⟶ (B : PredicateCategory T))
variable (h : a ≫ representedArrow T p = b ≫ representedArrow T q)

include h in
/-- The existing actual product lift already has the positive matching
property whenever its two legs satisfy the given square. -/
theorem lift_support : T ⊢ supportSentence X (carrier p q) (productLift T a b).graph := by
  apply complete.{0} T
  intro M _ hM
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  rw [models_iff, supportSentence_eval]
  intro x u hxu
  obtain ⟨r, d, har, hbd, rfl⟩ := (productLift_eval T a b M x u).mp hxu
  have hr := (relation_support T a M x r har).2
  obtain ⟨z, hpz, _⟩ := p.total_model M r hr
  have hleft : relation T (a ≫ representedArrow T p) M x z :=
    (relation_comp T a _ M x z).mpr
      ⟨r, har, (relation_class T p M r z).mpr hpz⟩
  rw [h] at hleft
  obtain ⟨d', hbd', hqz⟩ := (relation_comp T b _ M x z).mp hleft
  have hd' := relation_functional T b M x d' d hbd' hbd
  subst d'
  exact ⟨(relation_support T a M x r har).1,
    (carrier_pair p q r d).mpr ⟨z, hpz, (relation_class T q M d z).mp hqz⟩⟩

/-- This is the actual product-lift graph with its proved matching codomain. -/
def lift : GraphMorphism T X (carrier p q) where
  graph := (productLift T a b).graph
  support := lift_support p q a b h
  total := (productLift T a b).total

@[simp, reassoc] theorem lift_toProduct :
    representedArrow T (lift p q a b h) ≫ toProduct p q =
      representedArrow T (productLift T a b) := by
  apply SyntacticPredicates.hom_ext T
  intro M _ hM x u
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) hM
  simp only [toProduct, relation_comp, relation_class,
    GraphMorphism.inclusion, GraphMorphism.identityGraph_eval]
  change (∃ v : M, (productLift T a b).graph.val.Evalb ![x, v] ∧
      (carrier p q).val.Evalb ![v] ∧ u = v) ↔ (productLift T a b).graph.val.Evalb ![x, u]
  constructor
  · rintro ⟨v, hv, _, rfl⟩
    exact hv
  · intro hu
    exact ⟨u, hu, ((lift p q a b h).support_model M x u hu).2, rfl⟩

@[simp, reassoc] theorem lift_label :
    representedArrow T (lift p q a b h) ≫ representedArrow T (label p q) = a := by
  rw [← toProduct_label, ← Category.assoc, lift_toProduct]
  exact productLift_fst T a b

@[simp, reassoc] theorem lift_children :
    representedArrow T (lift p q a b h) ≫ representedArrow T (children p q) = b := by
  rw [← toProduct_children, ← Category.assoc, lift_toProduct]
  exact productLift_snd T a b

/-- The literal positive matching carrier presents the actual categorical
pullback of the two supplied graph morphisms. -/
theorem isPullback :
    IsPullback (representedArrow T (label p q)) (representedArrow T (children p q))
      (representedArrow T p) (representedArrow T q) := by
  refine IsPullback.mk' (square p q) ?_ ?_
  · intro X u v hu hv
    exact hom_ext p q u v hu hv
  · intro X a b h
    exact ⟨representedArrow T (lift p q a b h), lift_label p q a b h,
      lift_children p q a b h⟩

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.RuleInput
