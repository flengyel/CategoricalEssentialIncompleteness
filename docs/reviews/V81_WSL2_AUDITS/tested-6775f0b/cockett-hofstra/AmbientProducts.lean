module

public import CategoricalEssentialIncompleteness.V46ComputablePowerInclusion

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.V46.ApplicativeSystem

namespace IndependentPCAReading

universe v u

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : PCategoryStruct.nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

/-- The source W is arbitrary, and the two morphisms may have different domains. -/
theorem partial_pairing_in_base (unit : IsRestrictionTerminal t) (X Y : Powers app t)
    {W : C} (f : W ⟶ (inclusion app t).obj X) (g : W ⟶ (inclusion app t).obj Y) :
    let F := inclusion app t
    let D := products app t unit
    ∃! h : W ⟶ F.obj (D.prod X Y),
      h ≫ F.map (D.fst X Y) = rst g ≫ f ∧
      h ≫ F.map (D.snd X Y) = rst f ≫ g ∧ rst h = rst f ≫ rst g := by
  dsimp only
  have same : rst (rst g ≫ f) = rst (rst f ≫ g) := by
    rw [rst_comp_rst, rst_comp_rst, rst_comm]
  obtain ⟨h, ⟨hf, hg⟩, unique⟩ :=
    inclusion_product app t unit X Y (rst g ≫ f) (rst f ≫ g) same
  have total : isTotal ((inclusion app t).map ((products app t unit).fst X Y)) :=
    congrArg Subtype.val ((products app t unit).fst_total X Y)
  refine ⟨h, ⟨hf, hg, ?_⟩, fun other prop => unique other ⟨prop.1, prop.2.1⟩⟩
  rw [← rst_comp_of_isTotal h total, hf, rst_comp_rst, rst_comm]

/-- The canonical comparison into the ambient binary restriction product is invertible. -/
theorem canonical_product_iso (unit : IsRestrictionTerminal t) (X Y : Powers app t) :
    let F := inclusion app t
    let D := products app t unit
    IsIso (PCategoryStruct.partialPairing (F.map (D.fst X Y)) (F.map (D.snd X Y))) := by
  let F := inclusion app t
  let D := products app t unit
  let p := F.map (D.fst X Y)
  let q := F.map (D.snd X Y)
  let c := PCategoryStruct.partialPairing p q
  have ptotal : isTotal p := congrArg Subtype.val (D.fst_total X Y)
  have qtotal : isTotal q := congrArg Subtype.val (D.snd_total X Y)
  have cp : c ≫ PCategoryStruct.p0 _ _ = p := PCategory.p0_partialPairing_of_isTotal _ qtotal
  have cq : c ≫ PCategoryStruct.p1 _ _ = q := PCategory.p1_partialPairing_of_isTotal _ ptotal
  have hdom : rst (PCategoryStruct.p0 (F.obj X) (F.obj Y)) =
      rst (PCategoryStruct.p1 (F.obj X) (F.obj Y)) :=
    (PCategory.p0_isTotal _ _).trans (PCategory.p1_isTotal _ _).symm
  obtain ⟨s, ⟨s₁, s₂⟩, _⟩ := inclusion_product app t unit X Y _ _ hdom
  change s ≫ p = _ at s₁
  change s ≫ q = _ at s₂
  change IsIso c
  refine ⟨⟨s, ?_, ?_⟩⟩
  · have comparison := inclusion_product app t unit X Y p q (ptotal.trans qtotal.symm)
    apply comparison.unique
    · exact ⟨by rw [Category.assoc, s₁, cp], by rw [Category.assoc, s₂, cq]⟩
    · exact ⟨Category.id_comp p, Category.id_comp q⟩
  · apply product_hom_ext
    · rw [Category.assoc, cp, s₁, Category.id_comp]
    · rw [Category.assoc, cq, s₂, Category.id_comp]

/-- Inclusion takes the empty formal power and the chosen terminal morphism to the given ones. -/
theorem inclusion_terminal (X : Powers app t) :
    (inclusion app t).obj (formal app t 0) = Z ∧
      (inclusion app t).map (terminate app t X) = t ((inclusion app t).obj X) :=
  ⟨rfl, rfl⟩

#print axioms partial_pairing_in_base
#print axioms canonical_product_iso
#print axioms inclusion_terminal

end IndependentPCAReading
