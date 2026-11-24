module

public import CategoricalEssentialIncompleteness.V46TuringComputablePowers
public import CategoricalEssentialIncompleteness.V46ComputableTuringCategory
public import CategoricalEssentialIncompleteness.V46ComputablePowerRestriction

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Idempotents CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.V46

namespace IndependentPCAReading

universe v w u z

section Codes

open PCategoryStruct RecursionCategory ApplicativeSystem

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

theorem code_with_prefix (n : ℕ) (p : Z ⟶ A) (f : power Z A (n+2) ⟶ A) :
    Codes app t p (n+2) f ↔ isTotal p ∧ isTotal (applyPositive app t p n) ∧
      applyPositive app t p (n+1) = f := Iff.rfl

theorem positive_input_domain_iff (n : ℕ) (f : power Z A (n+1) ⟶ Z) :
    Computable app t (n+1) 0 f ↔ Computable app t (n+1) (n+1) (PCategoryStruct.rst f) :=
  Iff.rfl

theorem scalar_iff (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (e : Z ⟶ Z) :
    Computable app t 0 0 e ↔ ∃ p : Z ⟶ A, isTotal p ∧
      e = PCategoryStruct.rst (p ≫ diag A ≫ app) := by
  have tid : t Z = 𝟙 Z := by
    simpa only [PCategory.rst_id, Category.id_comp] using (unit (𝟙 Z)).symm
  have scalar : e = PCategoryStruct.rst e := by
    simpa only [tid, Category.comp_id] using unit e
  constructor
  · rintro ⟨g, dom, p, hp, rfl⟩
    exact ⟨p, hp, scalar.trans dom⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p ≫ diag A ≫ app, scalar.symm.trans h, p, hp, rfl⟩

theorem pca_iff_all_polynomials
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X) :
    CombinatoriallyComplete app t ↔
      ∀ (n m : ℕ) (f : power Z A n ⟶ power Z A m), Polynomial app t n m f →
        Computable app t n m f := by
  constructor
  · intro h n m f hf
    exact (polynomial_iff_computable app t h unit n m f).mp hf
  · intro all n f hf
    exact all n 1 f hf

theorem pca_turing_object (unit : IsRestrictionTerminal t) (complete : CombinatoriallyComplete app t) :
    let D := products app t unit
    letI : PCategoryStruct (Powers app t) := D.pcategoryStruct
    letI : PCategory (Powers app t) := D.pcategoryLaws
    IsTuringMorphism (W := formal app t 1) (X := formal app t 1) (Y := formal app t 1)
        (application app t unit) ∧
      ∀ X Y : Powers app t, ∃ a : nearProd (formal app t 1) X ⟶ Y, IsTuringMorphism a :=
  structure_of_pca app t unit complete

theorem representation_from_turing_object
    (typed : ∀ X Y : C, ∃ a : nearProd A X ⟶ Y, IsTuringMorphism a)
    (designated : IsTuringMorphism app) (ht : ∀ X, isTotal (t X))
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X) :
    CombinatoriallyComplete app t ∧
      (∀ (n m : ℕ) (f : power Z A n ⟶ power Z A m), Computable app t n m f) ∧
      ∃ E : ObjectProperty (Karoubi (Powers app t)),
        (∀ X : Powers app t, E ((toKaroubi _).obj X)) ∧
        Nonempty (C ≌ E.FullSubcategory) := by
  apply structure_of_turing app t designated (ht A) unit
  intro X
  obtain ⟨i, r, _, eqn⟩ := ((turingObject_iff A).mp typed).2 X
  exact ⟨i, r, eqn⟩

end Codes

section Restrictions

open IdempotentSplitting

variable {B : Type u} {C : Type z} [Category.{v} B] [Category.{w} C]
  [RestrictionCategory B] [RestrictionCategory C] (F : B ⥤ C)

def splitDomain {P Q : Karoubi B} (f : P ⟶ Q) : P ⟶ P :=
  ⟨P.p ≫ rst f.f, by
    have comm := rst_comp P.p f.f
    rw [Karoubi.p_comp] at comm
    simp only [← Category.assoc, P.idem]
    rw [Category.assoc, comm, ← Category.assoc, P.idem]⟩

theorem realization_preserves
    (hF : ∀ {U V : B} (g : U ⟶ V), F.map (rst g) = rst (F.map g))
    {P Q : (splitsIn F).FullSubcategory} (f : P ⟶ Q) :
    (realization F).map (ObjectProperty.homMk (splitDomain f.hom)) = rst ((realization F).map f) := by
  let p := splitting F P
  let q := splitting F Q
  have qtotal : isTotal q.i := by
    change rst q.i = 𝟙 _
    have h := congrArg (fun k => k ≫ q.r) (rst_comp_self q.i)
    simpa only [Category.assoc, q.section_retraction, Category.comp_id] using h
  have source : p.i ≫ F.map P.obj.p = p.i := by
    rw [← p.factor, ← Category.assoc, p.section_retraction, Category.id_comp]
  have last : (p.i ≫ F.map f.hom.f ≫ q.r) ≫ q.i = p.i ≫ F.map f.hom.f := by
    simp only [Category.assoc, q.factor, ← F.map_comp, Karoubi.comp_p]
  have r4 := congrArg (fun k => k ≫ p.r) (rst_comp p.i (F.map f.hom.f))
  change p.i ≫ F.map (P.obj.p ≫ rst f.hom.f) ≫ p.r = rst (p.i ≫ F.map f.hom.f ≫ q.r)
  calc
    _ = (p.i ≫ F.map (rst f.hom.f)) ≫ p.r := by
      rw [F.map_comp]
      simp only [← Category.assoc, source]
    _ = rst (p.i ≫ F.map f.hom.f) := by
      rw [hF]
      simpa only [Category.assoc, p.section_retraction, Category.comp_id] using r4.symm
    _ = rst ((p.i ≫ F.map f.hom.f ≫ q.r) ≫ q.i) := by rw [last]
    _ = _ := rst_comp_of_isTotal _ qtotal

end Restrictions

open PCategoryStruct ApplicativeSystem

theorem comparison_preserves {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)
    {P Q : (IdempotentSplitting.splitsIn (inclusion app t)).FullSubcategory} (f : P ⟶ Q) :
    (IdempotentSplitting.realization (inclusion app t)).map
        (ObjectProperty.homMk (splitDomain f.hom)) =
      CategoryTheory.RestrictionCategory.rst
        ((IdempotentSplitting.realization (inclusion app t)).map f) :=
  realization_preserves (inclusion app t) (fun _ => rfl) f

theorem representation_preserves {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)
    (universal : RecursionCategory.IsTuringMorphism app) (ht : isTotal (t A))
    (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (retracts : ∀ X : C, ∃ (i : X ⟶ A) (r : A ⟶ X), i ≫ r = 𝟙 X)
    {X Y : C} (f : X ⟶ Y) :
    (representation app t universal ht unit retracts).functor.map (RestrictionCategory.rst f) =
      RestrictionCategory.rst ((representation app t universal ht unit retracts).functor.map f) := by
  apply CategoricalEssentialIncompleteness.LocalConnectedness.V46.equivalence_inverse_preserves
      (representation app t universal ht unit retracts).symm _ f
  intro P Q g
  exact comparison_preserves app t g

#print axioms code_with_prefix
#print axioms positive_input_domain_iff
#print axioms scalar_iff
#print axioms pca_iff_all_polynomials
#print axioms pca_turing_object
#print axioms representation_from_turing_object
#print axioms realization_preserves
#print axioms comparison_preserves
#print axioms representation_preserves

end IndependentPCAReading
