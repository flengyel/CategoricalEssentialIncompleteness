/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LaxPolynomialComparison
public import CategoricalEssentialIncompleteness.V46RegularSlices
public import CategoricalEssentialIncompleteness.V46SliceBaseChangeGeometry
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Extensive

/-! # Change of base for polynomials in finitely many sorts -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe w v v' u u'
namespace CategoricalEssentialIncompleteness.V46.FiniteSorts

/-- One output expression in the variable sorts and labelled constants of Appendix A.1. -/
inductive Expression (r : ℕ) (I : Type w) where
  | variableSort (i : Fin r)
  | coefficient (i : I)
  | unit
  | zero
  | product (p q : Expression r I)
  | sum (p q : Expression r I)

variable {r : ℕ} {I : Type w} {C : Type u} [Category.{v} C]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]

def eval (c : I → C) : Expression r I → (Fin r → C) ⥤ C
  | .variableSort i => Pi.eval (fun _ => C) i
  | .coefficient i => (Functor.const _).obj (c i)
  | .unit => (Functor.const _).obj (⊤_ C)
  | .zero => (Functor.const _).obj (⊥_ C)
  | .product p q => {
      obj := fun X => (eval c p).obj X ⨯ (eval c q).obj X
      map := fun f => prod.map ((eval c p).map f) ((eval c q).map f)
      map_id := fun _ => by simp
      map_comp := fun f g => by simp only [Functor.map_comp, prod.map_map] }
  | .sum p q => {
      obj := fun X => (eval c p).obj X ⨿ (eval c q).obj X
      map := fun f => coprod.map ((eval c p).map f) ((eval c q).map f)
      map_id := fun _ => by simp
      map_comp := fun f g => by simp only [Functor.map_comp, coprod.map_map] }

def polynomial (c : I → C) (K : Fin r → Expression r I) : (Fin r → C) ⥤ (Fin r → C) :=
  Functor.pi' (fun i => eval c (K i))

variable {D : Type u'} [Category.{v'} D] [HasFiniteProducts D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [PreservesFiniteProducts F] [PreservesFiniteCoproducts F]

def component (c : I → C) (X : Fin r → C) (p : Expression r I) :
    F.obj ((eval c p).obj X) ≅ (eval (F.obj ∘ c) p).obj (F.obj ∘ X) :=
  match p with
  | .variableSort _ => Iso.refl _
  | .coefficient _ => Iso.refl _
  | .unit => asIso (terminalComparison F)
  | .zero => (asIso (initialComparison F)).symm
  | .product p q => asIso (prodComparison F _ _) ≪≫
      prod.mapIso (component c X p) (component c X q)
  | .sum p q => (asIso (coprodComparison F _ _)).symm ≪≫
      coprod.mapIso (component c X p) (component c X q)

theorem naturality (c : I → C) (p : Expression r I) {X Y : Fin r → C} (f : X ⟶ Y) :
    F.map ((eval c p).map f) ≫ (component F c Y p).hom =
      (component F c X p).hom ≫ (eval (F.obj ∘ c) p).map (fun i => F.map (f i)) := by
  induction p with
  | variableSort i => simp [eval, component]
  | coefficient i => simp [eval, component]
  | unit => simp [eval, component]
  | zero => simp [eval, component]
  | product p q hp hq =>
    change F.map (prod.map _ _) ≫ (prodComparison F _ _ ≫ prod.map _ _) =
      (prodComparison F _ _ ≫ prod.map _ _) ≫ prod.map _ _
    rw [← Category.assoc, prodComparison_natural, Category.assoc, prod.map_map, hp, hq]
    simp only [Category.assoc, prod.map_map]
  | sum p q hp hq =>
    change F.map (coprod.map _ _) ≫ (inv (coprodComparison F _ _) ≫ coprod.map _ _) =
      (inv (coprodComparison F _ _) ≫ coprod.map _ _) ≫ coprod.map _ _
    apply (cancel_epi (coprodComparison F _ _)).mp
    rw [← Category.assoc, coprodComparison_natural]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, coprod.map_map]
    rw [hp, hq]

/-- The natural comparison uses every input coordinate and every output sort. -/
def comparison (c : I → C) (K : Fin r → Expression r I) :
    Functor.pi (fun _ : Fin r => F) ⋙ polynomial (F.obj ∘ c) K ≅
      polynomial c K ⋙ Functor.pi (fun _ : Fin r => F) := by
  symm
  apply NatIso.pi'
  intro i
  exact NatIso.ofComponents (fun X => component F c X (K i)) (fun f => naturality F c (K i) f)

section Slice
variable {E : Type u} [Category.{v} E] [Regular E] [FinitaryExtensive E]

omit [FinitaryExtensive E] in
theorem product_square (P : E) {X Y : E} (f : X ⟶ Y) :
    IsPullback (prod.map (𝟙 P) f) prod.snd (prod.snd : P ⨯ Y ⟶ Y) f := by
  apply IsPullback.mk' (by simp)
  · intro R a b h₁ h₂
    apply prod.hom_ext
    · simpa using congrArg (fun k => k ≫ prod.fst) h₁
    · exact h₂
  · intro R a b h
    refine ⟨prod.lift (a ≫ prod.fst) b, ?_, by simp⟩
    apply prod.hom_ext
    · simp
    · simpa using h.symm

/-- Each finite coproduct cocone remains colimiting after taking constant families. -/
theorem constant_preservesFiniteCoproducts (P : E) :
    PreservesFiniteCoproducts (constantFamilyFunctor P) where
  preserves J := by
    constructor
    intro K
    constructor
    intro c hc
    let B := constantFamilyFunctor P ⋙ Over.forget P
    let π : K ⋙ B ⟶ K := { app := fun j => prod.snd
                           naturality := fun _ _ f => prod.map_snd _ _ }
    apply Nonempty.intro
    apply isColimitOfReflects (Over.forget P)
    exact (FinitaryPreExtensive.isUniversal_finiteCoproducts hc (B.mapCocone c) π prod.snd
      (by ext j; exact (prod.map_snd _ _).symm) (fun {i j} f => product_square P (K.map f))
      (fun j => product_square P (c.ι.app j))).some

/-- Change of base to the slice over any parameter in Appendix A.1. -/
def sliceComparison (P : E) (c : I → E) (K : Fin r → Expression r I) :
    Functor.pi (fun _ : Fin r => constantFamilyFunctor P) ⋙ polynomial ((constantFamily P) ∘ c) K ≅
      polynomial c K ⋙ Functor.pi (fun _ : Fin r => constantFamilyFunctor P) := by
  let : PreservesFiniteLimits (constantFamilyFunctor P) :=
    SliceBaseChangeGeometry.constant_preservesFiniteLimits P
  let : PreservesFiniteCoproducts (constantFamilyFunctor P) := constant_preservesFiniteCoproducts P
  exact comparison (constantFamilyFunctor P) c K

end Slice
end CategoricalEssentialIncompleteness.V46.FiniteSorts
