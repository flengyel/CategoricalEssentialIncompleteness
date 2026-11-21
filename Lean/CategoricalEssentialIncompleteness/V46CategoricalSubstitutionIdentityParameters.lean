/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! Parameter change for the syntax folds. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

namespace SyntaxParameterChange

variable {P Q : D} (r : P ⟶ Q)

/-- A constant family map whose parameter coordinate changes by `r`. -/
def baseMap (X : D) : (Over.map r).obj (constantFamily P X) ⟶ constantFamily Q X :=
  Over.homMk (prod.map r (𝟙 X)) (by simp [constantFamily, Over.map])

omit [FinitaryExtensive D] in
theorem baseMap_natural {X Y : D} (f : X ⟶ Y) :
    baseMap r X ≫ (constantFamilyFunctor Q).map f =
      (Over.map r).map ((constantFamilyFunctor P).map f) ≫ baseMap r Y := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;> simp [baseMap, constantFamilyFunctor, Over.map]

def baseTransformation : constantFamilyFunctor P ⋙ Over.map r ⟶ constantFamilyFunctor Q where
  app := baseMap r
  naturality := by
    intro X Y f
    exact (baseMap_natural r f).symm

omit [Regular D] in
@[simp, reassoc] theorem map_inl_desc {X Y Z : Over P} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (Over.map r).map coprod.inl ≫ (Over.map r).map (coprod.desc f g) =
      (Over.map r).map f := by
  rw [← (Over.map r).map_comp, coprod.inl_desc]

omit [Regular D] in
@[simp, reassoc] theorem map_inr_desc {X Y Z : Over P} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (Over.map r).map coprod.inr ≫ (Over.map r).map (coprod.desc f g) =
      (Over.map r).map g := by
  rw [← (Over.map r).map_comp, coprod.inr_desc]

omit [FinitaryExtensive D] in
theorem constant_map_head (R X Y : D) :
    parameterHom (prod.snd ≫ prod.fst : R ⨯ (X ⨯ Y) ⟶ X) =
      (constantFamilyFunctor R).map prod.fst := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;> simp [parameterHom, constantFamilyFunctor]

omit [FinitaryExtensive D] in
theorem constant_map_value (R X Y : D) :
    parameterHom (prod.snd ≫ prod.snd : R ⨯ (X ⨯ Y) ⟶ Y) =
      (constantFamilyFunctor R).map prod.snd := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext <;> simp [parameterHom, constantFamilyFunctor]

omit [FinitaryExtensive D] in
theorem constant_prodComparison (R X Y : D) :
    prodComparison (constantFamilyFunctor R) X Y = parameterStep R X Y := by
  unfold prodComparison parameterStep
  rw [constant_map_head, constant_map_value]
  rfl

instance constant_prodComparison_isIso (R X Y : D) :
    IsIso (prodComparison (constantFamilyFunctor R) X Y) := by
  rw [constant_prodComparison]
  infer_instance

omit [FinitaryExtensive D] in
theorem constant_comparison_prodComparison (R X Y : D) :
    constantProductComparison R X Y ≫ prodComparison (constantFamilyFunctor R) X Y = 𝟙 _ := by
  rw [constant_prodComparison]
  exact (parameterStepIso R X Y).inv_hom_id

omit [FinitaryExtensive D] in
theorem baseMap_product (X Y : D) :
    prodComparison (Over.map r) (constantFamily P X) (constantFamily P Y) ≫
        prod.map (baseMap r X) (baseMap r Y) ≫ constantProductComparison Q X Y =
      (Over.map r).map (constantProductComparison P X Y) ≫ baseMap r (X ⨯ Y) := by
  apply (cancel_mono (prodComparison (constantFamilyFunctor Q) X Y)).mp
  rw [Category.assoc, Category.assoc, constant_comparison_prodComparison, Category.comp_id]
  have hn := prodComparison_natural_of_natTrans (baseTransformation r) (A := X) (B := Y)
  dsimp only [baseTransformation] at hn
  rw [Category.assoc, hn, prodComparison_comp]
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    constant_comparison_prodComparison]
  dsimp only [constantFamilyFunctor]
  rw [(Over.map r).map_id, Category.id_comp]

theorem baseMap_coproduct (X Y : D) :
    inv (coprodComparison (Over.map r) (constantFamily P X) (constantFamily P Y)) ≫
        coprod.map (baseMap r X) (baseMap r Y) ≫ constantCoproductComparison Q X Y =
      (Over.map r).map (constantCoproductComparison P X Y) ≫ baseMap r (X ⨿ Y) := by
  apply (cancel_epi (coprodComparison (Over.map r)
    (constantFamily P X) (constantFamily P Y))).mp
  rw [IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simpa only [coprod.inl_map_assoc, constantCoproductComparison, coprod.inl_desc,
      coprodComparison_inl_assoc, map_inl_desc_assoc] using
        baseMap_natural r (coprod.inl : X ⟶ X ⨿ Y)
  · simpa only [coprod.inr_map_assoc, constantCoproductComparison, coprod.inr_desc,
      coprodComparison_inr_assoc, map_inr_desc_assoc] using
        baseMap_natural r (coprod.inr : Y ⟶ X ⨿ Y)

omit [FinitaryExtensive D] in
theorem baseMap_unit :
    terminal.from ((Over.map r).obj (⊤_ (Over P))) ≫ constantUnitComparison Q =
      (Over.map r).map (constantUnitComparison P) ≫ baseMap r (⊤_ D) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · exact terminalIsTerminal.hom_ext _ _

/-- Polynomial action on a pair of maps over a changing parameter.
Postcomposition preserves sums; its product comparison needs no inverse. -/
def polynomialMap {A : Over P × Over P} {B : Over Q × Over Q}
    (f : ((Over.map r).obj A.1, (Over.map r).obj A.2) ⟶ B) :
    (p : SyntaxPolynomial D) →
      (Over.map r).obj ((p.withParameters P).eval.obj A) ⟶
        (p.withParameters Q).eval.obj B
  | .term => f.1
  | .formula => f.2
  | .coefficient X => baseMap r X
  | .unit => terminal.from _
  | .product p q =>
      prodComparison (Over.map r) _ _ ≫
        prod.map (polynomialMap f p) (polynomialMap f q)
  | .sum p q =>
      inv (coprodComparison (Over.map r) _ _) ≫
        coprod.map (polynomialMap f p) (polynomialMap f q)

@[simp, reassoc] theorem polynomialMap_inl {A : Over P × Over P} {B : Over Q × Over Q}
    (f : ((Over.map r).obj A.1, (Over.map r).obj A.2) ⟶ B) (p q : SyntaxPolynomial D) :
    (Over.map r).map (coprod.inl : (p.withParameters P).eval.obj A ⟶
      (p.withParameters P).eval.obj A ⨿ (q.withParameters P).eval.obj A) ≫
        polynomialMap r f (.sum p q) = polynomialMap r f p ≫ coprod.inl := by
  simp only [polynomialMap]
  rw [← Category.assoc, map_inl_inv_coprodComparison, coprod.inl_map]

@[simp, reassoc] theorem polynomialMap_inr {A : Over P × Over P} {B : Over Q × Over Q}
    (f : ((Over.map r).obj A.1, (Over.map r).obj A.2) ⟶ B) (p q : SyntaxPolynomial D) :
    (Over.map r).map (coprod.inr : (q.withParameters P).eval.obj A ⟶
      (p.withParameters P).eval.obj A ⨿ (q.withParameters P).eval.obj A) ≫
        polynomialMap r f (.sum p q) = polynomialMap r f q ≫ coprod.inr := by
  simp only [polynomialMap]
  rw [← Category.assoc, map_inr_inv_coprodComparison, coprod.inr_map]

theorem push_coprod_hom_ext {X Y : Over P} {Z : Over Q}
    {f g : (Over.map r).obj (X ⨿ Y) ⟶ Z}
    (hl : (Over.map r).map coprod.inl ≫ f = (Over.map r).map coprod.inl ≫ g)
    (hr : (Over.map r).map coprod.inr ≫ f = (Over.map r).map coprod.inr ≫ g) : f = g := by
  apply (cancel_epi (coprodComparison (Over.map r) X Y)).mp
  apply coprod.hom_ext
  · simpa only [coprodComparison_inl_assoc] using hl
  · simpa only [coprodComparison_inr_assoc] using hr

theorem polynomialMap_left {A A' : Over P × Over P} {B : Over Q × Over Q}
    (h : A ⟶ A') (f : ((Over.map r).obj A'.1, (Over.map r).obj A'.2) ⟶ B)
    (p : SyntaxPolynomial D) :
    (Over.map r).map ((p.withParameters P).eval.map h) ≫ polynomialMap r f p =
      polynomialMap r (((Over.map r).map h.1, (Over.map r).map h.2) ≫ f) p := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient X => simp [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, polynomialMap]
  | unit => simp [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, polynomialMap]
  | product p q hp hq =>
    change (Over.map r).map (prod.map _ _) ≫ (prodComparison _ _ _ ≫ prod.map _ _) = _
    rw [← Category.assoc, prodComparison_natural, Category.assoc, prod.map_map, hp, hq]
    rfl
  | sum p q hp hq =>
    change (Over.map r).map (coprod.map _ _) ≫ (inv (coprodComparison _ _ _) ≫
      coprod.map _ _) = _
    rw [← Category.assoc, ← coprodComparison_inv_natural, Category.assoc,
      coprod.map_map, hp, hq]
    rfl

theorem polynomialMap_right {A : Over P × Over P} {B B' : Over Q × Over Q}
    (f : ((Over.map r).obj A.1, (Over.map r).obj A.2) ⟶ B) (g : B ⟶ B')
    (p : SyntaxPolynomial D) :
    polynomialMap r f p ≫ (p.withParameters Q).eval.map g =
      polynomialMap r (f ≫ g) p := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient X => simp [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, polynomialMap]
  | unit => simp [SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, polynomialMap]
  | product p q hp hq =>
    change (prodComparison _ _ _ ≫ prod.map _ _) ≫ prod.map _ _ = _
    rw [Category.assoc, prod.map_map, hp, hq]
    rfl
  | sum p q hp hq =>
    change (inv (coprodComparison _ _ _) ≫ coprod.map _ _) ≫ coprod.map _ _ = _
    rw [Category.assoc, coprod.map_map, hp, hq]
    rfl

/-- The changing-parameter map is compatible with the concrete
constant-family polynomial comparisons used by the syntax structure. -/
theorem polynomialMap_comparison (X : D × D) (p : SyntaxPolynomial D) :
    polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫
        SyntaxPolynomial.parameterComparison Q X p =
      (Over.map r).map (SyntaxPolynomial.parameterComparison P X p) ≫
        baseMap r (p.eval.obj X) := by
  induction p with
  | term => simp [polynomialMap, SyntaxPolynomial.parameterComparison, SyntaxPolynomial.eval]
  | formula => simp [polynomialMap, SyntaxPolynomial.parameterComparison, SyntaxPolynomial.eval]
  | coefficient A =>
    simp [polynomialMap, SyntaxPolynomial.parameterComparison, SyntaxPolynomial.eval]
  | unit => exact baseMap_unit r
  | product p q hp hq =>
    change (prodComparison _ _ _ ≫
        prod.map (polynomialMap r (baseMap r X.1, baseMap r X.2) p)
          (polynomialMap r (baseMap r X.1, baseMap r X.2) q)) ≫
      (prod.map (SyntaxPolynomial.parameterComparison Q X p)
        (SyntaxPolynomial.parameterComparison Q X q) ≫
          constantProductComparison Q (p.eval.obj X) (q.eval.obj X)) =
      (Over.map r).map
        (prod.map (SyntaxPolynomial.parameterComparison P X p)
          (SyntaxPolynomial.parameterComparison P X q) ≫
            constantProductComparison P (p.eval.obj X) (q.eval.obj X)) ≫
          baseMap r (p.eval.obj X ⨯ q.eval.obj X)
    rw [Category.assoc, ← Category.assoc (prod.map _ _), prod.map_map, hp, hq,
      ← prod.map_map, ← Category.assoc, ← Category.assoc, ← prodComparison_natural]
    simp only [Category.assoc]
    rw [baseMap_product, ← Category.assoc, ← (Over.map r).map_comp]
  | sum p q hp hq =>
    change (inv (coprodComparison _ _ _) ≫
        coprod.map (polynomialMap r (baseMap r X.1, baseMap r X.2) p)
          (polynomialMap r (baseMap r X.1, baseMap r X.2) q)) ≫
      (coprod.map (SyntaxPolynomial.parameterComparison Q X p)
        (SyntaxPolynomial.parameterComparison Q X q) ≫
          constantCoproductComparison Q (p.eval.obj X) (q.eval.obj X)) =
      (Over.map r).map
        (coprod.map (SyntaxPolynomial.parameterComparison P X p)
          (SyntaxPolynomial.parameterComparison P X q) ≫
            constantCoproductComparison P (p.eval.obj X) (q.eval.obj X)) ≫
          baseMap r (p.eval.obj X ⨿ q.eval.obj X)
    rw [Category.assoc, ← Category.assoc (coprod.map _ _), coprod.map_map, hp, hq,
      ← coprod.map_map, ← Category.assoc, ← Category.assoc, coprodComparison_inv_natural]
    simp only [Category.assoc]
    rw [baseMap_coproduct, ← Category.assoc, ← (Over.map r).map_comp]

theorem parameter_algebra_str (X : D × D) (p : SyntaxPolynomial D)
    {Y : D} (α : p.eval.obj X ⟶ Y) :
    polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫
        (SyntaxPolynomial.parameterComparison Q X p ≫ (constantFamilyFunctor Q).map α) =
      (Over.map r).map (SyntaxPolynomial.parameterComparison P X p ≫
        (constantFamilyFunctor P).map α) ≫ baseMap r Y := by
  rw [← Category.assoc, polynomialMap_comparison, Category.assoc, baseMap_natural,
    ← Category.assoc, ← Functor.map_comp]

/-- Adjunction mates for the two sorts. -/
def mate {A : Over P × Over P} {B : Over Q × Over Q}
    (f : ((Over.map r).obj A.1, (Over.map r).obj A.2) ⟶ B) :
    A ⟶ ((Over.pullback r).obj B.1, (Over.pullback r).obj B.2) :=
  ((Over.mapPullbackAdj r).homEquiv _ _ f.1,
    (Over.mapPullbackAdj r).homEquiv _ _ f.2)

def counitPair (B : Over Q × Over Q) :
    ((Over.map r).obj ((Over.pullback r).obj B.1),
      (Over.map r).obj ((Over.pullback r).obj B.2)) ⟶ B :=
  ((Over.mapPullbackAdj r).counit.app B.1, (Over.mapPullbackAdj r).counit.app B.2)

omit [FinitaryExtensive D] in
theorem mate_counit {A : Over P × Over P} {B : Over Q × Over Q}
    (f : ((Over.map r).obj A.1, (Over.map r).obj A.2) ⟶ B) :
    ((Over.map r).map (mate r f).1, (Over.map r).map (mate r f).2) ≫ counitPair r B = f := by
  apply Prod.ext
  · change (Over.map r).map ((Over.mapPullbackAdj r).homEquiv A.1 B.1 f.1) ≫
      (Over.mapPullbackAdj r).counit.app B.1 = f.1
    exact ((Over.mapPullbackAdj r).homEquiv_counit
      (g := (Over.mapPullbackAdj r).homEquiv A.1 B.1 f.1)).symm.trans
        (((Over.mapPullbackAdj r).homEquiv A.1 B.1).symm_apply_apply f.1)
  · change (Over.map r).map ((Over.mapPullbackAdj r).homEquiv A.2 B.2 f.2) ≫
      (Over.mapPullbackAdj r).counit.app B.2 = f.2
    exact ((Over.mapPullbackAdj r).homEquiv_counit
      (g := (Over.mapPullbackAdj r).homEquiv A.2 B.2 f.2)).symm.trans
        (((Over.mapPullbackAdj r).homEquiv A.2 B.2).symm_apply_apply f.2)

/-- The algebra pulled to the new parameter by adjunction. The polynomial comparison is
constructed above, rather than assumed. -/
def reindexAlgebra (p q : SyntaxPolynomial D)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters Q) (q.withParameters Q))) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters P) (q.withParameters P)) where
  a := ((Over.pullback r).obj B.a.1, (Over.pullback r).obj B.a.2)
  str := mate r
    (polynomialMap r (counitPair r B.a) p ≫ B.str.1,
      polynomialMap r (counitPair r B.a) q ≫ B.str.2)

theorem mate_algebra_hom (p q : SyntaxPolynomial D)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters P) (q.withParameters P)))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters Q) (q.withParameters Q)))
    (f : ((Over.map r).obj A.a.1, (Over.map r).obj A.a.2) ⟶ B.a)
    (hp : polynomialMap r f p ≫ B.str.1 = (Over.map r).map A.str.1 ≫ f.1)
    (hq : polynomialMap r f q ≫ B.str.2 = (Over.map r).map A.str.2 ≫ f.2) :
    (SyntaxPolynomial.jointFunctor (p.withParameters P) (q.withParameters P)).map
        (mate r f) ≫ (reindexAlgebra r p q B).str = A.str ≫ mate r f := by
  apply Prod.ext
  · let β : (p.withParameters Q).eval.obj B.a ⟶ B.a.1 := B.str.1
    change (p.withParameters P).eval.map (mate r f) ≫
        (Over.mapPullbackAdj r).homEquiv _ _
          (polynomialMap r (counitPair r B.a) p ≫ β) =
      A.str.1 ≫ (Over.mapPullbackAdj r).homEquiv _ _ f.1
    apply ((Over.mapPullbackAdj r).homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_left_symm]
    simp only [Equiv.symm_apply_apply]
    rw [← Category.assoc, polynomialMap_left r (mate r f) (counitPair r B.a) p,
      mate_counit r f]
    exact hp
  · let β : (q.withParameters Q).eval.obj B.a ⟶ B.a.2 := B.str.2
    change (q.withParameters P).eval.map (mate r f) ≫
        (Over.mapPullbackAdj r).homEquiv _ _
          (polynomialMap r (counitPair r B.a) q ≫ β) =
      A.str.2 ≫ (Over.mapPullbackAdj r).homEquiv _ _ f.2
    apply ((Over.mapPullbackAdj r).homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_left_symm]
    simp only [Equiv.symm_apply_apply]
    rw [← Category.assoc, polynomialMap_left r (mate r f) (counitPair r B.a) q,
      mate_counit r f]
    exact hq

/-- Initiality gives uniqueness across arbitrary parameter maps, including
maps with no inverse or section. -/
theorem cross_hom_unique (p q : SyntaxPolynomial D)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters P) (q.withParameters P))) (hA : IsInitial A)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters Q) (q.withParameters Q)))
    (f g : ((Over.map r).obj A.a.1, (Over.map r).obj A.a.2) ⟶ B.a)
    (hfp : polynomialMap r f p ≫ B.str.1 = (Over.map r).map A.str.1 ≫ f.1)
    (hfq : polynomialMap r f q ≫ B.str.2 = (Over.map r).map A.str.2 ≫ f.2)
    (hgp : polynomialMap r g p ≫ B.str.1 = (Over.map r).map A.str.1 ≫ g.1)
    (hgq : polynomialMap r g q ≫ B.str.2 = (Over.map r).map A.str.2 ≫ g.2) : f = g := by
  let f' : A ⟶ reindexAlgebra r p q B :=
    ⟨mate r f, mate_algebra_hom r p q A B f hfp hfq⟩
  let g' : A ⟶ reindexAlgebra r p q B :=
    ⟨mate r g, mate_algebra_hom r p q A B g hgp hgq⟩
  have he : mate r f = mate r g := congrArg Endofunctor.Algebra.Hom.f (hA.hom_ext f' g')
  apply Prod.ext
  · exact ((Over.mapPullbackAdj r).homEquiv _ _).injective (congrArg Prod.fst he)
  · exact ((Over.mapPullbackAdj r).homEquiv _ _).injective (congrArg Prod.snd he)

end SyntaxParameterChange

namespace CategoricalSyntax

open SyntaxParameterChange

variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)
variable {P Q : D} (r : P ⟶ Q)

/-- The original two syntax objects as constant parameter families. -/
def parameterSyntaxFamilies (R : D) : Over R × Over R :=
  (constantFamily R S.algebra.a.1, constantFamily R S.algebra.a.2)

/-- The old-parameter fold, precomposed with the canonical map that changes only the
parameter coordinate. -/
def crossParameterFold
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters Q)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters Q))) :
    ((Over.map r).obj (constantFamily P S.algebra.a.1),
      (Over.map r).obj (constantFamily P S.algebra.a.2)) ⟶ B.a :=
  (baseMap r S.algebra.a.1, baseMap r S.algebra.a.2) ≫ S.foldWithParameters Q B

theorem crossParameterFold_commutes
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters Q)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters Q))) :
    (polynomialMap r (A := S.parameterSyntaxFamilies P) (S.crossParameterFold r B)
        (SyntaxPolynomial.termExpression V σ d) ≫
        B.str.1,
      polynomialMap r (A := S.parameterSyntaxFamilies P) (S.crossParameterFold r B)
        (SyntaxPolynomial.formulaExpression V π d) ≫
        B.str.2) =
      ((Over.map r).map
          (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
            (SyntaxPolynomial.formulaExpression V π d) S.algebra P).str.1 ≫
          (S.crossParameterFold r B).1,
        (Over.map r).map
          (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
            (SyntaxPolynomial.formulaExpression V π d) S.algebra P).str.2 ≫
          (S.crossParameterFold r B).2) := by
  apply Prod.ext
  · let β : ((SyntaxPolynomial.termExpression V σ d).withParameters Q).eval.obj B.a ⟶
        B.a.1 := B.str.1
    have hf : ((SyntaxPolynomial.termExpression V σ d).withParameters Q).eval.map
          (S.foldWithParameters Q B) ≫ β =
        (SyntaxPolynomial.parameterComparison Q S.algebra.a
          (SyntaxPolynomial.termExpression V σ d) ≫
            (constantFamilyFunctor Q).map S.algebra.str.1) ≫
          (S.foldWithParameters Q B).1 :=
      congrArg Prod.fst (S.foldWithParameters_commutes Q B)
    change _ ≫ β = _
    dsimp only [parameterSyntaxFamilies, crossParameterFold]
    rw [← polynomialMap_right, Category.assoc, hf, ← Category.assoc,
      parameter_algebra_str, Category.assoc]
    rfl
  · let β : ((SyntaxPolynomial.formulaExpression V π d).withParameters Q).eval.obj B.a ⟶
        B.a.2 := B.str.2
    have hf : ((SyntaxPolynomial.formulaExpression V π d).withParameters Q).eval.map
          (S.foldWithParameters Q B) ≫ β =
        (SyntaxPolynomial.parameterComparison Q S.algebra.a
          (SyntaxPolynomial.formulaExpression V π d) ≫
            (constantFamilyFunctor Q).map S.algebra.str.2) ≫
          (S.foldWithParameters Q B).2 :=
      congrArg Prod.snd (S.foldWithParameters_commutes Q B)
    change _ ≫ β = _
    dsimp only [parameterSyntaxFamilies, crossParameterFold]
    rw [← polynomialMap_right, Category.assoc, hf, ← Category.assoc,
      parameter_algebra_str, Category.assoc]
    rfl

/-- A constructor-preserving map over `r` agrees with the fold over `Q`. This uses
initiality over `P`, not an elementwise argument. -/
theorem crossParameterFold_unique
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters Q)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters Q)))
    (f : ((Over.map r).obj (constantFamily P S.algebra.a.1),
      (Over.map r).obj (constantFamily P S.algebra.a.2)) ⟶ B.a)
    (hf : (polynomialMap r (A := S.parameterSyntaxFamilies P) f
          (SyntaxPolynomial.termExpression V σ d) ≫ B.str.1,
        polynomialMap r (A := S.parameterSyntaxFamilies P) f
          (SyntaxPolynomial.formulaExpression V π d) ≫ B.str.2) =
      ((Over.map r).map
          (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
            (SyntaxPolynomial.formulaExpression V π d) S.algebra P).str.1 ≫ f.1,
        (Over.map r).map
          (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
            (SyntaxPolynomial.formulaExpression V π d) S.algebra P).str.2 ≫ f.2)) :
    f = S.crossParameterFold r B := by
  exact cross_hom_unique r (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra P)
    (S.stable P) B f (S.crossParameterFold r B)
    (congrArg Prod.fst hf) (congrArg Prod.snd hf)
    (congrArg Prod.fst (S.crossParameterFold_commutes r B))
    (congrArg Prod.snd (S.crossParameterFold_commutes r B))

/-- The reindexed fold is the fold into the reindexed algebra, with the comparison
constructed from the slice adjunction. -/
theorem fold_parameter_change
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters Q)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters Q))) :
    mate r (A := S.parameterSyntaxFamilies P) (S.crossParameterFold r B) =
      S.foldWithParameters P (reindexAlgebra r (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) B) := by
  refine S.foldWithParameters_unique P
    (reindexAlgebra r (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) B)
    (mate r (A := S.parameterSyntaxFamilies P) (S.crossParameterFold r B)) ?_
  exact mate_algebra_hom r (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra P) B (S.crossParameterFold r B)
    (congrArg Prod.fst (S.crossParameterFold_commutes r B))
    (congrArg Prod.snd (S.crossParameterFold_commutes r B))

end CategoricalSyntax

end CategoricalEssentialIncompleteness.V46
