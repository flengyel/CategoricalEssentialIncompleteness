import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonFreeVariables
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonOptions

/-! # Every named constructor under the actual uniform syntax chart -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison

private theorem map_diagram_comp {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) {A B Z : C} {A' B' Z' : D}
    (f : A ⟶ B) (g : B ⟶ Z)
    (iA : G.obj A ⟶ A') (iB : G.obj B ⟶ B') (iZ : G.obj Z ⟶ Z')
    (f' : A' ⟶ B') (g' : B' ⟶ Z')
    (hf : G.map f ≫ iB = iA ≫ f') (hg : G.map g ≫ iZ = iB ≫ g') :
    G.map (f ≫ g) ≫ iZ = iA ≫ f' ≫ g' := by
  calc
    _ = (G.map f ≫ G.map g) ≫ iZ :=
      congrArg (fun k => k ≫ iZ) (G.map_comp f g)
    _ = G.map f ≫ (G.map g ≫ iZ) := Category.assoc _ _ _
    _ = G.map f ≫ (iB ≫ g') := congrArg (fun k => G.map f ≫ k) hg
    _ = (G.map f ≫ iB) ≫ g' := (Category.assoc _ _ _).symm
    _ = (iA ≫ f') ≫ g' := congrArg (fun k => k ≫ g') hf
    _ = _ := Category.assoc _ _ _

section PolynomialInjections
universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasFiniteCoproducts C]

/-- The actual coproduct injection, with its polynomial codomain fixed
before specializing the category or either recursive carrier. -/
def polynomialInl (a b : SyntaxPolynomial C) (X : C × C) :
    a.eval.obj X ⟶ (SyntaxPolynomial.sum a b).eval.obj X :=
  (coprod.inl : a.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X)

def polynomialInr (a b : SyntaxPolynomial C) (X : C × C) :
    b.eval.obj X ⟶ (SyntaxPolynomial.sum a b).eval.obj X :=
  (coprod.inr : b.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X)

theorem polynomialInl_eq (a b : SyntaxPolynomial C) (X : C × C) :
    polynomialInl a b X =
      (coprod.inl : a.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) := rfl

theorem polynomialInr_eq (a b : SyntaxPolynomial C) (X : C × C) :
    polynomialInr a b X =
      (coprod.inr : b.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) := rfl

@[reassoc] theorem polynomialInl_map (a b : SyntaxPolynomial C)
    {X Y : C × C} (k : X ⟶ Y) :
    polynomialInl a b X ≫ (SyntaxPolynomial.sum a b).eval.map k =
      a.eval.map k ≫ polynomialInl a b Y := by
  exact coprod.inl_map (a.eval.map k) (b.eval.map k)

@[reassoc] theorem polynomialInr_map (a b : SyntaxPolynomial C)
    {X Y : C × C} (k : X ⟶ Y) :
    polynomialInr a b X ≫ (SyntaxPolynomial.sum a b).eval.map k =
      b.eval.map k ≫ polynomialInr a b Y := by
  exact coprod.inr_map (a.eval.map k) (b.eval.map k)
end PolynomialInjections

variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)

def constructorInput (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) (Y : Total.TotalCategory P × Total.TotalCategory P)
    (c : (FP).obj X ≅ Y) (a : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r : SyntaxPolynomial (Total.TotalCategory P))
    (h : Syntax.Polynomial.mapped P a=r) : (F).obj (a.eval.obj X) ≅ r.eval.obj Y :=
  normalizedComponent P a r h X ≪≫ r.eval.mapIso c

private theorem constructorInput_coefficient
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (C : PredicateCategory 𝗣𝗔) :
    (constructorInput P X Y c (.coefficient C) (.coefficient ((F).obj C)) rfl).hom =
      𝟙 ((F).obj C) := by
  simp only [constructorInput,normalizedComponent,Syntax.Polynomial.component,
    Iso.trans_hom,eqToIso_refl,Iso.refl_hom,Category.comp_id,
    CategoryTheory.Functor.mapIso_hom,SyntaxPolynomial.eval,
    CategoryTheory.Functor.const_obj_map,Category.id_comp]


private theorem constructorInput_term
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y) :
    (constructorInput P X Y c .term .term rfl).hom = c.hom.1 := by
  change ((𝟙 ((F).obj X.1) ≫ 𝟙 ((F).obj X.1)) ≫ c.hom.1) = c.hom.1
  simp only [Category.id_comp]

private theorem constructorInput_formula
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y) :
    (constructorInput P X Y c .formula .formula rfl).hom = c.hom.2 := by
  change ((𝟙 ((F).obj X.2) ≫ 𝟙 ((F).obj X.2)) ≫ c.hom.2) = c.hom.2
  simp only [Category.id_comp]

private theorem constructorInput_product
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a = r) (hb : Syntax.Polynomial.mapped P b = s) :
    (constructorInput P X Y c (.product a b) (.product r s)
      (congrArg₂ SyntaxPolynomial.product ha hb)).hom =
      prodComparison (F) (a.eval.obj X) (b.eval.obj X) ≫
        prod.map (constructorInput P X Y c a r ha).hom
          (constructorInput P X Y c b s hb).hom := by
  change (normalizedComponent P (.product a b) (.product r s)
      (congrArg₂ SyntaxPolynomial.product ha hb) X).hom ≫
      prod.map (r.eval.map c.hom) (s.eval.map c.hom) =
    prodComparison (F) (a.eval.obj X) (b.eval.obj X) ≫
      prod.map ((normalizedComponent P a r ha X).hom ≫ r.eval.map c.hom)
        ((normalizedComponent P b s hb X).hom ≫ s.eval.map c.hom)
  rw [normalizedComponent_product P a b r s ha hb X]
  change (prodComparison (F) (a.eval.obj X) (b.eval.obj X) ≫
      prod.map (normalizedComponent P a r ha X).hom (normalizedComponent P b s hb X).hom) ≫
      prod.map (r.eval.map c.hom) (s.eval.map c.hom) = _
  rw [Category.assoc, prod.map_map]

private theorem constructorInput_term_square
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y) :
    (constructorInput P X Y c (SyntaxPolynomial.power .term 2) (SyntaxPolynomial.power .term 2)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2)).hom =
      prodComparison (F) X.1 X.1 ≫ prod.map c.hom.1 c.hom.1 := by
  exact (constructorInput_product P X Y c .term .term .term .term rfl rfl).trans
    (congrArg (fun u => prodComparison (F) X.1 X.1 ≫ prod.map u u)
      (constructorInput_term P X Y c))

private theorem constructorInput_formula_square
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y) :
    (constructorInput P X Y c (SyntaxPolynomial.power .formula 2) (SyntaxPolynomial.power .formula 2)
      (SyntaxOperationsTransport.mapCoefficients_power (F).obj .formula 2)).hom =
      prodComparison (F) X.2 X.2 ≫ prod.map c.hom.2 c.hom.2 := by
  exact (constructorInput_product P X Y c .formula .formula .formula .formula rfl rfl).trans
    (congrArg (fun u => prodComparison (F) X.2 X.2 ≫ prod.map u u)
      (constructorInput_formula P X Y c))

private theorem constructorInput_quantifier_product
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (V : PredicateCategory 𝗣𝗔) :
    (constructorInput P X Y c (.product (.coefficient V) .formula)
      (.product (.coefficient ((F).obj V)) .formula) rfl).hom =
      prodComparison (F) V X.2 ≫ prod.map (𝟙 ((F).obj V)) c.hom.2 := by
  exact (constructorInput_product P X Y c (.coefficient V) .formula
    (.coefficient ((F).obj V)) .formula rfl rfl).trans
      (congrArg₂ (fun u v => prodComparison (F) V X.2 ≫ prod.map u v)
        (constructorInput_coefficient P X Y c V) (constructorInput_formula P X Y c))

@[reassoc] theorem constructorInput_inl (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s) :
    (F).map (polynomialInl (C := PredicateCategory 𝗣𝗔) a b X) ≫
      (constructorInput P X Y c (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb)).hom=
        (constructorInput P X Y c a r ha).hom ≫
          polynomialInl (C := Total.TotalCategory P) r s Y := by
  have h := normalizedComponent_inl P a b r s ha hb X
  change (F).map (polynomialInl (C := PredicateCategory 𝗣𝗔) a b X) ≫
      (normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X).hom =
    (normalizedComponent P a r ha X).hom ≫
      polynomialInl (C := Total.TotalCategory P) r s ((FP).obj X) at h
  calc
    _ = ((F).map (polynomialInl (C := PredicateCategory 𝗣𝗔) a b X) ≫
      (normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X).hom) ≫
        (SyntaxPolynomial.sum r s).eval.map c.hom := (Category.assoc _ _ _).symm
    _ = ((normalizedComponent P a r ha X).hom ≫
      polynomialInl (C := Total.TotalCategory P) r s ((FP).obj X)) ≫
        (SyntaxPolynomial.sum r s).eval.map c.hom :=
      congrArg (fun f => f ≫ (SyntaxPolynomial.sum r s).eval.map c.hom) h
    _ = (normalizedComponent P a r ha X).hom ≫ r.eval.map c.hom ≫
      polynomialInl (C := Total.TotalCategory P) r s Y := by
      rw [Category.assoc,polynomialInl_map r s c.hom]
    _ = _ := (Category.assoc _ _ _).symm

@[reassoc] theorem constructorInput_inr (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
    (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (FP).obj X ≅ Y)
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s) :
    (F).map (polynomialInr (C := PredicateCategory 𝗣𝗔) a b X) ≫
      (constructorInput P X Y c (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb)).hom=
        (constructorInput P X Y c b s hb).hom ≫
          polynomialInr (C := Total.TotalCategory P) r s Y := by
  have h := normalizedComponent_inr P a b r s ha hb X
  change (F).map (polynomialInr (C := PredicateCategory 𝗣𝗔) a b X) ≫
      (normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X).hom =
    (normalizedComponent P b s hb X).hom ≫
      polynomialInr (C := Total.TotalCategory P) r s ((FP).obj X) at h
  calc
    _ = ((F).map (polynomialInr (C := PredicateCategory 𝗣𝗔) a b X) ≫
      (normalizedComponent P (.sum a b) (.sum r s) (congrArg₂ SyntaxPolynomial.sum ha hb) X).hom) ≫
        (SyntaxPolynomial.sum r s).eval.map c.hom := (Category.assoc _ _ _).symm
    _ = ((normalizedComponent P b s hb X).hom ≫
      polynomialInr (C := Total.TotalCategory P) r s ((FP).obj X)) ≫
        (SyntaxPolynomial.sum r s).eval.map c.hom :=
      congrArg (fun f => f ≫ (SyntaxPolynomial.sum r s).eval.map c.hom) h
    _ = (normalizedComponent P b s hb X).hom ≫ s.eval.map c.hom ≫
      polynomialInr (C := Total.TotalCategory P) r s Y := by
      rw [Category.assoc,polynomialInr_map r s c.hom]
    _ = _ := (Category.assoc _ _ _).symm

theorem constructorInput_natural {X X0 : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    {Y Y0 : Total.TotalCategory P × Total.TotalCategory P} (c : (FP).obj X ≅ Y) (c0 : (FP).obj X0 ≅ Y0)
    (f : X ⟶ X0) (g : Y ⟶ Y0) (hc : (FP).map f ≫ c0.hom=c.hom ≫ g)
    (a : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) :
    (F).map (a.eval.map f) ≫ (constructorInput P X0 Y0 c0 a r ha).hom=
      (constructorInput P X Y c a r ha).hom ≫ r.eval.map g := by
  cases ha
  simp only [constructorInput,normalizedComponent,Iso.trans_hom,eqToIso_refl,Iso.refl_hom,
    Category.comp_id,CategoryTheory.Functor.mapIso_hom]
  rw [← Category.assoc,Syntax.Polynomial.component_natural P a f,Category.assoc,
    ← CategoryTheory.Functor.map_comp,hc,CategoryTheory.Functor.map_comp,← Category.assoc]

/-- Project the constructed whole-algebra square before substituting the
literal syntax objects. The comparison is the actual algebra isomorphism. -/
theorem constructorInput_structure_first
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s))
    (k : B ≅ castAlgebra ha hb (Syntax.Polynomial.mappedAlgebra P a b A)) :
    (F).map A.str.1 ≫ (castedCarrierIso P a b r s ha hb A B k).inv.1 =
      (constructorInput P A.a B.a (castedCarrierIso P a b r s ha hb A B k).symm
        a r ha).hom ≫ B.str.1 := by
  have h := congrArg
    (fun f : (FP).obj ((SyntaxPolynomial.jointFunctor a b).obj A.a) ⟶ B.a => f.1)
    (normalized_iso_structure P a b r s ha hb A B k)
  change (F).map A.str.1 ≫ (castedCarrierIso P a b r s ha hb A B k).inv.1 =
    ((normalizedJointIso P a b r s ha hb).hom.app A.a).1 ≫
      r.eval.map (castedCarrierIso P a b r s ha hb A B k).inv ≫ B.str.1 at h
  rw [normalizedJointIso_first P a b r s ha hb A.a] at h
  simpa only [constructorInput,Iso.trans_hom,CategoryTheory.Functor.mapIso_hom,Iso.symm_hom,
    Category.assoc] using h

theorem constructorInput_structure_second
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (r s : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a=r) (hb : Syntax.Polynomial.mapped P b=s)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s))
    (k : B ≅ castAlgebra ha hb (Syntax.Polynomial.mappedAlgebra P a b A)) :
    (F).map A.str.2 ≫ (castedCarrierIso P a b r s ha hb A B k).inv.2 =
      (constructorInput P A.a B.a (castedCarrierIso P a b r s ha hb A B k).symm
        b s hb).hom ≫ B.str.2 := by
  have h := congrArg
    (fun f : (FP).obj ((SyntaxPolynomial.jointFunctor a b).obj A.a) ⟶ B.a => f.2)
    (normalized_iso_structure P a b r s ha hb A B k)
  change (F).map A.str.2 ≫ (castedCarrierIso P a b r s ha hb A B k).inv.2 =
    ((normalizedJointIso P a b r s ha hb).hom.app A.a).2 ≫
      s.eval.map (castedCarrierIso P a b r s ha hb A B k).inv ≫ B.str.2 at h
  rw [normalizedJointIso_second P a b r s ha hb A.a] at h
  simpa only [constructorInput,Iso.trans_hom,CategoryTheory.Functor.mapIso_hom,Iso.symm_hom,
    Category.assoc] using h


section FormulaConstructorSquares
variable (V : PredicateCategory 𝗣𝗔) (π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
variable (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
  (Y : Total.TotalCategory P × Total.TotalCategory P) (c : (CategoryTheory.Functor.prod (Syntax.predicateFunctor P)
    (Syntax.predicateFunctor P)).obj X ≅ Y)
local notation "E₀" => SyntaxPolynomial.power (D := PredicateCategory 𝗣𝗔) SyntaxPolynomial.term 2
local notation "E₁" => SyntaxPolynomial.power (D := Total.TotalCategory P) SyntaxPolynomial.term 2
local notation "R₀" => SyntaxPolynomial.constructors π d
local notation "R₁" => SyntaxPolynomial.constructors (fun n => CategoryTheory.Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "A₀" => SyntaxPolynomial.sum (E₀) (R₀)
local notation "A₁" => SyntaxPolynomial.sum (E₁) (R₁)
local notation "U₀" => SyntaxPolynomial.sum (A₀) SyntaxPolynomial.formula
local notation "U₁" => SyntaxPolynomial.sum (A₁) SyntaxPolynomial.formula
local notation "B₀" => SyntaxPolynomial.sum (U₀) (SyntaxPolynomial.power SyntaxPolynomial.formula 2)
local notation "B₁" => SyntaxPolynomial.sum (U₁) (SyntaxPolynomial.power SyntaxPolynomial.formula 2)
local notation "Q₀" => SyntaxPolynomial.product (SyntaxPolynomial.coefficient V) SyntaxPolynomial.formula
local notation "Q₁" => SyntaxPolynomial.product (SyntaxPolynomial.coefficient (CategoryTheory.Functor.obj (Syntax.predicateFunctor P) V)) SyntaxPolynomial.formula
local notation "hE" => SyntaxOperationsTransport.mapCoefficients_power (CategoryTheory.Functor.obj (Syntax.predicateFunctor P)) SyntaxPolynomial.term 2
local notation "hR" => SyntaxOperationsTransport.mapCoefficients_constructors (CategoryTheory.Functor.obj (Syntax.predicateFunctor P)) π d
local notation "hA" => (congrArg₂ SyntaxPolynomial.sum (hE) (hR))
local notation "hU" => (congrArg₂ SyntaxPolynomial.sum (hA) rfl)
local notation "hF" => SyntaxOperationsTransport.mapCoefficients_power (CategoryTheory.Functor.obj (Syntax.predicateFunctor P)) SyntaxPolynomial.formula 2
local notation "hB" => (congrArg₂ SyntaxPolynomial.sum (hU) (hF))
local notation "iA" => constructorInput P X Y c (A₀) (A₁) (hA)
local notation "iU" => constructorInput P X Y c (U₀) (U₁) (hU)
local notation "iB" => constructorInput P X Y c (B₀) (B₁) (hB)
local notation "iE" => constructorInput P X Y c (E₀) (E₁) (hE)
local notation "iR" => constructorInput P X Y c (R₀) (R₁) (hR)
local notation "iN" => constructorInput P X Y c SyntaxPolynomial.formula SyntaxPolynomial.formula rfl
local notation "iF" => constructorInput P X Y c (SyntaxPolynomial.power SyntaxPolynomial.formula 2) (SyntaxPolynomial.power SyntaxPolynomial.formula 2) (hF)
local notation "iQ" => constructorInput P X Y c (Q₀) (Q₁) rfl
local notation "iWhole" => constructorInput P X Y c
  (SyntaxPolynomial.formulaExpression V π d)
  (SyntaxPolynomial.formulaExpression (CategoryTheory.Functor.obj (Syntax.predicateFunctor P) V)
    (fun n => CategoryTheory.Functor.obj (Syntax.predicateFunctor P) (π n)) d) (formulaExpression_mapped P V π d)
variable (s₀ : (SyntaxPolynomial.formulaExpression V π d).eval.obj X ⟶ X.2)
  (s₁ : (SyntaxPolynomial.formulaExpression ((Syntax.predicateFunctor P).obj V) (fun n => (Syntax.predicateFunctor P).obj (π n)) d).eval.obj Y ⟶ Y.2)
  (k : (Syntax.predicateFunctor P).obj X.2 ⟶ Y.2)
  (hs : (Syntax.predicateFunctor P).map s₀ ≫ k = (constructorInput P X Y c
    (SyntaxPolynomial.formulaExpression V π d)
    (SyntaxPolynomial.formulaExpression ((Syntax.predicateFunctor P).obj V)
      (fun n => (Syntax.predicateFunctor P).obj (π n)) d)
    (formulaExpression_mapped P V π d)).hom ≫ s₁)
include hs

private theorem formula_nonquantified_square :
    (F).map (polynomialInl (B₀) (Q₀) X ≫ s₀) ≫ k =
      (iB).hom ≫ polynomialInl (B₁) (Q₁) Y ≫ s₁ := by
  exact map_diagram_comp (F) (polynomialInl (B₀) (Q₀) X) s₀
    (iB).hom (iWhole).hom k (polynomialInl (B₁) (Q₁) Y) s₁
    (constructorInput_inl P X Y c (B₀) (Q₀) (B₁) (Q₁) (hB) rfl) hs

private theorem formula_unary_square :
    (F).map (polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫
      polynomialInl (B₀) (Q₀) X ≫ s₀) ≫ k =
      (iU).hom ≫ polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
        polynomialInl (B₁) (Q₁) Y ≫ s₁ := by
  exact map_diagram_comp (F)
    (polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X)
    (polynomialInl (B₀) (Q₀) X ≫ s₀)
    (iU).hom (iB).hom k (polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y)
    (polynomialInl (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_inl P X Y c (U₀) (SyntaxPolynomial.power .formula 2)
      (U₁) (SyntaxPolynomial.power .formula 2) (hU) (hF))
    (formula_nonquantified_square P V π d X Y c s₀ s₁ k hs)

private theorem formula_atoms_square :
    (F).map (polynomialInl (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫
        polynomialInl (B₀) (Q₀) X ≫ s₀) ≫ k =
      (iA).hom ≫ polynomialInl (A₁) SyntaxPolynomial.formula Y ≫
        polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
          polynomialInl (B₁) (Q₁) Y ≫ s₁ := by
  exact map_diagram_comp (F) (polynomialInl (A₀) SyntaxPolynomial.formula X)
    (polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫
      polynomialInl (B₀) (Q₀) X ≫ s₀)
    (iA).hom (iU).hom k (polynomialInl (A₁) SyntaxPolynomial.formula Y)
    (polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
      polynomialInl (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_inl P X Y c (A₀) SyntaxPolynomial.formula (A₁) SyntaxPolynomial.formula (hA) rfl)
    (formula_unary_square P V π d X Y c s₀ s₁ k hs)

private theorem raw_relation_square :
    (F).map (polynomialInr (E₀) (R₀) X ≫ polynomialInl (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫
        polynomialInl (B₀) (Q₀) X ≫ s₀) ≫ k =
      (iR).hom ≫ polynomialInr (E₁) (R₁) Y ≫ polynomialInl (A₁) SyntaxPolynomial.formula Y ≫
        polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
          polynomialInl (B₁) (Q₁) Y ≫ s₁ := by
  exact map_diagram_comp (F) (polynomialInr (E₀) (R₀) X)
    (polynomialInl (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫ polynomialInl (B₀) (Q₀) X ≫ s₀)
    (iR).hom (iA).hom k (polynomialInr (E₁) (R₁) Y)
    (polynomialInl (A₁) SyntaxPolynomial.formula Y ≫
      polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_inr P X Y c (E₀) (R₀) (E₁) (R₁) (hE) (hR))
    (formula_atoms_square P V π d X Y c s₀ s₁ k hs)

private theorem raw_equality_square :
    (F).map (polynomialInl (E₀) (R₀) X ≫ polynomialInl (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫
        polynomialInl (B₀) (Q₀) X ≫ s₀) ≫ k =
      (prodComparison (F) X.1 X.1 ≫ prod.map c.hom.1 c.hom.1) ≫
        polynomialInl (E₁) (R₁) Y ≫ polynomialInl (A₁) SyntaxPolynomial.formula Y ≫
          polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
            polynomialInl (B₁) (Q₁) Y ≫ s₁ := by
  have h := map_diagram_comp (F) (polynomialInl (E₀) (R₀) X)
    (polynomialInl (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫ polynomialInl (B₀) (Q₀) X ≫ s₀)
    (iE).hom (iA).hom k (polynomialInl (E₁) (R₁) Y)
    (polynomialInl (A₁) SyntaxPolynomial.formula Y ≫
      polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_inl P X Y c (E₀) (R₀) (E₁) (R₁) (hE) (hR))
    (formula_atoms_square P V π d X Y c s₀ s₁ k hs)
  exact h.trans (congrArg (fun u => u ≫ polynomialInl (E₁) (R₁) Y ≫
    polynomialInl (A₁) SyntaxPolynomial.formula Y ≫
      polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_term_square P X Y c))

omit hs in
private theorem formula_unary_injection_square :
    (F).map (polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫
      polynomialInl (B₀) (Q₀) X) ≫ (iWhole).hom =
      (iU).hom ≫ polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
        polynomialInl (B₁) (Q₁) Y := by
  exact map_diagram_comp (F)
    (polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X) (polynomialInl (B₀) (Q₀) X)
    (iU).hom (iB).hom (iWhole).hom
    (polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y) (polynomialInl (B₁) (Q₁) Y)
    (constructorInput_inl P X Y c (U₀) (SyntaxPolynomial.power .formula 2)
      (U₁) (SyntaxPolynomial.power .formula 2) (hU) (hF))
    (constructorInput_inl P X Y c (B₀) (Q₀) (B₁) (Q₁) (hB) rfl)

private theorem raw_negation_square :
    (F).map ((polynomialInr (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫ polynomialInl (B₀) (Q₀) X) ≫ s₀) ≫ k =
      c.hom.2 ≫ (polynomialInr (A₁) SyntaxPolynomial.formula Y ≫
        polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y) ≫ s₁ := by
  have hinj := map_diagram_comp (F) (polynomialInr (A₀) SyntaxPolynomial.formula X)
    (polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫ polynomialInl (B₀) (Q₀) X)
    (iN).hom (iU).hom (iWhole).hom (polynomialInr (A₁) SyntaxPolynomial.formula Y)
    (polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y)
    (constructorInput_inr P X Y c (A₀) SyntaxPolynomial.formula (A₁) SyntaxPolynomial.formula (hA) rfl)
    (formula_unary_injection_square P V π d X Y c)
  have h := map_diagram_comp (F)
    (polynomialInr (A₀) SyntaxPolynomial.formula X ≫
      polynomialInl (U₀) (SyntaxPolynomial.power .formula 2) X ≫ polynomialInl (B₀) (Q₀) X) s₀
    (iN).hom (iWhole).hom k
    (polynomialInr (A₁) SyntaxPolynomial.formula Y ≫
      polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y) s₁ hinj hs
  exact h.trans (congrArg (fun u => u ≫
    (polynomialInr (A₁) SyntaxPolynomial.formula Y ≫
      polynomialInl (U₁) (SyntaxPolynomial.power .formula 2) Y ≫ polynomialInl (B₁) (Q₁) Y) ≫ s₁)
    (constructorInput_formula P X Y c))

private theorem raw_implication_square :
    (F).map (polynomialInr (U₀) (SyntaxPolynomial.power .formula 2) X ≫
      polynomialInl (B₀) (Q₀) X ≫ s₀) ≫ k =
      (prodComparison (F) X.2 X.2 ≫ prod.map c.hom.2 c.hom.2) ≫
        polynomialInr (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
          polynomialInl (B₁) (Q₁) Y ≫ s₁ := by
  have h := map_diagram_comp (F)
    (polynomialInr (U₀) (SyntaxPolynomial.power .formula 2) X) (polynomialInl (B₀) (Q₀) X ≫ s₀)
    (iF).hom (iB).hom k (polynomialInr (U₁) (SyntaxPolynomial.power .formula 2) Y)
    (polynomialInl (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_inr P X Y c (U₀) (SyntaxPolynomial.power .formula 2)
      (U₁) (SyntaxPolynomial.power .formula 2) (hU) (hF))
    (formula_nonquantified_square P V π d X Y c s₀ s₁ k hs)
  exact h.trans (congrArg (fun u => u ≫ polynomialInr (U₁) (SyntaxPolynomial.power .formula 2) Y ≫
    polynomialInl (B₁) (Q₁) Y ≫ s₁) (constructorInput_formula_square P X Y c))

private theorem raw_quantifier_square :
    (F).map (polynomialInr (B₀) (Q₀) X ≫ s₀) ≫ k =
      (prodComparison (F) V X.2 ≫ prod.map (𝟙 ((F).obj V)) c.hom.2) ≫
        polynomialInr (B₁) (Q₁) Y ≫ s₁ := by
  have h := map_diagram_comp (F) (polynomialInr (B₀) (Q₀) X) s₀
    (iQ).hom (iWhole).hom k (polynomialInr (B₁) (Q₁) Y) s₁
    (constructorInput_inr P X Y c (B₀) (Q₀) (B₁) (Q₁) (hB) rfl) hs
  exact h.trans (congrArg (fun u => u ≫ polynomialInr (B₁) (Q₁) Y ≫ s₁)
    (constructorInput_quantifier_product P X Y c V))
end FormulaConstructorSquares

variable (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S₀" => sourceSyntax V σ π d
local notation "S₁" => presentedSyntax P V σ π d
local notation "a" => SyntaxPolynomial.termExpression V σ d
local notation "b" => SyntaxPolynomial.formulaExpression V π d
local notation "p" => SyntaxPolynomial.termExpression (Functor.obj (Syntax.predicateFunctor P) V) (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression (Functor.obj (Syntax.predicateFunctor P) V) (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "c" => Iso.symm (sourcePairIso P V σ π d)

def termInput : (F).obj ((a).eval.obj (S₀).algebra.a) ≅ (p).eval.obj (S₁).algebra.a :=
  constructorInput P (S₀).algebra.a (S₁).algebra.a (c) a p (termExpression_mapped P V σ d)
def formulaInput : (F).obj ((b).eval.obj (S₀).algebra.a) ≅ (q).eval.obj (S₁).algebra.a :=
  constructorInput P (S₀).algebra.a (S₁).algebra.a (c) b q (formulaExpression_mapped P V π d)

private theorem casted_sourcePairIso :
    castedCarrierIso P a b p q (termExpression_mapped P V σ d)
      (formulaExpression_mapped P V π d) (S₀).algebra (S₁).algebra
      (sourceAlgebraIso P V σ π d) = sourcePairIso P V σ π d := rfl

theorem term_structure : (F).map (S₀).algebra.str.1 ≫ (termIso P V σ π d).inv=
    (termInput P V σ π d).hom ≫ (S₁).algebra.str.1 := by
  have h := constructorInput_structure_first P a b p q
    (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)
    (S₀).algebra (S₁).algebra (sourceAlgebraIso P V σ π d)
  rw [casted_sourcePairIso P V σ π d] at h
  simpa only [termInput,termIso] using h

theorem formula_structure : (F).map (S₀).algebra.str.2 ≫ (formulaIso P V σ π d).inv=
    (formulaInput P V σ π d).hom ≫ (S₁).algebra.str.2 := by
  have h := constructorInput_structure_second P a b p q
    (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)
    (S₀).algebra (S₁).algebra (sourceAlgebraIso P V σ π d)
  rw [casted_sourcePairIso P V σ π d] at h
  simpa only [formulaInput,formulaIso] using h

def functionInput :
    (F).obj ((SyntaxPolynomial.constructors σ d).eval.obj (S₀).algebra.a) ≅
      (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d).eval.obj (S₁).algebra.a :=
  constructorInput P (S₀).algebra.a (S₁).algebra.a (c)
  (SyntaxPolynomial.constructors σ d) (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
  (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)

def relationInput :
    (F).obj ((SyntaxPolynomial.constructors π d).eval.obj (S₀).algebra.a) ≅
      (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d).eval.obj (S₁).algebra.a :=
  constructorInput P (S₀).algebra.a (S₁).algebra.a (c)
  (SyntaxPolynomial.constructors π d) (SyntaxPolynomial.constructors (fun n => (F).obj (π n)) d)
  (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d)

theorem variable_constructor : (F).map (S₀).variableConstructor ≫ (termIso P V σ π d).inv=
    (S₁).variableConstructor := by
  let X := (S₀).algebra.a
  let Y := (S₁).algebra.a
  let i := constructorInput P X Y (c) (.coefficient V) (.coefficient ((F).obj V)) rfl
  have h₀ := constructorInput_inl P X Y (c)
    (.coefficient V) (SyntaxPolynomial.constructors σ d)
    (.coefficient ((F).obj V)) (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
    rfl (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
  have h := map_diagram_comp (F)
    (polynomialInl (.coefficient V) (SyntaxPolynomial.constructors σ d) X)
    (S₀).algebra.str.1 i.hom (termInput P V σ π d).hom (termIso P V σ π d).inv
    (polynomialInl (.coefficient ((F).obj V))
      (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d) Y)
    (S₁).algebra.str.1 h₀ (term_structure P V σ π d)
  have hi := constructorInput_coefficient P X Y (c) V
  exact h.trans ((congrArg (fun f => f ≫
    polynomialInl (.coefficient ((F).obj V))
      (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d) Y ≫
      (S₁).algebra.str.1) hi).trans (Category.id_comp _))

theorem function_constructors : (F).map (S₀).functionConstructors ≫ (termIso P V σ π d).inv=
    (functionInput P V σ π d).hom ≫ (S₁).functionConstructors := by
  let X := (S₀).algebra.a
  let Y := (S₁).algebra.a
  have h₀ := constructorInput_inr P X Y (c)
    (.coefficient V) (SyntaxPolynomial.constructors σ d)
    (.coefficient ((F).obj V)) (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
    rfl (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
  exact map_diagram_comp (F)
    (polynomialInr (.coefficient V) (SyntaxPolynomial.constructors σ d) X)
    (S₀).algebra.str.1 (functionInput P V σ π d).hom (termInput P V σ π d).hom
    (termIso P V σ π d).inv
    (polynomialInr (.coefficient ((F).obj V))
      (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d) Y)
    (S₁).algebra.str.1 h₀ (term_structure P V σ π d)

theorem relation_constructors : (F).map (S₀).relationConstructors ≫ (formulaIso P V σ π d).inv=
    (relationInput P V σ π d).hom ≫ (S₁).relationConstructors := by
  exact raw_relation_square P V π d (S₀).algebra.a (S₁).algebra.a (c)
    (S₀).algebra.str.2 (S₁).algebra.str.2 (formulaIso P V σ π d).inv
    (formula_structure P V σ π d)

theorem equality_constructor : (F).map (S₀).equalityConstructor ≫ (formulaIso P V σ π d).inv=
    (Options.productIso (F) (termIso P V σ π d).symm (termIso P V σ π d).symm).hom ≫
      (S₁).equalityConstructor := by
  exact raw_equality_square P V π d (S₀).algebra.a (S₁).algebra.a (c)
    (S₀).algebra.str.2 (S₁).algebra.str.2 (formulaIso P V σ π d).inv
    (formula_structure P V σ π d)

theorem negation_constructor : (F).map (S₀).negationConstructor ≫ (formulaIso P V σ π d).inv=
    (formulaIso P V σ π d).inv ≫ (S₁).negationConstructor := by
  exact raw_negation_square P V π d (S₀).algebra.a (S₁).algebra.a (c)
    (S₀).algebra.str.2 (S₁).algebra.str.2 (formulaIso P V σ π d).inv
    (formula_structure P V σ π d)

theorem implication_constructor : (F).map (S₀).implicationConstructor ≫ (formulaIso P V σ π d).inv=
    (Options.productIso (F) (formulaIso P V σ π d).symm (formulaIso P V σ π d).symm).hom ≫
      (S₁).implicationConstructor := by
  exact raw_implication_square P V π d (S₀).algebra.a (S₁).algebra.a (c)
    (S₀).algebra.str.2 (S₁).algebra.str.2 (formulaIso P V σ π d).inv
    (formula_structure P V σ π d)

theorem quantifier_constructor : (F).map (S₀).quantifierConstructor ≫ (formulaIso P V σ π d).inv=
    (Options.productIso (F) (Iso.refl ((F).obj V)) (formulaIso P V σ π d).symm).hom ≫
      (S₁).quantifierConstructor := by
  exact raw_quantifier_square P V π d (S₀).algebra.a (S₁).algebra.a (c)
    (S₀).algebra.str.2 (S₁).algebra.str.2 (formulaIso P V σ π d).inv
    (formula_structure P V σ π d)

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
