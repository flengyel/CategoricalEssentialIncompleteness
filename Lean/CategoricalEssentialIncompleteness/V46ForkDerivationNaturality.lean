/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationComponent
public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation
public import CategoricalEssentialIncompleteness.V46NumericalUnderlying
public import CategoricalEssentialIncompleteness.ForkProofObjects

/-! # Folds and naturality on the actual valid fork proof carriers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Naturality

/-- The explicit unary presentation keeps every old carrier value as
its actual dimension-one tuple. Its program is the given partial program. -/
def unaryMap {X Y : EnumerableCarriers.Total} (f : X ⟶ Y) :
    NumericalTuples.unary X ⟶ NumericalTuples.unary Y where
  toFun := EnumerableCarriers.totalFunction f
  represented := ⟨EnumerableCarriers.val f.hom,EnumerableCarriers.val_partrec f.hom,
    fun x => Part.eq_some_iff.mpr (EnumerableCarriers.totalFunction_mem f x)⟩

def unaryFunctor : EnumerableCarriers.Total ⥤ NumericalTuples.Object where
  obj := NumericalTuples.unary
  map := unaryMap
  map_id X := by
    apply NumericalTuples.Map.ext
    funext x
    exact ConcreteCategory.congr_hom (EnumerableCarriers.underlying.map_id X) x
  map_comp f g := by
    apply NumericalTuples.Map.ext
    funext x
    exact ConcreteCategory.congr_hom (EnumerableCarriers.underlying.map_comp f g) x

theorem totalMap_ext {X Y : EnumerableCarriers.Total} (f g : X ⟶ Y)
    (h : ∀ x, EnumerableCarriers.totalFunction f x = EnumerableCarriers.totalFunction g x) : f = g := by
  apply WideSubcategory.hom_ext
  apply EnumerableCarriers.val_ext_on_source
  intro n hn
  let x : {n // n ∈ X.obj.support} := ⟨n,hn⟩
  exact (Part.eq_some_iff.mpr (EnumerableCarriers.totalFunction_mem f x)).trans
    ((congrArg (fun z : {n // n ∈ Y.obj.support} => Part.some z.val) (h x)).trans
      (Part.eq_some_iff.mpr (EnumerableCarriers.totalFunction_mem g x)).symm)

theorem totalFunction_comp {X Y Z : EnumerableCarriers.Total}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : {n // n ∈ X.obj.support}) :
    EnumerableCarriers.totalFunction (f ≫ g) x =
      EnumerableCarriers.totalFunction g (EnumerableCarriers.totalFunction f x) :=
  ConcreteCategory.congr_hom (EnumerableCarriers.underlying.map_comp f g) x

theorem totalFunction_eqToHom {X Y : EnumerableCarriers.Total} (h : X = Y)
    (x : {n // n ∈ X.obj.support}) :
    (EnumerableCarriers.totalFunction (eqToHom h) x).val = x.val := by
  cases h
  exact congrArg Subtype.val
    (ConcreteCategory.congr_hom (EnumerableCarriers.underlying.map_id X) x)

/-- This comparison is proved on the actual old carrier functions.
It uses the proved unary coding equality, rather than an inverse choice. -/
def unaryComparison : unaryFunctor ⋙ NumericalTuples.comparison ≅ 𝟭 EnumerableCarriers.Total :=
  NatIso.ofComponents (fun X => eqToIso (NumericalTuples.codedObject_unary X)) (by
    intro X Y f
    apply totalMap_ext
    intro z
    apply Subtype.ext
    let x := (NumericalTuples.pointEquiv (NumericalTuples.unary X)).symm z
    have hx : x.val = z.val := NumericalTuples.pointEquiv_symm_code (NumericalTuples.unary X) z
    have hsource : EnumerableCarriers.totalFunction
        (eqToIso (NumericalTuples.codedObject_unary X)).hom z = x :=
      Subtype.ext ((totalFunction_eqToHom (NumericalTuples.codedObject_unary X) z).trans hx.symm)
    have hm : EnumerableCarriers.totalFunction
        (NumericalTuples.comparison.map (unaryMap f)) z =
        NumericalTuples.pointEquiv (NumericalTuples.unary Y) (EnumerableCarriers.totalFunction f x) :=
      (congrArg (EnumerableCarriers.totalFunction (NumericalTuples.comparison.map (unaryMap f)))
        ((NumericalTuples.pointEquiv (NumericalTuples.unary X)).apply_symm_apply z)).symm.trans
          (NumericalTuples.comparisonMap_function (unaryMap f) x)
    have hl := congrArg Subtype.val
      (totalFunction_comp (NumericalTuples.comparison.map (unaryMap f))
        (eqToIso (NumericalTuples.codedObject_unary Y)).hom z)
    have hr := congrArg Subtype.val
      (totalFunction_comp (eqToIso (NumericalTuples.codedObject_unary X)).hom f z)
    exact hl.trans ((totalFunction_eqToHom (NumericalTuples.codedObject_unary Y)
      (EnumerableCarriers.totalFunction (NumericalTuples.comparison.map (unaryMap f)) z)).trans
        ((congrArg Subtype.val hm).trans
          (hr.trans (congrArg (fun x => (EnumerableCarriers.totalFunction f x).val) hsource)).symm)))

instance unaryComposite_isEquivalence : (unaryFunctor ⋙ NumericalTuples.comparison).IsEquivalence :=
  Functor.isEquivalence_of_iso unaryComparison.symm

instance unaryFunctor_isEquivalence : unaryFunctor.IsEquivalence :=
  Functor.isEquivalence_of_comp_right unaryFunctor NumericalTuples.comparison

instance unaryFunctor_preservesLimits : PreservesLimits unaryFunctor := inferInstance
instance unaryFunctor_preservesColimits : PreservesColimits unaryFunctor := inferInstance

/- The code comparison used below is a complete inference-algebra
isomorphism. Its concrete instance is supplied by Component. -/
section CodeFold
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
variable (P : Endofunctor.Algebra R.inference)
variable (e : P ≅ NumericalDerivation.codeAlgebra R)

def comparedInitial : IsInitial P := (NumericalDerivation.codeInitial R).ofIso e.symm

def comparedFoldHom (B : Endofunctor.Algebra R.inference) : P ⟶ B :=
  e.hom ≫ NumericalDerivation.codeFold R B

def comparedFold (B : Endofunctor.Algebra R.inference) : P.a.left ⟶ B.a.left :=
  (comparedFoldHom R P e B).f.left

theorem comparedFold_conclusion (B : Endofunctor.Algebra R.inference) :
    comparedFold R P e B ≫ B.a.hom = P.a.hom :=
  Over.w (comparedFoldHom R P e B).f

theorem comparedFold_constructor (B : Endofunctor.Algebra R.inference) :
    P.str.left ≫ comparedFold R P e B =
      (R.inference.map (comparedFoldHom R P e B).f).left ≫ B.str.left :=
  congrArg (fun h => h.left) (comparedFoldHom R P e B).h.symm

theorem comparedFold_unique (B : Endofunctor.Algebra R.inference)
    (f : P.a.left ⟶ B.a.left) (hf : f ≫ B.a.hom = P.a.hom)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str = P.str ≫ Over.homMk f hf) :
    f = comparedFold R P e B := by
  let m : P ⟶ B := ⟨Over.homMk f hf,hc⟩
  exact congrArg (fun k : P ⟶ B => k.f.left)
    ((comparedInitial R P e).hom_ext m (comparedFoldHom R P e B))

theorem comparedFold_algebra_unique (B : Endofunctor.Algebra R.inference) (m : P ⟶ B) :
    m = comparedFoldHom R P e B :=
  (comparedInitial R P e).hom_ext m _

theorem comparedFold_postcompose {B C : Endofunctor.Algebra R.inference} (h : B ⟶ C) :
    comparedFold R P e B ≫ h.f.left = comparedFold R P e C := by
  exact congrArg (fun k : P ⟶ C => k.f.left)
    ((comparedInitial R P e).hom_ext (comparedFoldHom R P e B ≫ h)
      (comparedFoldHom R P e C))

end CodeFold

section ActualInputs
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)

/-- The branch operation of an arbitrary target inference algebra. -/
def branch (B : Endofunctor.Algebra R.inference) (i : Fin (N + 1)) :
    R.ruleObject B.a i ⟶ B.a.left := Sigma.ι (R.ruleObject B.a) i ≫ B.str.left

theorem branch_conclusion (B : Endofunctor.Algebra R.inference) (i : Fin (N + 1)) :
    branch R B i ≫ B.a.hom = R.ruleConclusion B.a i := by
  rw [branch,Category.assoc,Over.w B.str]
  exact Sigma.ι_comp_desc _ i

/-- Every algebra morphism commutes with every ordered-rule branch. -/
theorem branch_natural {B C : Endofunctor.Algebra R.inference} (m : B ⟶ C)
    (i : Fin (N + 1)) :
    branch R B i ≫ m.f.left = R.ruleMap m.f i ≫ branch R C i := by
  have h := congrArg (fun k => Sigma.ι (R.ruleObject B.a) i ≫ k.left) m.h.symm
  simpa only [branch,RulePresentation.inference,Over.comp_left,Over.homMk_left,Category.assoc,
    Sigma.ι_map_assoc] using h

/-- Every nullary rule label has its prescribed value in every algebra. -/
def nullary (B : Endofunctor.Algebra R.inference) : R.instances 0 ⟶ B.a.left :=
  R.nullaryRule B.a ≫ branch R B 0

theorem nullary_conclusion (B : Endofunctor.Algebra R.inference) :
    nullary R B ≫ B.a.hom = R.conclusion 0 := by
  rw [nullary,Category.assoc,branch_conclusion,RulePresentation.ruleConclusion,
    ← Category.assoc,R.nullaryRule_fst,Category.id_comp]

theorem nullary_input_natural {B C : Endofunctor.Algebra R.inference} (m : B ⟶ C) :
    R.nullaryRule B.a ≫ R.ruleMap m.f 0 = R.nullaryRule C.a := by
  apply pullback.hom_ext
  · simp only [Category.assoc,R.ruleMap_fst,R.nullaryRule_fst]
  · exact terminal.hom_ext _ _

theorem nullary_natural {B C : Endofunctor.Algebra R.inference} (m : B ⟶ C) :
    nullary R B ≫ m.f.left = nullary R C := by
  calc
    _ = R.nullaryRule B.a ≫ (branch R B 0 ≫ m.f.left) := Category.assoc _ _ _
    _ = R.nullaryRule B.a ≫ (R.ruleMap m.f 0 ≫ branch R C 0) :=
      congrArg (fun k => R.nullaryRule B.a ≫ k) (branch_natural R m 0)
    _ = (R.nullaryRule B.a ≫ R.ruleMap m.f 0) ≫ branch R C 0 := (Category.assoc _ _ _).symm
    _ = R.nullaryRule C.a ≫ branch R C 0 :=
      congrArg (fun k => k ≫ branch R C 0) (nullary_input_natural R m)
    _ = nullary R C := rfl

theorem nullary_value_conclusion (B : Endofunctor.Algebra R.inference)
    (r : NumericalTuples.Point (R.instances 0)) :
    B.a.hom.toFun ((nullary R B).toFun r) = (R.conclusion 0).toFun r :=
  congrArg (fun f => f.toFun r) (nullary_conclusion R B)

end ActualInputs

namespace SelectedTrees
open ForkSyntax

/-- Values lie over their own conclusions. In particular the MP operation
accepts a value over p and a value over p implies q. -/
structure Operations (A B : Set ℕ) where
  Value : Formula → Type
  logical1 : ∀ p q, Value (H1 p q)
  logical2 : ∀ p q r, Value (H2 p q r)
  logical3 : ∀ p q, Value (H3 p q)
  positive : ∀ x, x ∈ A → Value (.atom x)
  negative : ∀ x, x ∈ B → Value (.neg (.atom x))
  mp : ∀ p q, Value p → Value (.imp p q) → Value q

/-- These are the constructor equations of a candidate map on valid
selected trees. Its existence as a numerical morphism is proved separately
by the code initial algebra, rather than by an ambient-code evaluator. -/
structure Evaluation {A B : Set ℕ} (O : Operations A B) where
  value : ∀ {t p}, Concludes A B t p → O.Value p
  logical1 : ∀ p q, value (Concludes.logical1 p q) = O.logical1 p q
  logical2 : ∀ p q r, value (Concludes.logical2 p q r) = O.logical2 p q r
  logical3 : ∀ p q, value (Concludes.logical3 p q) = O.logical3 p q
  positive : ∀ x (hx : x ∈ A), value (Concludes.positive hx) = O.positive x hx
  negative : ∀ x (hx : x ∈ B), value (Concludes.negative hx) = O.negative x hx
  mp : ∀ {t u p q} (ht : Concludes A B t p) (hu : Concludes A B u (.imp p q)),
    value (Concludes.mp ht hu) = O.mp p q (value ht) (value hu)

/-- Only algebra-operation naturality is supplied. The value over each
formula is mapped over its actual atom relabeling, with no injectivity
assumption on the atom map. -/
structure NaturalOperations {A B A' B' : Set ℕ} (O : Operations A B) (O' : Operations A' B')
    (f : ℕ → ℕ) (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B') where
  map : ∀ p, O.Value p → O'.Value (p.mapAtoms f)
  logical1 : ∀ p q, map (H1 p q) (O.logical1 p q) =
    O'.logical1 (p.mapAtoms f) (q.mapAtoms f)
  logical2 : ∀ p q r, map (H2 p q r) (O.logical2 p q r) =
    O'.logical2 (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f)
  logical3 : ∀ p q, map (H3 p q) (O.logical3 p q) =
    O'.logical3 (p.mapAtoms f) (q.mapAtoms f)
  positive : ∀ x (hx : x ∈ A), map (.atom x) (O.positive x hx) =
    O'.positive (f x) (ha x hx)
  negative : ∀ x (hx : x ∈ B), map (.neg (.atom x)) (O.negative x hx) =
    O'.negative (f x) (hb x hx)
  mp : ∀ p q (x : O.Value p) (y : O.Value (.imp p q)),
    map q (O.mp p q x y) =
      O'.mp (p.mapAtoms f) (q.mapAtoms f) (map p x) (map (.imp p q) y)

/-- Naturality is proved by induction on the actual valid selected
proof. No operation is applied to an invalid child or an unmatched pair. -/
theorem evaluation_natural {A B A' B' : Set ℕ} {O : Operations A B} {O' : Operations A' B'}
    (E : Evaluation O) (E' : Evaluation O') (f : ℕ → ℕ)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
    (h : NaturalOperations O O' f ha hb) {t p} (ht : Concludes A B t p) :
    h.map p (E.value ht) = E'.value (ht.mapAtoms f ha hb) := by
  induction ht with
  | logical1 p q =>
    exact (congrArg (h.map (H1 p q)) (E.logical1 p q)).trans
      ((h.logical1 p q).trans (E'.logical1 (p.mapAtoms f) (q.mapAtoms f)).symm)
  | logical2 p q r =>
    exact (congrArg (h.map (H2 p q r)) (E.logical2 p q r)).trans
      ((h.logical2 p q r).trans
        (E'.logical2 (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f)).symm)
  | logical3 p q =>
    exact (congrArg (h.map (H3 p q)) (E.logical3 p q)).trans
      ((h.logical3 p q).trans (E'.logical3 (p.mapAtoms f) (q.mapAtoms f)).symm)
  | @positive x hx =>
    exact (congrArg (h.map (.atom x)) (E.positive x hx)).trans
      ((h.positive x hx).trans (E'.positive (f x) (ha x hx)).symm)
  | @negative x hx =>
    exact (congrArg (h.map (.neg (.atom x))) (E.negative x hx)).trans
      ((h.negative x hx).trans (E'.negative (f x) (hb x hx)).symm)
  | @mp t u p q ht hu iht ihu =>
    exact (congrArg (h.map q) (E.mp ht hu)).trans
      ((h.mp p q (E.value ht) (E.value hu)).trans
        ((congrArg₂ (O'.mp (p.mapAtoms f) (q.mapAtoms f)) iht ihu).trans
          (E'.mp (ht.mapAtoms f ha hb) (hu.mapAtoms f ha hb)).symm))

/-- Constructor-compatible values on the selected valid trees are unique. -/
theorem evaluation_unique {A B : Set ℕ} {O : Operations A B}
    (E E' : Evaluation O) {t p} (ht : Concludes A B t p) : E.value ht = E'.value ht := by
  induction ht with
  | logical1 p q => exact (E.logical1 p q).trans (E'.logical1 p q).symm
  | logical2 p q r => exact (E.logical2 p q r).trans (E'.logical2 p q r).symm
  | logical3 p q => exact (E.logical3 p q).trans (E'.logical3 p q).symm
  | @positive x hx => exact (E.positive x hx).trans (E'.positive x hx).symm
  | @negative x hx => exact (E.negative x hx).trans (E'.negative x hx).symm
  | @mp t u p q ht hu iht ihu =>
    exact (E.mp ht hu).trans
      ((congrArg₂ (O.mp p q) iht ihu).trans (E'.mp ht hu).symm)

end SelectedTrees

section ComponentFolds
open ForkSyntax
variable (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))

/-- The source is the original six-tag proof carrier. The complete code
algebra comparison supplies its initiality for arbitrary numerical targets. -/
def foldHom (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    Component.algebra A B hA hB ⟶ D :=
  comparedFoldHom (Component.rules A B hA hB) (Component.algebra A B hA hB)
    (Component.algebraIso A B hA hB) D

def fold (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    Component.proofObject A B hA hB ⟶ D.a.left := (foldHom A B hA hB D).f.left

theorem fold_conclusion (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    fold A B hA hB D ≫ D.a.hom = Component.conclusion A B hA hB :=
  Over.w (foldHom A B hA hB D).f

theorem fold_constructor (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    (Component.algebra A B hA hB).str.left ≫ fold A B hA hB D =
      ((Component.rules A B hA hB).inference.map (foldHom A B hA hB D).f).left ≫ D.str.left :=
  congrArg (fun h => h.left) (foldHom A B hA hB D).h.symm

theorem fold_unique (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    (u : Component.proofObject A B hA hB ⟶ D.a.left)
    (hu : u ≫ D.a.hom = Component.conclusion A B hA hB)
    (hc : (Component.rules A B hA hB).inference.map (Over.homMk u hu) ≫ D.str =
      (Component.algebra A B hA hB).str ≫ Over.homMk u hu) :
    u = fold A B hA hB D :=
  comparedFold_unique (Component.rules A B hA hB) (Component.algebra A B hA hB)
    (Component.algebraIso A B hA hB) D u hu hc

/-- The conclusion fiber of a target algebra can be empty. Operations
are evaluated only on the matched fibers prescribed by the inference functor. -/
def Value (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) (p : Formula) :=
  {z : NumericalTuples.Point D.a.left // (D.a.hom.toFun z).val = p.encode}

def foldValue (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    {t p} (ht : Concludes A B t p) : Value A B hA hB D p := by
  let x := Component.proofPoint A B hA hB t ⟨p,ht⟩
  refine ⟨(fold A B hA hB D).toFun x,?_⟩
  have h := congrArg (fun f => (f.toFun x).val) (fold_conclusion A B hA hB D)
  exact h.trans ((Component.conclusion_value A B hA hB x).trans
    (conclusionCode_of_concludes ht))

def targetNullary (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    (r : NumericalTuples.Point ((Component.rules A B hA hB).instances 0))
    (p : Formula)
    (hr : (((Component.rules A B hA hB).conclusion 0).toFun r).val = p.encode) :
    Value A B hA hB D p :=
  ⟨(nullary (Component.rules A B hA hB) D).toFun r,
    (congrArg Subtype.val (nullary_value_conclusion (Component.rules A B hA hB) D r)).trans hr⟩

def targetMP (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    (p q : Formula) (x : Value A B hA hB D p) (y : Value A B hA hB D (.imp p q)) :
    Value A B hA hB D q := by
  let u := Component.mpInputPoint A B hA hB D.a p q x.val y.val x.property y.property
  refine ⟨(branch (Component.rules A B hA hB) D 2).toFun u,?_⟩
  exact (congrArg (fun f => (f.toFun u).val)
    (branch_conclusion (Component.rules A B hA hB) D 2)).trans
      (Component.mpInputPoint_conclusion A B hA hB D.a p q x.val y.val x.property y.property)

/-- These operations are induced by the supplied numerical inference
algebra. Their domains are the original premise-matching pullbacks. -/
def targetOperations (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    SelectedTrees.Operations A B where
  Value := Value A B hA hB D
  logical1 p q := targetNullary A B hA hB D (Component.logical1Label A B hA hB p q) (H1 p q)
    (Component.logical1Label_conclusion A B hA hB p q)
  logical2 p q r := targetNullary A B hA hB D (Component.logical2Label A B hA hB p q r) (H2 p q r)
    (Component.logical2Label_conclusion A B hA hB p q r)
  logical3 p q := targetNullary A B hA hB D (Component.logical3Label A B hA hB p q) (H3 p q)
    (Component.logical3Label_conclusion A B hA hB p q)
  positive x hx := targetNullary A B hA hB D (Component.positiveLabel A B hA hB x hx) (.atom x)
    (Component.positiveLabel_conclusion A B hA hB x hx)
  negative x hx := targetNullary A B hA hB D (Component.negativeLabel A B hA hB x hx) (.neg (.atom x))
    (Component.negativeLabel_conclusion A B hA hB x hx)
  mp := targetMP A B hA hB D

theorem fold_nullary (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    (r : NumericalTuples.Point ((Component.rules A B hA hB).instances 0))
    {t p} (ht : Concludes A B t p)
    (hr : (((Component.rules A B hA hB).conclusion 0).toFun r).val = p.encode)
    (hs : (nullary (Component.rules A B hA hB) (Component.algebra A B hA hB)).toFun r =
      Component.proofPoint A B hA hB t ⟨p,ht⟩) :
    foldValue A B hA hB D ht = targetNullary A B hA hB D r p hr := by
  apply Subtype.ext
  have h := congrArg (fun f => f.toFun r)
    (nullary_natural (Component.rules A B hA hB) (foldHom A B hA hB D))
  exact (congrArg (fold A B hA hB D).toFun hs.symm).trans h

private theorem over_point_conclusion {Q Q' : Over Component.formulaObject} (m : Q ⟶ Q')
    (x : NumericalTuples.Point Q.left) (p : Formula) (hx : (Q.hom.toFun x).val = p.encode) :
    (Q'.hom.toFun (m.left.toFun x)).val = p.encode :=
  (congrArg (fun k => (k.toFun x).val) (Over.w m)).trans hx

private theorem mp_node_natural {Q Q' : Over Component.formulaObject} (m : Q ⟶ Q')
    (p q : Formula) (x y : NumericalTuples.Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (ForkSyntax.Formula.imp p q).encode) :
    ((Component.rules A B hA hB).inference.map m).left.toFun
      (Component.mpNodePoint A B hA hB Q p q x y hx hy) =
    Component.mpNodePoint A B hA hB Q' p q (m.left.toFun x) (m.left.toFun y)
      (over_point_conclusion m x p hx) (over_point_conclusion m y (.imp p q) hy) :=
  Component.nodeInput_map A B hA hB m (.mp p q x y hx hy)

theorem fold_mp (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
    {t u p q} (ht : Concludes A B t p) (hu : Concludes A B u (.imp p q)) :
    foldValue A B hA hB D (Concludes.mp ht hu) =
      targetMP A B hA hB D p q (foldValue A B hA hB D ht) (foldValue A B hA hB D hu) := by
  apply Subtype.ext
  let x := Component.proofPoint A B hA hB t ⟨p,ht⟩
  let y := Component.proofPoint A B hA hB u ⟨.imp p q,hu⟩
  let hx := Component.proofPoint_conclusion A B hA hB ht
  let hy := Component.proofPoint_conclusion A B hA hB hu
  let v := Component.mpNodePoint A B hA hB (Component.algebra A B hA hB).a p q x y hx hy
  have hs := Component.algebra_mp A B hA hB ht hu
  have hc := congrArg (fun k => k.toFun v) (fold_constructor A B hA hB D)
  have hn := mp_node_natural A B hA hB (foldHom A B hA hB D).f p q x y hx hy
  exact (congrArg (fold A B hA hB D).toFun hs.symm).trans
    (hc.trans (congrArg D.str.left.toFun hn))

/-- All six equations are derived from the actual algebra morphism.
The proof labels and ordered children are those of the old proof carrier. -/
def foldEvaluation (D : Endofunctor.Algebra (Component.rules A B hA hB).inference) :
    SelectedTrees.Evaluation (targetOperations A B hA hB D) where
  value := foldValue A B hA hB D
  logical1 p q := fold_nullary A B hA hB D (Component.logical1Label A B hA hB p q)
    (Concludes.logical1 p q) (Component.logical1Label_conclusion A B hA hB p q)
    (Component.algebra_logical1 A B hA hB p q)
  logical2 p q r := fold_nullary A B hA hB D (Component.logical2Label A B hA hB p q r)
    (Concludes.logical2 p q r) (Component.logical2Label_conclusion A B hA hB p q r)
    (Component.algebra_logical2 A B hA hB p q r)
  logical3 p q := fold_nullary A B hA hB D (Component.logical3Label A B hA hB p q)
    (Concludes.logical3 p q) (Component.logical3Label_conclusion A B hA hB p q)
    (Component.algebra_logical3 A B hA hB p q)
  positive x hx := fold_nullary A B hA hB D (Component.positiveLabel A B hA hB x hx)
    (Concludes.positive hx) (Component.positiveLabel_conclusion A B hA hB x hx)
    (Component.algebra_positive A B hA hB x hx)
  negative x hx := fold_nullary A B hA hB D (Component.negativeLabel A B hA hB x hx)
    (Concludes.negative hx) (Component.negativeLabel_conclusion A B hA hB x hx)
    (Component.algebra_negative A B hA hB x hx)
  mp := fold_mp A B hA hB D


private theorem native_value_concludes {p : Formula}
    (x : Value A B hA hB (Component.algebra A B hA hB) p) :
    Concludes A B (ProofTree.decode x.val.val) p := by
  have ht := Component.proofAt_concludes A B hA hB x.val
  have hx : ((Component.conclusion A B hA hB).toFun x.val).val = p.encode := x.property
  change Concludes A B (ProofTree.decode x.val.val)
    (Formula.decode (((Component.conclusion A B hA hB).toFun x.val).val)) at ht
  rw [hx,Formula.decode_encode] at ht
  exact ht

private theorem native_value_point {p : Formula}
    (x : Value A B hA hB (Component.algebra A B hA hB) p) :
    x.val = Component.proofPoint A B hA hB (ProofTree.decode x.val.val)
      ⟨p,native_value_concludes A B hA hB x⟩ :=
  Subtype.ext (ProofTree.encode_decode x.val.val).symm

private theorem mp_node_congr (Q : Over Component.formulaObject) (p q : Formula)
    (x₀ y₀ x₁ y₁ : NumericalTuples.Point Q.left)
    (hx₀ : (Q.hom.toFun x₀).val = p.encode) (hy₀ : (Q.hom.toFun y₀).val = (ForkSyntax.Formula.imp p q).encode)
    (hx₁ : (Q.hom.toFun x₁).val = p.encode) (hy₁ : (Q.hom.toFun y₁).val = (ForkSyntax.Formula.imp p q).encode)
    (ex : x₀ = x₁) (ey : y₀ = y₁) :
    Component.mpNodePoint A B hA hB Q p q x₀ y₀ hx₀ hy₀ =
      Component.mpNodePoint A B hA hB Q p q x₁ y₁ hx₁ hy₁ := by
  subst x₁
  subst y₁
  rfl

private theorem native_mp_from_points {t u : ProofTree} {p q : Formula}
    (ht : Concludes A B t p) (hu : Concludes A B u (.imp p q))
    (x : Value A B hA hB (Component.algebra A B hA hB) p)
    (y : Value A B hA hB (Component.algebra A B hA hB) (.imp p q))
    (ex : x.val = Component.proofPoint A B hA hB t ⟨p,ht⟩)
    (ey : y.val = Component.proofPoint A B hA hB u ⟨.imp p q,hu⟩) :
    (targetMP A B hA hB (Component.algebra A B hA hB) p q x y).val =
      Component.proofPoint A B hA hB (.mp t u) ⟨q,Concludes.mp ht hu⟩ := by
  have hi := mp_node_congr A B hA hB (Component.algebra A B hA hB).a p q x.val y.val
    (Component.proofPoint A B hA hB t ⟨p,ht⟩) (Component.proofPoint A B hA hB u ⟨.imp p q,hu⟩)
    x.property y.property (Component.proofPoint_conclusion A B hA hB ht)
    (Component.proofPoint_conclusion A B hA hB hu) ex ey
  exact (congrArg (Component.algebra A B hA hB).str.left.toFun hi).trans
    (Component.algebra_mp A B hA hB ht hu)

/-- The conclusion is the explicit unary presentation of the old
carrier-total conclusion program, on the same proof words. -/
theorem conclusion_unary : Component.conclusion A B hA hB =
    unaryMap (⟨ForkSyntax.conclusionArrow A B hA hB,
      ForkSyntax.conclusionArrow_total A B hA hB⟩ :
      (⟨ForkSyntax.proofCarrier A B hA hB⟩ : EnumerableCarriers.Total) ⟶
        (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total)) := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  have h := (EnumerableCarriers.mem_totalFromFunction ForkSyntax.conclusionCode
    ForkSyntax.conclusionCode_computable (fun n _ => Set.mem_univ (ForkSyntax.conclusionCode n)) x.val _).mp
    (EnumerableCarriers.totalFunction_mem
      (⟨ForkSyntax.conclusionArrow A B hA hB,ForkSyntax.conclusionArrow_total A B hA hB⟩ :
        (⟨ForkSyntax.proofCarrier A B hA hB⟩ : EnumerableCarriers.Total) ⟶
          (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total)) x)
  exact (Component.conclusion_value A B hA hB x).trans h.2.symm

theorem algebraHom_node
    {D E : Endofunctor.Algebra (Component.rules A B hA hB).inference} (m : D ⟶ E)
    (n : Component.Node A B D.a) :
    m.f.left.toFun (D.str.left.toFun (Component.nodeInput A B hA hB D.a n)) =
      E.str.left.toFun (Component.nodeInput A B hA hB E.a (Component.nodeMap A B m.f n)) := by
  have h := congrArg (fun f => f.left.toFun (Component.nodeInput A B hA hB D.a n)) m.h.symm
  exact h.trans (congrArg E.str.left.toFun (Component.nodeInput_map A B hA hB m.f n))

end ComponentFolds

section Relabeling
open ForkSyntax
variable {A B A' B' : Set ℕ}
variable (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
variable (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
variable (f : ℕ → ℕ) (hf : Computable f)
variable (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')

include ha hb in
theorem relabel_valid {t : ProofTree} (ht : ProofTree.Valid A B t) :
    ProofTree.Valid A' B' (t.mapAtoms f) := by
  obtain ⟨p,hp⟩ := ht
  exact ⟨p.mapAtoms f,hp.mapAtoms f ha hb⟩

/-- This is the old recursive relabeling of the same six-tag proof
words. It is total on the valid source carrier. -/
def proofMap : Component.proofObject A B hA hB ⟶ Component.proofObject A' B' hA' hB' where
  toFun x := Component.proofPoint A' B' hA' hB' ((ProofTree.decode x.val).mapAtoms f)
    (relabel_valid f ha hb ((mem_proofCarrier A B hA hB x.val).mp x.property))
  represented := ⟨fun n => Part.some (proofRelabelCode f n),proofRelabelCode_computable hf,fun _ => rfl⟩

theorem proofMap_value (x : NumericalTuples.Point (Component.proofObject A B hA hB)) :
    ((proofMap hA hB hA' hB' f hf ha hb).toFun x).val = proofRelabelCode f x.val := rfl

theorem proofMap_selected (t : ProofTree) (ht : ProofTree.Valid A B t) :
    (proofMap hA hB hA' hB' f hf ha hb).toFun (Component.proofPoint A B hA hB t ht) =
      Component.proofPoint A' B' hA' hB' (t.mapAtoms f) (relabel_valid f ha hb ht) := by
  apply Subtype.ext
  change proofRelabelCode f t.encode = (t.mapAtoms f).encode
  rw [proofRelabelCode,ProofTree.decode_encode]

def formulaMap : Component.formulaObject ⟶ Component.formulaObject where
  toFun x := ⟨Formula.sigma f x.val,Set.mem_univ _⟩
  represented := ⟨fun n => Part.some (Formula.sigma f n),Formula.sigma_computable hf,fun _ => rfl⟩

theorem formulaMap_encoded (p : Formula) :
    (formulaMap f hf).toFun ⟨p.encode,Set.mem_univ _⟩ =
      ⟨(p.mapAtoms f).encode,Set.mem_univ _⟩ :=
  Subtype.ext (sigma_encode f p)

theorem proofMap_conclusion : proofMap hA hB hA' hB' f hf ha hb ≫ Component.conclusion A' B' hA' hB' =
    Component.conclusion A B hA hB ≫ formulaMap f hf := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  have hd := Component.conclusion_value A' B' hA' hB'
    ((proofMap hA hB hA' hB' f hf ha hb).toFun x)
  have hs := Component.conclusion_value A B hA hB x
  exact hd.trans ((conclusion_relabel f ha hb x.val
    ((mem_proofCarrier A B hA hB x.val).mp x.property)).trans
      (congrArg (Formula.sigma f) hs).symm)

/-- The numerical relabeling is exactly the explicit unary presentation
of the original total recursive proof morphism. -/
theorem proofMap_unary : proofMap hA hB hA' hB' f hf ha hb =
    unaryMap (⟨ForkSyntax.proofMap hA hB hA' hB' f hf ha hb,
      ForkSyntax.proofMap_total hA hB hA' hB' f hf ha hb⟩ :
      (⟨ForkSyntax.proofCarrier A B hA hB⟩ : EnumerableCarriers.Total) ⟶
        (⟨ForkSyntax.proofCarrier A' B' hA' hB'⟩ : EnumerableCarriers.Total)) := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact ((ForkSyntax.mem_proofMap hA hB hA' hB' f hf ha hb x.val _).mp
    (EnumerableCarriers.totalFunction_mem
      (⟨ForkSyntax.proofMap hA hB hA' hB' f hf ha hb,
        ForkSyntax.proofMap_total hA hB hA' hB' f hf ha hb⟩ :
        (⟨ForkSyntax.proofCarrier A B hA hB⟩ : EnumerableCarriers.Total) ⟶
          (⟨ForkSyntax.proofCarrier A' B' hA' hB'⟩ : EnumerableCarriers.Total)) x)).2.symm

theorem formulaMap_unary : formulaMap f hf =
    unaryMap (⟨ForkSyntax.natArrow (Formula.sigma f) (Formula.sigma_computable hf),
      ForkSyntax.natArrow_total (Formula.sigma f) (Formula.sigma_computable hf)⟩ :
      (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) ⟶
        (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total)) := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  exact ((ForkSyntax.mem_natArrow (Formula.sigma f) (Formula.sigma_computable hf) x.val _).mp
    (EnumerableCarriers.totalFunction_mem
      (⟨ForkSyntax.natArrow (Formula.sigma f) (Formula.sigma_computable hf),
        ForkSyntax.natArrow_total (Formula.sigma f) (Formula.sigma_computable hf)⟩ :
        (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) ⟶
          (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total)) x)).symm


theorem formulaMap_id : formulaMap id Computable.id = 𝟙 Component.formulaObject := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  simp only [formulaMap,Formula.sigma,Formula.mapAtoms_id,Formula.encode_decode]
  rfl

theorem proofTree_mapAtoms_id (t : ProofTree) : t.mapAtoms id = t := by
  induction t with
  | logical1 | logical2 | logical3 => simp only [ProofTree.mapAtoms,Formula.mapAtoms_id]
  | positive | negative => rfl
  | mp t u ht hu => exact congrArg₂ ProofTree.mp ht hu

end Relabeling

theorem proofMap_id (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) :
    proofMap hA hB hA hB id Computable.id (fun _ hx => hx) (fun _ hx => hx) =
      𝟙 (Component.proofObject A B hA hB) := by
  apply NumericalTuples.Map.ext
  funext x
  apply Subtype.ext
  change ForkSyntax.proofRelabelCode id x.val = x.val
  simp only [ForkSyntax.proofRelabelCode,proofTree_mapAtoms_id,ForkSyntax.ProofTree.encode_decode]

theorem point_relabel_conclusion {Q Q' : Over Component.formulaObject}
    (f : ℕ → ℕ) (hf : Computable f) (h : Q.left ⟶ Q'.left)
    (hc : h ≫ Q'.hom = Q.hom ≫ formulaMap f hf) (p : ForkSyntax.Formula)
    (x : NumericalTuples.Point Q.left) (hx : (Q.hom.toFun x).val = p.encode) :
    (Q'.hom.toFun (h.toFun x)).val = (p.mapAtoms f).encode :=
  (congrArg (fun k => (k.toFun x).val) hc).trans
    ((congrArg (ForkSyntax.Formula.sigma f) hx).trans (ForkSyntax.sigma_encode f p))

def mapNode {A B A' B' : Set ℕ} {Q Q' : Over Component.formulaObject}
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
    (h : Q.left ⟶ Q'.left) (hc : h ≫ Q'.hom = Q.hom ≫ formulaMap f hf) :
    Component.Node A B Q → Component.Node A' B' Q'
  | .logical1 p q => .logical1 (p.mapAtoms f) (q.mapAtoms f)
  | .logical2 p q r => .logical2 (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f)
  | .logical3 p q => .logical3 (p.mapAtoms f) (q.mapAtoms f)
  | .positive x hx => .positive (f x) (ha x hx)
  | .negative x hx => .negative (f x) (hb x hx)
  | .mp p q x y hx hy => .mp (p.mapAtoms f) (q.mapAtoms f) (h.toFun x) (h.toFun y)
    (point_relabel_conclusion f hf h hc p x hx)
    (point_relabel_conclusion f hf h hc (.imp p q) y hy)

private theorem node_mp_congr {A B : Set ℕ} (Q : Over Component.formulaObject)
    (p q : ForkSyntax.Formula) (x₀ y₀ x₁ y₁ : NumericalTuples.Point Q.left)
    (hx₀ : (Q.hom.toFun x₀).val = p.encode) (hy₀ : (Q.hom.toFun y₀).val = (ForkSyntax.Formula.imp p q).encode)
    (hx₁ : (Q.hom.toFun x₁).val = p.encode) (hy₁ : (Q.hom.toFun y₁).val = (ForkSyntax.Formula.imp p q).encode)
    (ex : x₀ = x₁) (ey : y₀ = y₁) :
    (Component.Node.mp p q x₀ y₀ hx₀ hy₀ : Component.Node A B Q) =
      Component.Node.mp p q x₁ y₁ hx₁ hy₁ := by
  subst x₁
  subst y₁
  rfl

/-- The node relabeling respects a commuting square of actual carrier
maps over the fixed formula relabeling. -/
theorem mapNode_square {A B A' B' : Set ℕ}
    {Q₀ Q₁ P₀ P₁ : Over Component.formulaObject}
    (f : ℕ → ℕ) (hf : Computable f)
    (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
    (e₀ : Q₀ ⟶ P₀) (e₁ : Q₁ ⟶ P₁)
    (h₀ : Q₀.left ⟶ Q₁.left) (h₁ : P₀.left ⟶ P₁.left)
    (hc₀ : h₀ ≫ Q₁.hom = Q₀.hom ≫ formulaMap f hf)
    (hc₁ : h₁ ≫ P₁.hom = P₀.hom ≫ formulaMap f hf)
    (he : h₀ ≫ e₁.left = e₀.left ≫ h₁) (n : Component.Node A B Q₀) :
    Component.nodeMap A' B' e₁ (mapNode f hf ha hb h₀ hc₀ n) =
      mapNode f hf ha hb h₁ hc₁ (Component.nodeMap A B e₀ n) := by
  cases n with
  | logical1 | logical2 | logical3 | positive | negative => rfl
  | mp p q x y hx hy =>
    apply node_mp_congr
    · exact congrArg (fun k => k.toFun x) he
    · exact congrArg (fun k => k.toFun y) he

section RelabeledFolds
open ForkSyntax
variable {A B A' B' : Set ℕ}
variable (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
variable (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
variable (D : Endofunctor.Algebra (Component.rules A B hA hB).inference)
variable (D' : Endofunctor.Algebra (Component.rules A' B' hA' hB').inference)
variable (f : ℕ → ℕ) (hf : Computable f)
variable (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
variable (h : D.a.left ⟶ D'.a.left)
variable (hc : h ≫ D'.a.hom = D.a.hom ≫ formulaMap f hf)

/-- The map of target conclusion fibers is the supplied carrier morphism,
with its proved conclusion square. -/
def mapValue (p : Formula) (x : Value A B hA hB D p) :
    Value A' B' hA' hB' D' (p.mapAtoms f) := by
  refine ⟨h.toFun x.val,?_⟩
  exact (congrArg (fun k => (k.toFun x.val).val) hc).trans
    ((congrArg (Formula.sigma f) x.property).trans (sigma_encode f p))

/-- These six equations express target-algebra naturality at the original
five nullary branches and the premise-matched MP branch. They do not refer
to the proof folds whose naturality is proved below. -/
structure AlgebraNaturality : Prop where
  logical1 : ∀ p q,
    mapValue hA hB hA' hB' D D' f hf h hc (H1 p q)
        ((targetOperations A B hA hB D).logical1 p q) =
      (targetOperations A' B' hA' hB' D').logical1 (p.mapAtoms f) (q.mapAtoms f)
  logical2 : ∀ p q r,
    mapValue hA hB hA' hB' D D' f hf h hc (H2 p q r)
        ((targetOperations A B hA hB D).logical2 p q r) =
      (targetOperations A' B' hA' hB' D').logical2 (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f)
  logical3 : ∀ p q,
    mapValue hA hB hA' hB' D D' f hf h hc (H3 p q)
        ((targetOperations A B hA hB D).logical3 p q) =
      (targetOperations A' B' hA' hB' D').logical3 (p.mapAtoms f) (q.mapAtoms f)
  positive : ∀ x (hx : x ∈ A),
    mapValue hA hB hA' hB' D D' f hf h hc (.atom x)
        ((targetOperations A B hA hB D).positive x hx) =
      (targetOperations A' B' hA' hB' D').positive (f x) (ha x hx)
  negative : ∀ x (hx : x ∈ B),
    mapValue hA hB hA' hB' D D' f hf h hc (.neg (.atom x))
        ((targetOperations A B hA hB D).negative x hx) =
      (targetOperations A' B' hA' hB' D').negative (f x) (hb x hx)
  mp : ∀ p q (x : Value A B hA hB D p) (y : Value A B hA hB D (.imp p q)),
    mapValue hA hB hA' hB' D D' f hf h hc q (targetMP A B hA hB D p q x y) =
      targetMP A' B' hA' hB' D' (p.mapAtoms f) (q.mapAtoms f)
        (mapValue hA hB hA' hB' D D' f hf h hc p x)
        (mapValue hA hB hA' hB' D D' f hf h hc (.imp p q) y)

def relabelNode : Component.Node A B D.a → Component.Node A' B' D'.a :=
  mapNode f hf ha hb h hc

/-- Operation naturality holds on every actual input, by its complete
root decomposition. The target map and its conclusion square are fixed. -/
theorem node_natural (hn : AlgebraNaturality hA hB hA' hB' D D' f hf ha hb h hc)
    (n : Component.Node A B D.a) :
    h.toFun (D.str.left.toFun (Component.nodeInput A B hA hB D.a n)) =
      D'.str.left.toFun (Component.nodeInput A' B' hA' hB' D'.a
        (relabelNode hA hB hA' hB' D D' f hf ha hb h hc n)) := by
  cases n with
  | logical1 p q => exact congrArg Subtype.val (hn.logical1 p q)
  | logical2 p q r => exact congrArg Subtype.val (hn.logical2 p q r)
  | logical3 p q => exact congrArg Subtype.val (hn.logical3 p q)
  | positive x hx => exact congrArg Subtype.val (hn.positive x hx)
  | negative x hx => exact congrArg Subtype.val (hn.negative x hx)
  | mp p q x y hx hy => exact congrArg Subtype.val (hn.mp p q ⟨x,hx⟩ ⟨y,hy⟩)

theorem algebraNaturalityOfNodes
    (hn : ∀ n : Component.Node A B D.a,
      h.toFun (D.str.left.toFun (Component.nodeInput A B hA hB D.a n)) =
        D'.str.left.toFun (Component.nodeInput A' B' hA' hB' D'.a
          (relabelNode hA hB hA' hB' D D' f hf ha hb h hc n))) :
    AlgebraNaturality hA hB hA' hB' D D' f hf ha hb h hc where
  logical1 p q := Subtype.ext (hn (.logical1 p q))
  logical2 p q r := Subtype.ext (hn (.logical2 p q r))
  logical3 p q := Subtype.ext (hn (.logical3 p q))
  positive x hx := Subtype.ext (hn (.positive x hx))
  negative x hx := Subtype.ext (hn (.negative x hx))
  mp p q x y := Subtype.ext (hn (.mp p q x.val y.val x.property y.property))

def selectedNaturality (hn : AlgebraNaturality hA hB hA' hB' D D' f hf ha hb h hc) :
    SelectedTrees.NaturalOperations (targetOperations A B hA hB D)
      (targetOperations A' B' hA' hB' D') f ha hb where
  map := mapValue hA hB hA' hB' D D' f hf h hc
  logical1 := hn.logical1
  logical2 := hn.logical2
  logical3 := hn.logical3
  positive := hn.positive
  negative := hn.negative
  mp := hn.mp

theorem fold_natural_selected (hn : AlgebraNaturality hA hB hA' hB' D D' f hf ha hb h hc)
    {t p} (ht : Concludes A B t p) :
    h.toFun ((fold A B hA hB D).toFun (Component.proofPoint A B hA hB t ⟨p,ht⟩)) =
      (fold A' B' hA' hB' D').toFun
        (Component.proofPoint A' B' hA' hB' (t.mapAtoms f) ⟨p.mapAtoms f,ht.mapAtoms f ha hb⟩) :=
  congrArg Subtype.val
    (SelectedTrees.evaluation_natural (foldEvaluation A B hA hB D)
      (foldEvaluation A' B' hA' hB' D') f ha hb
      (selectedNaturality hA hB hA' hB' D D' f hf ha hb h hc hn) ht)

/-- The actual numerical folds commute with the actual recursive proof
relabeling. This applies in particular to each arrow of the fork. -/
theorem fold_natural (hn : AlgebraNaturality hA hB hA' hB' D D' f hf ha hb h hc) :
    fold A B hA hB D ≫ h = proofMap hA hB hA' hB' f hf ha hb ≫ fold A' B' hA' hB' D' := by
  apply NumericalTuples.Map.ext
  funext x
  obtain ⟨p,hp⟩ := (mem_proofCarrier A B hA hB x.val).mp x.property
  let t := ProofTree.decode x.val
  let y := Component.proofPoint A B hA hB t ⟨p,hp⟩
  have hy : y = x := Subtype.ext (ProofTree.encode_decode x.val)
  have hs := fold_natural_selected hA hB hA' hB' D D' f hf ha hb h hc hn hp
  have hm := proofMap_selected hA hB hA' hB' f hf ha hb t ⟨p,hp⟩
  have hh : (fold A B hA hB D ≫ h).toFun y =
      (proofMap hA hB hA' hB' f hf ha hb ≫ fold A' B' hA' hB' D').toFun y :=
    hs.trans (congrArg (fold A' B' hA' hB' D').toFun hm.symm)
  exact (congrArg (fun z => (fold A B hA hB D ≫ h).toFun z) hy).symm.trans
    (hh.trans (congrArg
      (fun z => (proofMap hA hB hA' hB' f hf ha hb ≫ fold A' B' hA' hB' D').toFun z) hy))

end RelabeledFolds

private theorem iso_point_injective {X Y : NumericalTuples.Object} (e : X ≅ Y) :
    Function.Injective e.hom.toFun := by
  intro x y h
  have hx := congrArg (fun f => f.toFun x) e.hom_inv_id
  have hy := congrArg (fun f => f.toFun y) e.hom_inv_id
  exact hx.symm.trans ((congrArg e.inv.toFun h).trans hy)

section IsoNaturality
open ForkSyntax
variable {A B A' B' : Set ℕ}
variable (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
variable (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
variable {D₀ E₀ : Endofunctor.Algebra (Component.rules A B hA hB).inference}
variable {D₁ E₁ : Endofunctor.Algebra (Component.rules A' B' hA' hB').inference}
variable (e₀ : D₀ ≅ E₀) (e₁ : D₁ ≅ E₁) (f : ℕ → ℕ) (hf : Computable f)
variable (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')
variable (hD : D₀.a.left ⟶ D₁.a.left) (hE : E₀.a.left ⟶ E₁.a.left)
variable (hcD : hD ≫ D₁.a.hom = D₀.a.hom ≫ formulaMap f hf)
variable (hcE : hE ≫ E₁.a.hom = E₀.a.hom ≫ formulaMap f hf)
variable (he : hD ≫ e₁.hom.f.left = e₀.hom.f.left ≫ hE)

include e₀ e₁ he in
theorem algebraNaturalityOfIso
    (hn : AlgebraNaturality hA hB hA' hB' E₀ E₁ f hf ha hb hE hcE) :
    AlgebraNaturality hA hB hA' hB' D₀ D₁ f hf ha hb hD hcD := by
  apply algebraNaturalityOfNodes hA hB hA' hB' D₀ D₁ f hf ha hb hD hcD
  intro n
  let e : D₁.a.left ≅ E₁.a.left :=
    (Over.forget Component.formulaObject).mapIso
      ((Endofunctor.Algebra.forget (Component.rules A' B' hA' hB').inference).mapIso e₁)
  apply iso_point_injective e
  have hs := mapNode_square f hf ha hb e₀.hom.f e₁.hom.f hD hE hcD hcE he n
  exact (congrArg (fun k => k.toFun (D₀.str.left.toFun (Component.nodeInput A B hA hB D₀.a n))) he).trans
    ((congrArg hE.toFun (algebraHom_node A B hA hB e₀.hom n)).trans
      ((node_natural hA hB hA' hB' E₀ E₁ f hf ha hb hE hcE hn (Component.nodeMap A B e₀.hom.f n)).trans
        ((congrArg (fun m => E₁.str.left.toFun (Component.nodeInput A' B' hA' hB' E₁.a m)) hs.symm).trans
          (algebraHom_node A' B' hA' hB' e₁.hom (mapNode f hf ha hb hD hcD n)).symm)))
end IsoNaturality

section NativeNaturality
open ForkSyntax
variable {A B A' B' : Set ℕ}
variable (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
variable (hA' : REPred (· ∈ A')) (hB' : REPred (· ∈ B'))
variable (f : ℕ → ℕ) (hf : Computable f)
variable (ha : ∀ x ∈ A, f x ∈ A') (hb : ∀ x ∈ B, f x ∈ B')

private theorem native_nullary_natural
    (r : NumericalTuples.Point ((Component.rules A B hA hB).instances 0))
    (r' : NumericalTuples.Point ((Component.rules A' B' hA' hB').instances 0))
    {t p} (ht : Concludes A B t p)
    (hr : (((Component.rules A B hA hB).conclusion 0).toFun r).val = p.encode)
    (hr' : (((Component.rules A' B' hA' hB').conclusion 0).toFun r').val = (p.mapAtoms f).encode)
    (hs : (nullary (Component.rules A B hA hB) (Component.algebra A B hA hB)).toFun r =
      Component.proofPoint A B hA hB t ⟨p,ht⟩)
    (hd : (nullary (Component.rules A' B' hA' hB') (Component.algebra A' B' hA' hB')).toFun r' =
      Component.proofPoint A' B' hA' hB' (t.mapAtoms f) ⟨p.mapAtoms f,ht.mapAtoms f ha hb⟩) :
    mapValue hA hB hA' hB' (Component.algebra A B hA hB) (Component.algebra A' B' hA' hB') f hf
      (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) p
      (targetNullary A B hA hB (Component.algebra A B hA hB) r p hr) =
    targetNullary A' B' hA' hB' (Component.algebra A' B' hA' hB') r' (p.mapAtoms f) hr' := by
  apply Subtype.ext
  exact (congrArg (proofMap hA hB hA' hB' f hf ha hb).toFun hs).trans
    ((proofMap_selected hA hB hA' hB' f hf ha hb t ⟨p,ht⟩).trans hd.symm)

/-- The old proof relabeling itself is an inference-algebra map over
atom relabeling. Every matched MP input is included in this statement. -/
theorem native_algebra_naturality :
    AlgebraNaturality hA hB hA' hB' (Component.algebra A B hA hB)
      (Component.algebra A' B' hA' hB') f hf ha hb
      (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) where
  logical1 p q := native_nullary_natural hA hB hA' hB' f hf ha hb
    (Component.logical1Label A B hA hB p q)
    (Component.logical1Label A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f))
    (Concludes.logical1 p q) (Component.logical1Label_conclusion A B hA hB p q)
    (Component.logical1Label_conclusion A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f))
    (Component.algebra_logical1 A B hA hB p q)
    (Component.algebra_logical1 A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f))
  logical2 p q r := native_nullary_natural hA hB hA' hB' f hf ha hb
    (Component.logical2Label A B hA hB p q r)
    (Component.logical2Label A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f))
    (Concludes.logical2 p q r) (Component.logical2Label_conclusion A B hA hB p q r)
    (Component.logical2Label_conclusion A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f))
    (Component.algebra_logical2 A B hA hB p q r)
    (Component.algebra_logical2 A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f) (r.mapAtoms f))
  logical3 p q := native_nullary_natural hA hB hA' hB' f hf ha hb
    (Component.logical3Label A B hA hB p q)
    (Component.logical3Label A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f))
    (Concludes.logical3 p q) (Component.logical3Label_conclusion A B hA hB p q)
    (Component.logical3Label_conclusion A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f))
    (Component.algebra_logical3 A B hA hB p q)
    (Component.algebra_logical3 A' B' hA' hB' (p.mapAtoms f) (q.mapAtoms f))
  positive x hx := native_nullary_natural hA hB hA' hB' f hf ha hb
    (Component.positiveLabel A B hA hB x hx)
    (Component.positiveLabel A' B' hA' hB' (f x) (ha x hx))
    (Concludes.positive hx) (Component.positiveLabel_conclusion A B hA hB x hx)
    (Component.positiveLabel_conclusion A' B' hA' hB' (f x) (ha x hx))
    (Component.algebra_positive A B hA hB x hx)
    (Component.algebra_positive A' B' hA' hB' (f x) (ha x hx))
  negative x hx := native_nullary_natural hA hB hA' hB' f hf ha hb
    (Component.negativeLabel A B hA hB x hx)
    (Component.negativeLabel A' B' hA' hB' (f x) (hb x hx))
    (Concludes.negative hx) (Component.negativeLabel_conclusion A B hA hB x hx)
    (Component.negativeLabel_conclusion A' B' hA' hB' (f x) (hb x hx))
    (Component.algebra_negative A B hA hB x hx)
    (Component.algebra_negative A' B' hA' hB' (f x) (hb x hx))
  mp p q x y := by
    apply Subtype.ext
    let t := ProofTree.decode x.val.val
    let u := ProofTree.decode y.val.val
    have ht := native_value_concludes A B hA hB x
    have hu := native_value_concludes A B hA hB y
    have ex := native_value_point A B hA hB x
    have ey := native_value_point A B hA hB y
    have hs := native_mp_from_points A B hA hB ht hu x y ex ey
    let x' := mapValue hA hB hA' hB' (Component.algebra A B hA hB)
      (Component.algebra A' B' hA' hB') f hf
      (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) p x
    let y' := mapValue hA hB hA' hB' (Component.algebra A B hA hB)
      (Component.algebra A' B' hA' hB') f hf
      (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) (.imp p q) y
    have ex' : x'.val = Component.proofPoint A' B' hA' hB' (t.mapAtoms f)
        ⟨p.mapAtoms f,ht.mapAtoms f ha hb⟩ :=
      (congrArg (proofMap hA hB hA' hB' f hf ha hb).toFun ex).trans
        (proofMap_selected hA hB hA' hB' f hf ha hb t ⟨p,ht⟩)
    have ey' : y'.val = Component.proofPoint A' B' hA' hB' (u.mapAtoms f)
        ⟨(ForkSyntax.Formula.imp p q).mapAtoms f,hu.mapAtoms f ha hb⟩ :=
      (congrArg (proofMap hA hB hA' hB' f hf ha hb).toFun ey).trans
        (proofMap_selected hA hB hA' hB' f hf ha hb u ⟨.imp p q,hu⟩)
    have hd := native_mp_from_points A' B' hA' hB'
      (ht.mapAtoms f ha hb) (hu.mapAtoms f ha hb) x' y' ex' ey'
    exact (congrArg (proofMap hA hB hA' hB' f hf ha hb).toFun hs).trans
      ((proofMap_selected hA hB hA' hB' f hf ha hb (.mp t u) ⟨q,Concludes.mp ht hu⟩).trans hd.symm)

theorem native_node_naturality
    (n : Component.Node A B (Component.algebra A B hA hB).a) :
    (proofMap hA hB hA' hB' f hf ha hb).toFun
      ((Component.algebra A B hA hB).str.left.toFun
        (Component.nodeInput A B hA hB (Component.algebra A B hA hB).a n)) =
      (Component.algebra A' B' hA' hB').str.left.toFun
        (Component.nodeInput A' B' hA' hB' (Component.algebra A' B' hA' hB').a
          (relabelNode hA hB hA' hB' (Component.algebra A B hA hB)
            (Component.algebra A' B' hA' hB') f hf ha hb
            (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb) n)) :=
  node_natural hA hB hA' hB' (Component.algebra A B hA hB)
    (Component.algebra A' B' hA' hB') f hf ha hb
    (proofMap hA hB hA' hB' f hf ha hb) (proofMap_conclusion hA hB hA' hB' f hf ha hb)
    (native_algebra_naturality hA hB hA' hB' f hf ha hb) n

end NativeNaturality

end CategoricalEssentialIncompleteness.V46.ForkDerivation.Naturality
