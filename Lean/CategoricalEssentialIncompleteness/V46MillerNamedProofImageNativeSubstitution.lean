/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionValues
public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityBranches

/-! # Actual substitution states, framed constructor equations, and equal binders -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding

section Geometry
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P := P)
private theorem chain_point {A B C D E : Total.TotalCategory P}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (k : D ⟶ E) (x : (U).obj A) :
    (U).map k ((U).map (f ≫ g ≫ h) x)=(U).map (f ≫ g ≫ h ≫ k) x := by
  rw [← CategoryTheory.Functor.map_comp_apply,Category.assoc,Category.assoc]

end Geometry

variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

def termState (x : ℕ) (t r : Tm) : (U).obj (S).substitutionCarriers.1 :=
  (U).map ((prod.braiding (S).algebra.a.1 (S).substitutionParameters).hom ≫
    (S).substitutionFold.1.left ≫ prod.snd) (termInput P σ π d x t r)

def formulaState (x : ℕ) (t : Tm) (φ : Fm) : (U).obj (S).substitutionCarriers.2 :=
  (U).map ((prod.braiding (S).algebra.a.2 (S).substitutionParameters).hom ≫
    (S).substitutionFold.2.left ≫ prod.snd) (formulaInput P σ π d x t φ)

theorem termState_original (x : ℕ) (t r : Tm) :
    (U).map (prod.fst : (S).substitutionCarriers.1 ⟶ (S).algebra.a.1)
      (termState P σ π d x t r)=termPoint P σ π d r := by
  have h := congrArg (fun f => (U).map f (termInput P σ π d x t r))
    (S).termSubstitution_original
  simpa only [termState,CategoryTheory.Functor.map_comp_apply,termInput,Points.pairPoint_fst,
    CategoricalSyntax.substitutionCarriers]
    using h

theorem formulaState_original (x : ℕ) (t : Tm) (φ : Fm) :
    (U).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)
      (formulaState P σ π d x t φ)=formulaPoint P σ π d φ := by
  have h := congrArg (fun f => (U).map f (formulaInput P σ π d x t φ))
    (S).formulaSubstitution_original
  simpa only [formulaState,CategoryTheory.Functor.map_comp_apply,formulaInput,
    Points.substitutionPoint,Points.pairPoint_fst,CategoricalSyntax.substitutionCarriers] using h

theorem termState_result (x : ℕ) (t r : Tm) :
    (U).map (prod.snd : (S).substitutionCarriers.1 ⟶ (S).algebra.a.1)
      (termState P σ π d x t r)=termValue P σ π d x t r := by
  unfold termState termValue CategoricalSyntax.termSubstitution
  exact chain_point (prod.braiding (S).algebra.a.1 (S).substitutionParameters).hom
    (S).substitutionFold.1.left prod.snd prod.snd (termInput P σ π d x t r)

theorem formulaState_result (x : ℕ) (t : Tm) (φ : Fm) :
    (U).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj (S).algebra.a.2)
      (formulaState P σ π d x t φ)=formulaOptionValue P σ π d x t φ := by
  unfold formulaState formulaOptionValue CategoricalSyntax.formulaSubstitutionOption
  exact chain_point (prod.braiding (S).algebra.a.2 (S).substitutionParameters).hom
    (S).substitutionFold.2.left prod.snd prod.snd (formulaInput P σ π d x t φ)

section ActualRootLaws
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "A" => SyntaxPolynomial.algebraWithParameters p q
  (CategoricalSyntax.algebra (NamedProofImage.syntaxData P σ π d)) R

theorem term_root_framed (r : (U).obj (R))
    (u : PointFrame.Data (R) r (A).a (p)) :
    PointFrame.realize (R) r (A).a (p) u ≫ (A).str.1 ≫ (S).substitutionFold.1=
      PointFrame.realize (R) r (S).substitutionAlgebra.a (p)
        (PointFrame.mapData (R) r (S).substitutionFold (p) u) ≫
          (S).substitutionAlgebra.str.1 := by
  have h := congrArg (fun k => PointFrame.realize (R) r (A).a (p) u ≫ k.1)
    (S).substitutionFold_commutes
  change PointFrame.realize (R) r (A).a (p) u ≫
      (((p).withParameters R).eval.map (S).substitutionFold ≫ (S).substitutionAlgebra.str.1)=
    PointFrame.realize (R) r (A).a (p) u ≫ ((A).str.1 ≫ (S).substitutionFold.1) at h
  exact h.symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (S).substitutionAlgebra.str.1)
      (PointFrame.realize_natural (R) r (S).substitutionFold (p) u)))

theorem formula_root_framed (r : (U).obj (R))
    (u : PointFrame.Data (R) r (A).a (q)) :
    PointFrame.realize (R) r (A).a (q) u ≫ (A).str.2 ≫ (S).substitutionFold.2=
      PointFrame.realize (R) r (S).substitutionAlgebra.a (q)
        (PointFrame.mapData (R) r (S).substitutionFold (q) u) ≫
          (S).substitutionAlgebra.str.2 := by
  have h := congrArg (fun k => PointFrame.realize (R) r (A).a (q) u ≫ k.2)
    (S).substitutionFold_commutes
  change PointFrame.realize (R) r (A).a (q) u ≫
      (((q).withParameters R).eval.map (S).substitutionFold ≫ (S).substitutionAlgebra.str.2)=
    PointFrame.realize (R) r (A).a (q) u ≫ ((A).str.2 ≫ (S).substitutionFold.2) at h
  exact h.symm.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (S).substitutionAlgebra.str.2)
      (PointFrame.realize_natural (R) r (S).substitutionFold (q) u)))

end ActualRootLaws

section NativeNodeInputs
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "A" => SyntaxPolynomial.algebraWithParameters p q
  (CategoricalSyntax.algebra (NamedProofImage.syntaxData P σ π d)) R

def termLeaf (r : (U).obj (R)) (t : Tm) : PointFrame.source (R) r ⟶ (A).a.1 :=
  PointFrame.constant (R) r (S).algebra.a.1 (termPoint P σ π d t)

def formulaLeaf (r : (U).obj (R)) (φ : Fm) : PointFrame.source (R) r ⟶ (A).a.2 :=
  PointFrame.constant (R) r (S).algebra.a.2 (formulaPoint P σ π d φ)

def termNodeInput (r : (U).obj (R)) : Tm → PointFrame.Data (R) r (A).a (p)
  | .var x => Sum.inl (Points.namePoint P x)
  | .app k c children => Sum.inr
      (PointFrame.arityData (R) r (A).a (fun n => (F).obj (σ n)) d k
        (sourcePoint P (σ k.val) c) (fun i => termLeaf P σ π d r (children i)))

def formulaNodeInput (r : (U).obj (R)) : Fm → PointFrame.Data (R) r (A).a (q)
  | .equal u v => Sum.inl (Sum.inl (Sum.inl (Sum.inl
      (termLeaf P σ π d r u,termLeaf P σ π d r v))))
  | .relation k c children => Sum.inl (Sum.inl (Sum.inl (Sum.inr
      (PointFrame.arityData (R) r (A).a (fun n => (F).obj (π n)) d k
        (sourcePoint P (π k.val) c) (fun i => termLeaf P σ π d r (children i))))))
  | .neg body => Sum.inl (Sum.inl (Sum.inr (formulaLeaf P σ π d r body)))
  | .imp left right => Sum.inl (Sum.inr
      (formulaLeaf P σ π d r left,formulaLeaf P σ π d r right))
  | .all x body => Sum.inr (Points.namePoint P x,formulaLeaf P σ π d r body)

/-- At a function node, functoriality changes exactly the ordered child
arrows. The selected symbol label and arity do not change. -/
theorem function_node_map (r : (U).obj (R)) (k : Fin (d+1))
    (c : Symbols σ k.val) (children : Fin k.val → Tm) :
    PointFrame.mapData (R) r (S).substitutionFold (p)
      (termNodeInput P σ π d r (.app k c children))=
        Sum.inr (PointFrame.arityData (R) r (S).substitutionAlgebra.a
          (fun n => (F).obj (σ n)) d k (sourcePoint P (σ k.val) c)
            (fun i => termLeaf P σ π d r (children i) ≫ (S).substitutionFold.1)) := by
  change Sum.inr (PointFrame.mapData (R) r (S).substitutionFold
    (SyntaxPolynomial.constructors (fun n => (F).obj (σ n)) d)
      (PointFrame.arityData (R) r (A).a (fun n => (F).obj (σ n)) d k
        (sourcePoint P (σ k.val) c) (fun i => termLeaf P σ π d r (children i))))=_
  exact congrArg Sum.inr (PointFrame.arityData_natural (R) r (S).substitutionFold
    (fun n => (F).obj (σ n)) d k (sourcePoint P (σ k.val) c)
      (fun i => termLeaf P σ π d r (children i)))

theorem quantified_node_map (r : (U).obj (R)) (x : ℕ) (body : Fm) :
    PointFrame.mapData (R) r (S).substitutionFold (q)
      (formulaNodeInput P σ π d r (.all x body))=
        Sum.inr (Points.namePoint P x,formulaLeaf P σ π d r body ≫ (S).substitutionFold.2) := rfl

end NativeNodeInputs

/-- A full-option calculation for the actual fold. There is no assumption
about whether recursively substituting into the original body succeeds. -/
theorem equal_binder_option (x : ℕ) (t : Tm) (φ : Fm) :
    formulaOptionValue P σ π d x t (.all x φ)=optionPoint P σ π d (some (.all x φ)) := by
  let Z : Total.TotalCategory P := ⟨Total.terminalCarrier⟩
  let xp : Z ⟶ (F).obj (V) := Total.underlyingPoint (Points.namePoint P x)
  let tp : Z ⟶ (S).substitutionParameters := Total.underlyingPoint (parameterPoint P σ π d x t)
  let bp : Z ⟶ (S).algebra.a.2 := Total.underlyingPoint (formulaPoint P σ π d φ)
  let k : Z ⟶ (S).quantifierAdmissibilityParameters := prod.lift (prod.lift xp bp) tp
  have hx : tp ≫ prod.fst=xp := by
    exact (PointFrame.point_natural
      (prod.fst : (S).substitutionParameters ⟶ (F).obj (V))
      (parameterPoint P σ π d x t)).symm.trans
        (congrArg Total.underlyingPoint
          (Points.pairPoint_fst (Points.namePoint P x) (termPoint P σ π d t)))
  have he : k ≫ (S).quantifiedEquality=Two.constant Z true := by
    have ht := ((S).decidableVariables.test_true_iff xp xp).mpr rfl
    simpa only [k,CategoricalSyntax.quantifiedEquality,prod.comp_lift,
      prod.lift_fst,prod.lift_snd,prod.lift_fst_assoc,prod.lift_snd_assoc,
      prod.comp_lift_assoc,Category.assoc,hx] using ht
  have hh := (S).quantified_equal_name k he
  have h : prod.lift (prod.lift xp bp ≫ (S).quantifierConstructor) tp ≫
      (S).formulaSubstitutionOption=(prod.lift xp bp ≫ (S).quantifierConstructor) ≫ coprod.inr := by
    simpa only [k,CategoricalSyntax.quantifiedInput,prod.lift_map_assoc,
      Category.comp_id,prod.lift_fst,prod.lift_fst_assoc,Category.assoc] using hh
  let z : (U).obj Z := ⟨0,rfl⟩
  have hxv : (U).map xp z=Points.namePoint P x := at_point _
  have htv : (U).map tp z=parameterPoint P σ π d x t := at_point _
  have hbv : (U).map bp z=formulaPoint P σ π d φ := at_point _
  have hv := congrArg (fun f : Z ⟶ OptionSyntax.obj (S).algebra.a.2 => (U).map f z) h
  simpa only [CategoryTheory.Functor.map_comp_apply,Points.lift_point,hxv,htv,hbv,
    Points.quantifier_point,formulaOptionValue,formulaInput,Points.substitutionPoint,
    parameterPoint,optionPoint] using hv

theorem equal_binder_decoded (x : ℕ) (t : Tm) (φ : Fm) :
    decodedResult P σ π d x t (.all x φ)=some (.all x φ) := by
  exact (congrArg (decodeOption P σ π d) (equal_binder_option P σ π d x t φ)).trans
    (decode_optionPoint P σ π d _)

theorem equal_binder_success (x : ℕ) (t : Tm) (φ : Fm) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x (.all x φ) t ∧
      (U).map (S).formulaSubstitution a=formulaPoint P σ π d (.all x φ) :=
  (success_iff P σ π d x t (.all x φ) (.all x φ)).mpr
    (equal_binder_decoded P σ π d x t φ)

/-- Every successful point on the equal-name input has the original
quantified formula as its output, including when the body itself fails. -/
theorem equal_binder_reflection (x : ℕ) (t : Tm) (φ ψ : Fm)
    (a : (U).obj (S).admissibleSubstitution)
    (hi : (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x (.all x φ) t)
    (hr : (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ) : ψ=.all x φ := by
  have hs := (success_iff P σ π d x t (.all x φ) ψ).mp ⟨a,hi,hr⟩
  exact Option.some.inj ((hs.symm.trans (equal_binder_decoded P σ π d x t φ)))

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
