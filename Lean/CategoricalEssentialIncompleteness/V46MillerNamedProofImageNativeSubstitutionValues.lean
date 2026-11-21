/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentity
public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionFrame
public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels

/-! # Complete option points and success of the substitution morphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding
private theorem mem_or_of_isCompl {α : Type*} {s t : Set α} (h : IsCompl s t) (x : α) :
    x ∈ s ∨ x ∈ t := by
  have hh : s ∪ t=Set.univ := h.sup_eq_top
  change x ∈ s ∪ t
  rw [hh]
  trivial


section Geometry
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P := P)
private theorem map_product {A B C D : Total.TotalCategory P}
    (f : A ⟶ C) (g : B ⟶ D) (x : (U).obj A) (y : (U).obj B) :
    (U).map (prod.map f g) (Points.pairPoint x y)=
      Points.pairPoint ((U).map f x) ((U).map g y) := by
  apply Points.product_ext
  · rw [← CategoryTheory.Functor.map_comp_apply,prod.map_fst,
      CategoryTheory.Functor.map_comp_apply,Points.pairPoint_fst,Points.pairPoint_fst]
  · rw [← CategoryTheory.Functor.map_comp_apply,prod.map_snd,
      CategoryTheory.Functor.map_comp_apply,Points.pairPoint_snd,Points.pairPoint_snd]

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

def parameterPoint (x : ℕ) (t : Tm) : (U).obj (S).substitutionParameters :=
  Points.pairPoint (Points.namePoint P x) (termPoint P σ π d t)

def termInput (x : ℕ) (t r : Tm) :
    (U).obj ((S).algebra.a.1 ⨯ (S).substitutionParameters) :=
  Points.pairPoint (termPoint P σ π d r) (parameterPoint P σ π d x t)

def formulaInput (x : ℕ) (t : Tm) (φ : Fm) :
    (U).obj ((S).algebra.a.2 ⨯ (S).substitutionParameters) :=
  Points.substitutionPoint P σ π d x φ t

def termValue (x : ℕ) (t r : Tm) : (U).obj (S).algebra.a.1 :=
  (U).map (S).termSubstitution (termInput P σ π d x t r)

def formulaOptionValue (x : ℕ) (t : Tm) (φ : Fm) :
    (U).obj (OptionSyntax.obj (S).algebra.a.2) :=
  (U).map (S).formulaSubstitutionOption (formulaInput P σ π d x t φ)

theorem variable_point (x : ℕ) :
    (U).map (S).variableConstructor (Points.namePoint P x)=termPoint P σ π d (.var x) := by
  have hs : (N).map (S₀).variableConstructor (SyntacticNamedHilbert.namePoint x)=
      SyntacticNamedHilbert.termPoint σ π d (.var x) := by
    apply Subtype.ext
    exact (NamedPlainOperationsModels.variable_value 𝗣𝗔 ℕ (V) σ π d
      (SyntacticNamedHilbert.namePoint x)).trans
        (SyntacticNamedHilbert.termPoint_value σ π d (.var x)).symm
  have h := congrArg (fun k => (U).map k (Points.namePoint P x))
    (NamedSyntaxComparison.variable_constructor P (V) σ π d)
  simpa only [CategoryTheory.Functor.map_comp_apply,Points.namePoint,map_sourcePoint,
    hs,termPoint,sourceTermPoint] using h.symm

/-- A point of the chosen terminal object. -/
def terminalPoint : (U).obj (⊤_ (Total.TotalCategory P)) :=
  (U).map (terminal.from (⟨Total.terminalCarrier⟩ : Total.TotalCategory P)) ⟨0,rfl⟩

theorem terminalPoint_unique (q : (U).obj (⊤_ (Total.TotalCategory P))) :
    q=terminalPoint P := by
  apply (Total.pointHomEquiv (⊤_ (Total.TotalCategory P))).injective
  exact terminalIsTerminal.hom_ext _ _

/-- The uniform option coproduct, rather than the PA traversal's raw numerical option
encoding. -/
def optionPoint : Option Fm → (U).obj (OptionSyntax.obj (S).algebra.a.2)
  | none => (U).map (coprod.inl : ⊤_ (Total.TotalCategory P) ⟶
      OptionSyntax.obj (S).algebra.a.2) (terminalPoint P)
  | some φ => (U).map (coprod.inr : (S).algebra.a.2 ⟶
      OptionSyntax.obj (S).algebra.a.2) (formulaPoint P σ π d φ)

private theorem option_coproduct :
    Function.Injective ((U).map (coprod.inl : ⊤_ (Total.TotalCategory P) ⟶
        OptionSyntax.obj (S).algebra.a.2)) ∧
    Function.Injective ((U).map (coprod.inr : (S).algebra.a.2 ⟶
        OptionSyntax.obj (S).algebra.a.2)) ∧
    IsCompl (Set.range ((U).map (coprod.inl : ⊤_ (Total.TotalCategory P) ⟶
        OptionSyntax.obj (S).algebra.a.2)))
      (Set.range ((U).map (coprod.inr : (S).algebra.a.2 ⟶
        OptionSyntax.obj (S).algebra.a.2))) := by
  exact (Types.binaryCofan_isColimit_iff _).mp
    ⟨isColimitOfHasBinaryCoproductOfPreservesColimit (U)
      (⊤_ (Total.TotalCategory P)) (S).algebra.a.2⟩

theorem optionPoint_none_ne_some (φ : Fm) :
    optionPoint P σ π d none ≠ optionPoint P σ π d (some φ) := by
  intro h
  exact Set.disjoint_left.mp (option_coproduct P σ π d).2.2.disjoint
    ⟨terminalPoint P,rfl⟩ ⟨formulaPoint P σ π d φ,h.symm⟩

theorem optionPoint_injective : Function.Injective (optionPoint P σ π d) := by
  intro a b hab
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some ψ => exact False.elim (optionPoint_none_ne_some P σ π d ψ hab)
  | some φ =>
      cases b with
      | none => exact False.elim (optionPoint_none_ne_some P σ π d φ hab.symm)
      | some ψ =>
          exact congrArg some (formulaPoint_injective P σ π d
            ((option_coproduct P σ π d).2.1 hab))

/-- Every point of the option object is either its failure point or the successful point
of a unique named formula. -/
theorem optionPoint_surjective : Function.Surjective (optionPoint P σ π d) := by
  intro q
  have h := (option_coproduct P σ π d).2.2
  have hc : q ∈ Set.range ((U).map (coprod.inl : ⊤_ (Total.TotalCategory P) ⟶
        OptionSyntax.obj (S).algebra.a.2)) ∨
      q ∈ Set.range ((U).map (coprod.inr : (S).algebra.a.2 ⟶
        OptionSyntax.obj (S).algebra.a.2)) := mem_or_of_isCompl h q
  rcases hc with ⟨z,hz⟩ | ⟨z,hz⟩
  · exact ⟨none,(congrArg ((U).map coprod.inl) (terminalPoint_unique P z).symm).trans hz⟩
  · exact ⟨some (decodeFormula P σ π d z),
      (congrArg ((U).map coprod.inr) (formulaPoint_decode P σ π d z)).trans hz⟩

theorem optionPoint_negation (v : Option Fm) :
    (U).map (OptionSyntax.map (S).negationConstructor) (optionPoint P σ π d v)=
      optionPoint P σ π d (v.map Formula.neg) := by
  cases v with
  | none =>
      change (U).map (OptionSyntax.map (S).negationConstructor)
        ((U).map coprod.inl (terminalPoint P))=(U).map coprod.inl (terminalPoint P)
      rw [← CategoryTheory.Functor.map_comp_apply,OptionSyntax.map,coprod.inl_map,
        Category.id_comp]
  | some φ =>
      change (U).map (OptionSyntax.map (S).negationConstructor)
        ((U).map coprod.inr (formulaPoint P σ π d φ))=
          (U).map coprod.inr (formulaPoint P σ π d (.neg φ))
      rw [← CategoryTheory.Functor.map_comp_apply,OptionSyntax.map,coprod.inr_map,
        CategoryTheory.Functor.map_comp_apply,formulaPoint_negation]

def optionEquiv : Option Fm ≃ (U).obj (OptionSyntax.obj (S).algebra.a.2) :=
  Equiv.ofBijective (optionPoint P σ π d)
    ⟨optionPoint_injective P σ π d,optionPoint_surjective P σ π d⟩

def decodeOption : (U).obj (OptionSyntax.obj (S).algebra.a.2) → Option Fm :=
  (optionEquiv P σ π d).symm

@[simp] theorem decode_optionPoint (v : Option Fm) :
    decodeOption P σ π d (optionPoint P σ π d v)=v :=
  (optionEquiv P σ π d).symm_apply_apply v

@[simp] theorem optionPoint_decode (q : (U).obj (OptionSyntax.obj (S).algebra.a.2)) :
    optionPoint P σ π d (decodeOption P σ π d q)=q :=
  (optionEquiv P σ π d).apply_symm_apply q

/-- Decode the option as a named formula on success and as `none` on failure. -/
def decodedResult (x : ℕ) (t : Tm) (φ : Fm) : Option Fm :=
  decodeOption P σ π d (formulaOptionValue P σ π d x t φ)

theorem identity_parameter_point (x : ℕ) :
    (U).map (S).identityParameters (Points.namePoint P x)=parameterPoint P σ π d x (.var x) := by
  change (U).map (prod.lift (𝟙 ((F).obj (V))) (S).variableConstructor)
    (Points.namePoint P x)=_
  rw [Points.lift_point,CategoryTheory.Functor.map_id_apply,variable_point]
  rfl

/-- Identity substitution at every literal term point. -/
theorem identity_term (x : ℕ) (r : Tm) :
    termValue P σ π d x (.var x) r=termPoint P σ π d r := by
  let z := Points.pairPoint (termPoint P σ π d r) (Points.namePoint P x)
  have hi : (U).map (S).identityTermInput z=termInput P σ π d x (.var x) r := by
    change (U).map (prod.map (𝟙 (S).algebra.a.1) (S).identityParameters) z=_
    rw [map_product,CategoryTheory.Functor.map_id_apply,identity_parameter_point]
    rfl
  have h := congrArg (fun k => (U).map k z) (S).term_substitution_identity
  simpa only [CategoryTheory.Functor.map_comp_apply,hi,z,Points.pairPoint_fst,termValue] using h

/-- The complete option output for identity substitution, with arbitrary named formula and
original names. -/
theorem identity_option (x : ℕ) (φ : Fm) :
    formulaOptionValue P σ π d x (.var x) φ=optionPoint P σ π d (some φ) := by
  let z := Points.pairPoint (formulaPoint P σ π d φ) (Points.namePoint P x)
  have hi : (U).map (S).identityFormulaInput z=formulaInput P σ π d x (.var x) φ := by
    change (U).map (prod.map (𝟙 (S).algebra.a.2) (S).identityParameters) z=_
    rw [map_product,CategoryTheory.Functor.map_id_apply,identity_parameter_point]
    rfl
  have h := congrArg (fun k => (U).map k z) (S).formula_substitution_identity
  simpa only [CategoryTheory.Functor.map_comp_apply,hi,z,Points.pairPoint_fst,
    formulaOptionValue,optionPoint] using h

theorem identity_decoded (x : ℕ) (φ : Fm) :
    decodedResult P σ π d x (.var x) φ=some φ :=
  (congrArg (decodeOption P σ π d) (identity_option P σ π d x φ)).trans
    (decode_optionPoint P σ π d _)

theorem option_graph (x : ℕ) (t : Tm) (φ : Fm) (v : Option Fm) :
    (optionPoint P σ π d v).val∈Total.val (S).formulaSubstitutionOption.hom
      (formulaInput P σ π d x t φ).val ↔ decodedResult P σ π d x t φ=v := by
  rw [← Total.totalFunction_eq_iff]
  change formulaOptionValue P σ π d x t φ=optionPoint P σ π d v ↔ _
  constructor
  · intro h
    exact (congrArg (decodeOption P σ π d) h).trans (decode_optionPoint P σ π d v)
  · intro h
    exact (optionPoint_decode P σ π d _).symm.trans (congrArg (optionPoint P σ π d) h)

/-- Both directions are obtained from the constructed success pullback.
The inclusion coordinate, not the raw code of a pullback point, is used. -/
theorem success_iff (x : ℕ) (t : Tm) (φ ψ : Fm) :
    (∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=formulaInput P σ π d x t φ ∧
      (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ) ↔
        decodedResult P σ π d x t φ=some ψ := by
  constructor
  · rintro ⟨a,hi,hr⟩
    have h := congrArg (fun f => (U).map f a) (S).formulaSubstitution_square
    simp only [CategoryTheory.Functor.map_comp_apply,hi,hr] at h
    change formulaOptionValue P σ π d x t φ=optionPoint P σ π d (some ψ) at h
    exact (congrArg (decodeOption P σ π d) h).trans (decode_optionPoint P σ π d _)
  · intro h
    have hv : formulaOptionValue P σ π d x t φ=optionPoint P σ π d (some ψ) :=
      (optionPoint_decode P σ π d _).symm.trans (congrArg (optionPoint P σ π d) h)
    exact Points.pullback_point_exists (S).formulaSubstitutionOption
      (coprod.inr : (S).algebra.a.2 ⟶ OptionSyntax.obj (S).algebra.a.2)
      (formulaInput P σ π d x t φ) (formulaPoint P σ π d ψ) hv

theorem failure_iff (x : ℕ) (t : Tm) (φ : Fm) :
    decodedResult P σ π d x t φ=none ↔
      ¬ ∃ a : (U).obj (S).admissibleSubstitution,
        (U).map (S).admissibleInclusion a=formulaInput P σ π d x t φ := by
  constructor
  · intro hn ⟨a,ha⟩
    let ψ := decodeFormula P σ π d ((U).map (S).formulaSubstitution a)
    have hs : decodedResult P σ π d x t φ=some ψ :=
      (success_iff P σ π d x t φ ψ).mp
        ⟨a,ha,(formulaPoint_decode P σ π d _).symm⟩
    rw [hn] at hs
    cases hs
  · intro hf
    cases h : decodedResult P σ π d x t φ with
    | none => rfl
    | some ψ =>
        obtain ⟨a,ha,_⟩ := (success_iff P σ π d x t φ ψ).mpr h
        exact False.elim (hf ⟨a,ha⟩)


end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
