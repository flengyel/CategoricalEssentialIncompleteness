/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedAxioms
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersSlices

/-! # Numeral/complement splitting in the actual arithmetic category

The inverse of the displayed copair is justified in every PA model and
then reflected to the predicate category. It is transported through the
proved realization equivalence and the identity-omega comparison.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
universe u v
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
open NamedArithmeticSignature

/-- The complement retains the original numerical parameter as its
sole label. No membership witness is added to it. -/
def complementPredicate (e : ℕ) : Carrier := .mkSigma “x. x ≠ !!(e)”

def numeralGraph (e : ℕ) : 𝚺₁.Semisentence 2 := .mkSigma “x y. x = 0 ∧ y = !!(e)”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem complementPredicate_eval (e : ℕ) (x : M) :
    (complementPredicate e).val.Evalb ![x] ↔ x ≠ (e : M) := by
  simp [complementPredicate,numeral_eq_natCast_app]

@[simp] theorem numeralGraph_eval (e : ℕ) (x y : M) :
    (numeralGraph e).val.Evalb ![x,y] ↔ x = 0 ∧ y = (e : M) := by
  simp [numeralGraph,numeral_eq_natCast_app]

end Models

def numeralRepresentation (e : ℕ) : GraphMorphism 𝗣𝗔 terminalCarrier variableSymbols where
  graph := numeralGraph e
  support := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,supportSentence_eval]
    intro x y h
    exact ⟨(terminalCarrier_eval x).mpr ((numeralGraph_eval M e x y).mp h).1,variables_eval y⟩
  total := by
    apply complete.{0} 𝗣𝗔
    intro M _ _
    rw [models_iff,totalSentence_eval]
    intro x hx
    refine ⟨(e : M),(numeralGraph_eval M e x (e : M)).mpr
      ⟨(terminalCarrier_eval x).mp hx,rfl⟩,?_⟩
    intro y hy
    exact ((numeralGraph_eval M e x y).mp hy).2

def numeralPredicate (e : ℕ) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    terminalCarrier variableSymbols := representedArrow 𝗣𝗔 (numeralRepresentation e)

theorem complementInclusionProof (e : ℕ) :
    𝗣𝗔 ⊢ inclusionSentence (complementPredicate e) variableSymbols := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro x _
  exact variables_eval x

def complementPredicateInclusion (e : ℕ) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    (complementPredicate e) variableSymbols :=
  representedArrow 𝗣𝗔 (GraphMorphism.inclusion (complementInclusionProof e))

instance complementPredicateInclusion_mono (e : ℕ) : Mono (complementPredicateInclusion e) := by
  unfold complementPredicateInclusion
  infer_instance

def rawDispatch (e : ℕ) : GraphMorphism 𝗣𝗔
    (PredicateInterpretation.sumCarrier terminalCarrier (complementPredicate e)) variableSymbols :=
  PredicateInterpretation.sumCopair 𝗣𝗔 (numeralPredicate e) (complementPredicateInclusion e)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem dispatch_inl_value (e : ℕ) (x : Obj 𝗣𝗔 M terminalCarrier) :
    ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (rawDispatch e))
      (PredicateInterpretation.sumCoding 𝗣𝗔 M terminalCarrier (complementPredicate e) (.inl x))).val =
      (e : M) := by
  let z : Obj 𝗣𝗔 M variableSymbols := ⟨(e : M),variables_eval _⟩
  have h : (F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (rawDispatch e))
      (PredicateInterpretation.sumCoding 𝗣𝗔 M terminalCarrier (complementPredicate e) (.inl x)) = z := by
    apply (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 M (rawDispatch e) _ z).mpr
    apply (PredicateInterpretation.sumCopair_eval 𝗣𝗔 M (numeralPredicate e)
      (complementPredicateInclusion e) _ _).mpr
    refine Or.inl ⟨x.val,rfl,?_⟩
    rw [numeralPredicate,relation_class]
    exact (numeralGraph_eval M e x.val (e : M)).mpr ⟨(terminalCarrier_eval x.val).mp x.property,rfl⟩
  exact congrArg Subtype.val h

private theorem dispatch_inr_value (e : ℕ) (x : Obj 𝗣𝗔 M (complementPredicate e)) :
    ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (rawDispatch e))
      (PredicateInterpretation.sumCoding 𝗣𝗔 M terminalCarrier (complementPredicate e) (.inr x))).val = x.val := by
  let z : Obj 𝗣𝗔 M variableSymbols := ⟨x.val,variables_eval _⟩
  have h : (F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (rawDispatch e))
      (PredicateInterpretation.sumCoding 𝗣𝗔 M terminalCarrier (complementPredicate e) (.inr x)) = z := by
    apply (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 M (rawDispatch e) _ z).mpr
    apply (PredicateInterpretation.sumCopair_eval 𝗣𝗔 M (numeralPredicate e)
      (complementPredicateInclusion e) _ _).mpr
    refine Or.inr ⟨x.val,rfl,?_⟩
    rw [complementPredicateInclusion,relation_class]
    exact (GraphMorphism.identityGraph_eval (complementPredicate e) x.val z.val).mpr ⟨x.property,rfl⟩
  exact congrArg Subtype.val h

/-- The numeral and its complement give a genuine bijection at every
code-model point, including nonstandard parameters different from e. -/
theorem rawDispatch_bijective (e : ℕ) :
    Function.Bijective ((F 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (rawDispatch e))) := by
  classical
  constructor
  · intro x y h
    obtain ⟨a,rfl⟩ := (PredicateInterpretation.sumCoding_bijective 𝗣𝗔 M
      terminalCarrier (complementPredicate e)).2 x
    obtain ⟨b,rfl⟩ := (PredicateInterpretation.sumCoding_bijective 𝗣𝗔 M
      terminalCarrier (complementPredicate e)).2 y
    have hv := congrArg Subtype.val h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            have hab : a = b := Subtype.ext (((terminalCarrier_eval a.val).mp a.property).trans
              ((terminalCarrier_eval b.val).mp b.property).symm)
            exact congrArg (fun a => PredicateInterpretation.sumCoding 𝗣𝗔 M
              terminalCarrier (complementPredicate e) (Sum.inl a)) hab
        | inr b =>
            rw [dispatch_inl_value,dispatch_inr_value] at hv
            exact False.elim (((complementPredicate_eval M e b.val).mp b.property) hv.symm)
    | inr a =>
        cases b with
        | inl b =>
            rw [dispatch_inr_value,dispatch_inl_value] at hv
            exact False.elim (((complementPredicate_eval M e a.val).mp a.property) hv)
        | inr b =>
            rw [dispatch_inr_value,dispatch_inr_value] at hv
            exact congrArg (fun a => PredicateInterpretation.sumCoding 𝗣𝗔 M
              terminalCarrier (complementPredicate e) (Sum.inr a)) (Subtype.ext hv)
  · intro y
    by_cases he : y.val = (e : M)
    · let x : Obj 𝗣𝗔 M terminalCarrier := ⟨0,(terminalCarrier_eval (0 : M)).mpr rfl⟩
      refine ⟨PredicateInterpretation.sumCoding 𝗣𝗔 M terminalCarrier (complementPredicate e) (.inl x),?_⟩
      exact Subtype.ext ((dispatch_inl_value M e x).trans he.symm)
    · let x : Obj 𝗣𝗔 M (complementPredicate e) := ⟨y.val,(complementPredicate_eval M e y.val).mpr he⟩
      refine ⟨PredicateInterpretation.sumCoding 𝗣𝗔 M terminalCarrier (complementPredicate e) (.inr x),?_⟩
      exact Subtype.ext (dispatch_inr_value M e x)

end Models

instance rawDispatch_isIso (e : ℕ) : IsIso (representedArrow 𝗣𝗔 (rawDispatch e)) :=
  PredicateInterpretation.isIso_of_models_bijective 𝗣𝗔 _ (fun M _ _ => rawDispatch_bijective M e)

section RawSumComparison
variable {D : Type u} [Category.{v} D] [HasFiniteCoproducts D]
variable {A B Z : D} (f : A ⟶ Z) (g : B ⟶ Z) (h : IsColimit (BinaryCofan.mk f g))

def rawSumComparison : A ⨿ B ≅ Z :=
  IsColimit.coconePointUniqueUpToIso (coprodIsCoprod A B) h

@[simp,reassoc] theorem rawSumComparison_inl : coprod.inl ≫ (rawSumComparison f g h).hom = f := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod A B) h ⟨WalkingPair.left⟩

@[simp,reassoc] theorem rawSumComparison_inr : coprod.inr ≫ (rawSumComparison f g h).hom = g := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod A B) h ⟨WalkingPair.right⟩
end RawSumComparison

def predicateRawSumIso (e : ℕ) : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (terminalCarrier ⨿ complementPredicate e)
    (PredicateInterpretation.sumCarrier terminalCarrier (complementPredicate e)) :=
  rawSumComparison
    (representedArrow 𝗣𝗔 (PredicateInterpretation.sumInl 𝗣𝗔 terminalCarrier (complementPredicate e)))
    (representedArrow 𝗣𝗔 (PredicateInterpretation.sumInr 𝗣𝗔 terminalCarrier (complementPredicate e)))
    (PredicateInterpretation.sumIsColimit 𝗣𝗔 terminalCarrier (complementPredicate e))

def predicateSplitIso (e : ℕ) : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (terminalCarrier ⨿ complementPredicate e) variableSymbols :=
  predicateRawSumIso e ≪≫ asIso (representedArrow 𝗣𝗔 (rawDispatch e))

@[simp, reassoc] theorem predicateRawSumIso_inl (e : ℕ) :
    coprod.inl ≫ (predicateRawSumIso e).hom =
      representedArrow 𝗣𝗔 (PredicateInterpretation.sumInl 𝗣𝗔 terminalCarrier (complementPredicate e)) :=
  rawSumComparison_inl _ _ _

@[simp, reassoc] theorem predicateRawSumIso_inr (e : ℕ) :
    coprod.inr ≫ (predicateRawSumIso e).hom =
      representedArrow 𝗣𝗔 (PredicateInterpretation.sumInr 𝗣𝗔 terminalCarrier (complementPredicate e)) :=
  rawSumComparison_inr _ _ _

@[simp, reassoc] theorem predicateSplitIso_inl (e : ℕ) :
    coprod.inl ≫ (predicateSplitIso e).hom = numeralPredicate e := by
  rw [predicateSplitIso,Iso.trans_hom,← Category.assoc,predicateRawSumIso_inl]
  exact PredicateInterpretation.sum_inl_desc 𝗣𝗔 (numeralPredicate e) (complementPredicateInclusion e)

@[simp, reassoc] theorem predicateSplitIso_inr (e : ℕ) :
    coprod.inr ≫ (predicateSplitIso e).hom = complementPredicateInclusion e := by
  rw [predicateSplitIso,Iso.trans_hom,← Category.assoc,predicateRawSumIso_inr]
  exact PredicateInterpretation.sum_inr_desc 𝗣𝗔 (numeralPredicate e) (complementPredicateInclusion e)

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
