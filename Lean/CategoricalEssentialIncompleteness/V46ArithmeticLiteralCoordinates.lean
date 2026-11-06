/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticLiteralModel
import CategoricalEssentialIncompleteness.V46ArithmeticSetModelLaws

/-! # The literal sentence chart in the canonical split-domain interpretation

These comparisons use the existing natural domain comparisons and the proved
sentence morphism. No equality with an unproved source projection is needed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticLiteralCoordinates
open NamedArithmeticSignature ArithmeticLiteralModel

private theorem natural_apply {D : Type u} [Category.{v} D]
    (F G : D ⥤ Type) (η : F ≅ G) {X Y : D} (f : X ⟶ Y) (x : F.obj X) :
    (η.app Y).toEquiv (F.map f x) = G.map f ((η.app X).toEquiv x) :=
  ConcreteCategory.congr_hom (η.hom.naturality f) x

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "H" => PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M
local notation "E" => realization 𝗣𝗔
local notation "G" => F 𝗣𝗔 M

def predicateComparison : (E) ⋙ (H) ≅ (G) :=
  Functor.isoWhiskerLeft (E) (PredicateInterpretation.domainCanonicalComparison 𝗣𝗔 M).symm ≪≫
    PredicateInterpretation.realizedDomainComparison 𝗣𝗔 M

def chart (C : PredicateCategory 𝗣𝗔) :
    (H).obj ((E).obj C) ≃ Obj 𝗣𝗔 M C :=
  ((predicateComparison M).app C).toEquiv

theorem chart_value (C : PredicateCategory 𝗣𝗔) (x : (H).obj ((E).obj C)) :
    (chart M C x).val = x.val.val := rfl

theorem chart_map {C D : PredicateCategory 𝗣𝗔} (f : C ⟶ D)
    (x : (H).obj ((E).obj C)) :
    chart M D ((H).map ((E).map f) x) = (G).map f (chart M C x) := by
  exact natural_apply ((E) ⋙ (H)) (G) (predicateComparison M) f x

theorem theorem_iff_image (Γ : Carrier) (s : (H).obj ((E).obj sentencePredicate)) :
    (theoremPredicate Γ).val.Evalb ![s.val.val] ↔
      ∃ p : (H).obj ((E).obj (proofObject Γ)), (H).map ((E).map (conclusion Γ)) p = s := by
  have ht := ArithmeticLiteralModel.theorem_iff_image M Γ (chart M sentencePredicate s)
  constructor
  · intro h
    obtain ⟨p,hp⟩ := ht.mp h
    refine ⟨(chart M (proofObject Γ)).symm p,?_⟩
    apply (chart M sentencePredicate).injective
    rw [chart_map,Equiv.apply_symm_apply]
    exact hp
  · rintro ⟨p,hp⟩
    apply ht.mpr
    refine ⟨chart M (proofObject Γ) p,?_⟩
    rw [← chart_map,hp]

theorem negation_value (s : (H).obj ((E).obj sentencePredicate)) :
    ((H).map ((E).map negation) s).val.val =
      NamedArithmeticProofSearch.negationWord M s.val.val := by
  have h := congrArg Subtype.val (chart_map M negation s)
  exact h.trans (ArithmeticLiteralModel.negation_value M (chart M sentencePredicate s))

theorem theta_chart (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (x : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M (ArithmeticOmegaComparison.identityOmega 𝗣𝗔)) :
    chart M sentencePredicate ((H).map (NamedArithmeticLiteralTotal.theta φ hφ) x) =
      thetaPoint M φ hφ x.val.val := by
  apply Subtype.ext
  exact NamedArithmeticLiteralTotal.canonical_value φ hφ M x

/-- This is the image of the actual realized sentence-conclusion map,
on the canonical chosen splitting domain. -/
def theory (Γ : Carrier) : Idem (PartialFun.of ((H).obj ((E).obj sentencePredicate))) :=
  Ranges.range (fun p => Part.some ((H).map ((E).map (conclusion Γ)) p))

theorem theory_support (Γ : Carrier) (s : (H).obj ((E).obj sentencePredicate)) :
    s ∈ support (theory M Γ) ↔ (theoremPredicate Γ).val.Evalb ![s.val.val] :=
  (ArithmeticSetModelLaws.range_some_support ((H).map ((E).map (conclusion Γ))) s).trans
    (theorem_iff_image M Γ s).symm

def negationMap : PartialFun.of ((H).obj ((E).obj sentencePredicate)) ⟶
    PartialFun.of ((H).obj ((E).obj sentencePredicate)) :=
  fun s => Part.some ((H).map ((E).map negation) s)

def thetaMap (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    PartialFun.of M ⟶ PartialFun.of ((H).obj ((E).obj sentencePredicate)) :=
  fun n => Part.some ((H).map (NamedArithmeticLiteralTotal.theta φ hφ)
    (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n))

theorem thetaMap_total (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    isTotal (thetaMap M φ hφ) :=
  ArithmeticSetModelLaws.someMap_total (fun n =>
    (H).map (NamedArithmeticLiteralTotal.theta φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n))

theorem theta_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    ((H).map (NamedArithmeticLiteralTotal.theta φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)).val.val =
        NamedArithmeticFixedSubstitution.value φ n :=
  NamedArithmeticLiteralTotal.canonical_value_at φ hφ M n

theorem theory_consistent (Γ : Carrier)
    (hΓ : ∀ s : Obj 𝗣𝗔 M sentencePredicate,
      ¬ ((theoremPredicate Γ).val.Evalb ![s.val] ∧
        (theoremPredicate Γ).val.Evalb ![NamedArithmeticProofSearch.negationWord M s.val])) :
    theory M Γ ⊓ Idem.pull (negationMap M) (theory M Γ) = ⊥ := by
  apply ArithmeticSetModelLaws.consistent_of_support (theory M Γ)
    (fun s => (theoremPredicate Γ).val.Evalb ![s.val.val])
    ((H).map ((E).map negation)) (theory_support M Γ)
  intro s
  rw [negation_value M s]
  exact hΓ (chart M sentencePredicate s)

theorem theta_theory_pull (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (thetaMap M φ hφ) (theory M Γ) =
      setIdem {n : M | (NamedArithmeticProofSearch.positive Γ φ).val.Evalb ![n]} := by
  have h := ArithmeticSetModelLaws.pull_some_of_support
    (fun n => (H).map (NamedArithmeticLiteralTotal.theta φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n))
    (theory M Γ) (fun s => (theoremPredicate Γ).val.Evalb ![s.val.val])
    (theory_support M Γ)
  apply h.trans
  apply congrArg (fun S : Set M => setIdem S)
  apply Set.ext
  intro n
  change (theoremPredicate Γ).val.Evalb
    ![((H).map (NamedArithmeticLiteralTotal.theta φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)).val.val] ↔
      (NamedArithmeticProofSearch.positive Γ φ).val.Evalb ![n]
  exact (Iff.of_eq (congrArg
    (fun w : M => (theoremPredicate Γ).val.Evalb ![w]) (theta_value M φ hφ n))).trans
      (NamedArithmeticProofSearch.positive_eval M Γ φ n).symm

theorem theta_refutation_pull (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (thetaMap M φ hφ) (Idem.pull (negationMap M) (theory M Γ)) =
      setIdem {n : M | (NamedArithmeticProofSearch.negative Γ φ).val.Evalb ![n]} := by
  have h := ArithmeticSetModelLaws.pull_twice_some_of_support
    (fun n => (H).map (NamedArithmeticLiteralTotal.theta φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n))
    ((H).map ((E).map negation)) (theory M Γ)
    (fun s => (theoremPredicate Γ).val.Evalb ![s.val.val]) (theory_support M Γ)
  apply h.trans
  apply congrArg (fun S : Set M => setIdem S)
  apply Set.ext
  intro n
  exact (Iff.of_eq (congrArg
    (fun w : M => (theoremPredicate Γ).val.Evalb ![w])
    ((negation_value M ((H).map (NamedArithmeticLiteralTotal.theta φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n))).trans
        (congrArg (NamedArithmeticProofSearch.negationWord M) (theta_value M φ hφ n))))).trans
      (NamedArithmeticProofSearch.negative_eval_word M Γ φ hφ n).symm

end CategoricalEssentialIncompleteness.V46.ArithmeticLiteralCoordinates
