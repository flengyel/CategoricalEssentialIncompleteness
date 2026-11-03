/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SentenceImages
import Mathlib.Tactic.FinCases

/-! # Axiom introduction, generalization and modus ponens -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S A A' : D}

namespace RulePresentation

/-- Each nullary rule instance is a proof in any algebra for the rule
endofunctor, with its prescribed conclusion. -/
def nullaryToProof {F : D} {N : ℕ} (R : RulePresentation F N)
    (P : Endofunctor.Algebra R.inference) : R.instances 0 ⟶ P.a.left :=
  R.nullaryRule P.a ≫ Sigma.ι (fun i => R.ruleObject P.a i) 0 ≫ P.str.left

@[reassoc] theorem nullaryToProof_conclusion {F : D} {N : ℕ}
    (R : RulePresentation F N) (P : Endofunctor.Algebra R.inference) :
    R.nullaryToProof P ≫ P.a.hom = R.conclusion 0 := by
  unfold nullaryToProof
  have hc : P.str.left ≫ P.a.hom = Sigma.desc (R.ruleConclusion P.a) := Over.w P.str
  rw [Category.assoc, Category.assoc, hc]
  simp [ruleConclusion, nullaryRule]

end RulePresentation

/-- The first-order rule data of Appendix A.6. The morphism `logical`
is the copairing of the seven logical scheme morphisms. -/
def firstOrderRules (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) : RulePresentation F 2 where
  instances := ![L ⨿ A, V ⨯ F, F ⨯ F]
  premises := Fin.cases (terminal.from _) (Fin.cases prod.snd
    (Fin.cases (prod.lift prod.fst imp) (fun i => Fin.elim0 i)))
  conclusion := Fin.cases (coprod.desc logical (axioms ≫ sentence))
    (Fin.cases all (Fin.cases prod.snd (fun i => Fin.elim0 i)))

/-- The generated formula image contains all logical and nonlogical
axiom instances. -/
theorem firstOrder_axioms_factor (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference) :
    ∃ a : L ⨿ A ⟶ image P.a.hom,
      a ≫ image.ι P.a.hom = coprod.desc logical (axioms ≫ sentence) := by
  refine ⟨(firstOrderRules logical sentence axioms all imp).nullaryToProof P ≫
    factorThruImage P.a.hom, ?_⟩
  rw [Category.assoc, image.fac]
  exact (firstOrderRules logical sentence axioms all imp).nullaryToProof_conclusion P

/-- An inclusion of nonlogical axioms changes only the nullary rule
instances. It preserves all ordered premises and conclusions. -/
def firstOrderAxiomMap (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (axioms' : A' ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (k : A ⟶ A') (hk : k ≫ axioms' = axioms) :
    RulePresentation.Hom (firstOrderRules logical sentence axioms all imp)
      (firstOrderRules logical sentence axioms' all imp) where
  map := Fin.cases (coprod.map (𝟙 L) k)
    (Fin.cases (𝟙 _) (Fin.cases (𝟙 _) (fun i => Fin.elim0 i)))
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · exact Category.id_comp (prod.snd : V ⨯ F ⟶ F)
    · exact Category.id_comp (prod.lift (prod.fst : F ⨯ F ⟶ F) imp)
  conclusion i := by
    fin_cases i
    · change coprod.map (𝟙 L) k ≫ coprod.desc logical (axioms' ≫ sentence) =
        coprod.desc logical (axioms ≫ sentence)
      apply coprod.hom_ext <;> simp [← Category.assoc k, hk]
    · exact Category.id_comp all
    · exact Category.id_comp (prod.snd : F ⨯ F ⟶ F)

/-- For these three typed rules the image of an initial proof algebra
is least among the closed formula subobjects. -/
theorem firstOrder_least_image (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P) :
    ClosedUnder (firstOrderRules logical sentence axioms all imp).inference
      (image.ι P.a.hom) ∧
      ∀ {T : D} (m : T ⟶ F) [Mono m],
        ClosedUnder (firstOrderRules logical sentence axioms all imp).inference m →
          ∃ w : image P.a.hom ⟶ T, w ≫ m = image.ι P.a.hom :=
  (firstOrderRules logical sentence axioms all imp).least_theorem_subobject P hP

/-- Axiom inclusion induces inclusion of generated formula theories. -/
theorem firstOrder_image_monotone (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (axioms' : A' ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (k : A ⟶ A') (hk : k ≫ axioms' = axioms)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P)
    (P' : Endofunctor.Algebra (firstOrderRules logical sentence axioms' all imp).inference) :
    imageSubobject P.a.hom ≤ imageSubobject P'.a.hom :=
  generated_image_monotone
    (firstOrderAxiomMap logical sentence axioms axioms' all imp k hk) P hP P'

/-- The same axiom inclusion holds after restricting conclusions to
sentences. No extra preservation hypothesis on the rule functor is used. -/
theorem firstOrder_sentence_image_monotone (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (axioms' : A' ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (k : A ⟶ A') (hk : k ≫ axioms' = axioms)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P)
    (P' : Endofunctor.Algebra (firstOrderRules logical sentence axioms' all imp).inference) :
    imageSubobject (pullback.snd P.a.hom sentence) ≤
      imageSubobject (pullback.snd P'.a.hom sentence) := by
  rw [sentenceImage_subobject, sentenceImage_subobject]
  exact (Subobject.pullback sentence).monotone
    (firstOrder_image_monotone logical sentence axioms axioms' all imp k hk P hP P')

end CategoricalEssentialIncompleteness.V46
