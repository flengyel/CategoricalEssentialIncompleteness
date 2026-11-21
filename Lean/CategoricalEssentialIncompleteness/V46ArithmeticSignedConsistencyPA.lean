/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSignedContradiction

/-! # PA proves the absence of contradictory diagonal derivation codes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
open SyntacticDerivation
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)
local notation "Q" => derivationAlgebra 𝗣𝗔 (rules S)

/-- The carrier and graphs are those of the signed proof algebra. -/
def consistencySentence : ArithmeticSentence :=
  let D := (Q).a.left
  let C := (chosenGraph 𝗣𝗔 (Q).a.hom).graph
  let G := (chosenGraph 𝗣𝗔 S.negationConstructor).graph
  “∀ p q f n, !D.val p → !D.val q → !C.val p f → !C.val q n → !G.val f n → ⊥”

@[simp] theorem consistencySentence_eval
    {M : Type} [ORingStructure M] :
    (consistencySentence S).Evalb (M := M) ![] ↔
      ∀ p q f n : M,
        (Q).a.left.val.Evalb ![p] → (Q).a.left.val.Evalb ![q] →
        (chosenGraph 𝗣𝗔 (Q).a.hom).graph.val.Evalb ![p, f] →
        (chosenGraph 𝗣𝗔 (Q).a.hom).graph.val.Evalb ![q, n] →
        (chosenGraph 𝗣𝗔 S.negationConstructor).graph.val.Evalb ![f, n] → False := by
  simp [consistencySentence]

/-- PA proves consistency for all internal codes of the signed calculus. -/
theorem consistency_PA : 𝗣𝗔 ⊢ consistencySentence S := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, consistencySentence_eval]
  intro p q f n hp hq hf hn hg
  let pp : Obj 𝗣𝗔 M (Q).a.left := ⟨p, hp⟩
  let qq : Obj 𝗣𝗔 M (Q).a.left := ⟨q, hq⟩
  let ff : Obj 𝗣𝗔 M S.algebra.a.2 :=
    ⟨f, ((chosenGraph 𝗣𝗔 (Q).a.hom).support_model M p f hf).2⟩
  let nn : Obj 𝗣𝗔 M S.algebra.a.2 :=
    ⟨n, ((chosenGraph 𝗣𝗔 (Q).a.hom).support_model M q n hn).2⟩
  have hpf : (F 𝗣𝗔 M).map (Q).a.hom pp = ff :=
    (chosenGraph_map_iff 𝗣𝗔 M (Q).a.hom pp ff).mp hf
  have hqn : (F 𝗣𝗔 M).map (Q).a.hom qq = nn :=
    (chosenGraph_map_iff 𝗣𝗔 M (Q).a.hom qq nn).mp hn
  have hfn : (F 𝗣𝗔 M).map S.negationConstructor ff = nn :=
    (chosenGraph_map_iff 𝗣𝗔 M S.negationConstructor ff nn).mp hg
  apply no_contradictory_derivations S M pp qq
  exact hqn.trans (hfn.symm.trans (congrArg ((F 𝗣𝗔 M).map S.negationConstructor) hpf.symm))

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
