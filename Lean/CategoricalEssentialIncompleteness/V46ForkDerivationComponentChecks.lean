/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationComponent


/-! # The six-tag fork proof carrier as an inference algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Component
open ForkSyntax NumericalTuples
variable (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))

example : formulaObject.dimension = 1 := rfl
example : (proofObject A B hA hB).dimension = 1 := rfl
example (n : ℕ) : code 1 n = n := rfl
example : (rules A B hA hB).instances 0 =
    ∐ (axiomFamily A B hA hB) := rfl
example : (rules A B hA hB).instances 1 = ⊥_ Object := rfl
example : (rules A B hA hB).instances 2 = (formulaObject ⨯ formulaObject) := rfl
example : (rules A B hA hB).premises 2 = prod.lift prod.fst implication := rfl
example : (rules A B hA hB).conclusion 2 = prod.snd := rfl

example (Q : Over formulaObject) : (rules A B hA hB).ruleObject Q 2 =
    pullback (prod.lift prod.fst implication) (finitePowerMap Q.hom 2) := rfl
example (Q : Over formulaObject) :
    (rules A B hA hB).ruleConclusion Q 2 = pullback.fst _ _ ≫ prod.snd := rfl

example (x : Point (proofObject A B hA hB)) :
    ((conclusion A B hA hB).toFun x).val = ForkSyntax.conclusionCode x.val :=
  conclusion_value A B hA hB x
example (t : ProofTree) (ht : ProofTree.Valid A B t) :
    (proofPoint A B hA hB t ht).val = t.encode := rfl
example {t : ProofTree} {p : Formula} (ht : Concludes A B t p) :
    ((conclusion A B hA hB).toFun (proofPoint A B hA hB t ⟨p,ht⟩)).val = p.encode :=
  proofPoint_conclusion A B hA hB ht

example (p q : Formula) :
    (((rules A B hA hB).conclusion 0).toFun (logical1Label A B hA hB p q)).val = (H1 p q).encode :=
  logical1Label_conclusion A B hA hB p q
example (p q r : Formula) :
    (((rules A B hA hB).conclusion 0).toFun (logical2Label A B hA hB p q r)).val = (H2 p q r).encode :=
  logical2Label_conclusion A B hA hB p q r
example (p q : Formula) :
    (((rules A B hA hB).conclusion 0).toFun (logical3Label A B hA hB p q)).val = (H3 p q).encode :=
  logical3Label_conclusion A B hA hB p q
example (z : ℕ) (hz : z ∈ A) :
    (((rules A B hA hB).conclusion 0).toFun (positiveLabel A B hA hB z hz)).val = (Formula.atom z).encode :=
  positiveLabel_conclusion A B hA hB z hz
example (z : ℕ) (hz : z ∈ B) :
    (((rules A B hA hB).conclusion 0).toFun (negativeLabel A B hA hB z hz)).val =
      (Formula.neg (.atom z)).encode := negativeLabel_conclusion A B hA hB z hz

example (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    firstPoint ((pullback.snd ((rules A B hA hB).premises 2)
      (finitePowerMap Q.hom 2)).toFun (mpInputPoint A B hA hB Q p q x y hx hy)) = x :=
  mpInputPoint_first A B hA hB Q p q x y hx hy
example (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    secondPoint ((pullback.snd ((rules A B hA hB).premises 2)
      (finitePowerMap Q.hom 2)).toFun (mpInputPoint A B hA hB Q p q x y hx hy)) = y :=
  mpInputPoint_second A B hA hB Q p q x y hx hy
example (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    (((rules A B hA hB).ruleConclusion Q 2).toFun
      (mpInputPoint A B hA hB Q p q x y hx hy)).val = q.encode :=
  mpInputPoint_conclusion A B hA hB Q p q x y hx hy

example : Endofunctor.Algebra (rules A B hA hB).inference := algebra A B hA hB
example : algebra A B hA hB ≅ NumericalDerivation.codeAlgebra (rules A B hA hB) :=
  algebraIso A B hA hB
example : IsInitial (algebra A B hA hB) := initial A B hA hB

example (p q : Formula) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (logical1Label A B hA hB p q)) =
      proofPoint A B hA hB (.logical1 p q) ⟨_,Concludes.logical1 p q⟩ :=
  algebra_logical1 A B hA hB p q
example (p q r : Formula) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (logical2Label A B hA hB p q r)) =
      proofPoint A B hA hB (.logical2 p q r) ⟨_,Concludes.logical2 p q r⟩ :=
  algebra_logical2 A B hA hB p q r
example (p q : Formula) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (logical3Label A B hA hB p q)) =
      proofPoint A B hA hB (.logical3 p q) ⟨_,Concludes.logical3 p q⟩ :=
  algebra_logical3 A B hA hB p q
example (z : ℕ) (hz : z ∈ A) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (positiveLabel A B hA hB z hz)) =
      proofPoint A B hA hB (.positive z) ⟨_,Concludes.positive hz⟩ := algebra_positive A B hA hB z hz
example (z : ℕ) (hz : z ∈ B) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (negativeLabel A B hA hB z hz)) =
      proofPoint A B hA hB (.negative z) ⟨_,Concludes.negative hz⟩ := algebra_negative A B hA hB z hz
example {t u : ProofTree} {p q : Formula}
    (ht : Concludes A B t p) (hu : Concludes A B u (.imp p q)) :
    (algebra A B hA hB).str.left.toFun
      (mpNodePoint A B hA hB (algebra A B hA hB).a p q
        (proofPoint A B hA hB t ⟨p,ht⟩) (proofPoint A B hA hB u ⟨_,hu⟩)
        (proofPoint_conclusion A B hA hB ht) (proofPoint_conclusion A B hA hB hu)) =
      proofPoint A B hA hB (.mp t u) ⟨q,Concludes.mp ht hu⟩ := algebra_mp A B hA hB ht hu

example : (codeIso A B hA hB).hom ≫ NumericalDerivation.codeConclusion (rules A B hA hB) =
    conclusion A B hA hB := codeIso_conclusion A B hA hB
example : (algebra A B hA hB).str ≫ (algebraIso A B hA hB).hom.f =
    (rules A B hA hB).inference.map (algebraIso A B hA hB).hom.f ≫
      (NumericalDerivation.codeAlgebra (rules A B hA hB)).str := codeIso_constructor A B hA hB
example : (NumericalDerivation.codeAlgebra (rules A B hA hB)).str ≫
    (algebraIso A B hA hB).inv.f =
    (rules A B hA hB).inference.map (algebraIso A B hA hB).inv.f ≫
      (algebra A B hA hB).str := codeIso_inverse_constructor A B hA hB
example (n : Node A B (algebra A B hA hB).a) :
    (codeIso A B hA hB).hom.toFun
      ((algebra A B hA hB).str.left.toFun (nodeInput A B hA hB _ n)) =
      (NumericalDerivation.codeAlgebra (rules A B hA hB)).str.left.toFun
        (nodeInput A B hA hB _ (nodeMap A B (algebraIso A B hA hB).hom.f n)) := codeIso_node A B hA hB n

example (C : Endofunctor.Algebra (rules A B hA hB).inference)
    (f g : algebra A B hA hB ⟶ C) : f = g := (initial A B hA hB).hom_ext f g
example (C : Endofunctor.Algebra (rules A B hA hB).inference) :
    ∃ f : algebra A B hA hB ⟶ C,∀ g : algebra A B hA hB ⟶ C,g = f :=
  ⟨(initial A B hA hB).to C,fun g => (initial A B hA hB).hom_ext g _⟩

example : Partrec (oldToCodeProgram A B hA hB) := oldToCodeProgram_partrec A B hA hB
example : Partrec (codeToOldProgram A B hA hB) := codeToOldProgram_partrec A B hA hB
example (n k : ℕ) : k ∈ oldToCodeProgram A B hA hB n ↔
    ∃ x : Point (proofObject A B hA hB),x.val = n ∧ ((codeIso A B hA hB).hom.toFun x).val = k :=
  oldToCodeProgram_graph A B hA hB n k
example (x : Point (proofObject A B hA hB)) :
    (oldToCodeProgram A B hA hB x.val).bind (codeToOldProgram A B hA hB) = Part.some x.val :=
  oldToCodeProgram_roundtrip A B hA hB x
example (x : Point (NumericalDerivation.codeObject (rules A B hA hB))) :
    (codeToOldProgram A B hA hB x.val).bind (oldToCodeProgram A B hA hB) = Part.some x.val :=
  codeToOldProgram_roundtrip A B hA hB x
end CategoricalEssentialIncompleteness.V46.ForkDerivation.Component
