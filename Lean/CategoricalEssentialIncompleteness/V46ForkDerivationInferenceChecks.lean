import CategoricalEssentialIncompleteness.V46ForkDerivationInference
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkInference
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {S Ax : D} (axioms : Ax ⟶ S) (implication : S ⨯ S ⟶ S)

example : (rules axioms implication).instances = ![Ax,⊥_ D,S ⨯ S] := rfl
example : (rules axioms implication).premises 2 = prod.lift prod.fst implication := rfl
example : (rules axioms implication).conclusion 0 = axioms := rfl
example : (rules axioms implication).conclusion 2 = prod.snd := rfl

example (Q : Over S) : mpObject implication Q =
    pullback (prod.lift prod.fst implication) (prod.map Q.hom Q.hom) := rfl
example (Q : Over S) : mpConclusion implication Q =
    pullback.fst (prod.lift prod.fst implication) (prod.map Q.hom Q.hom) ≫ prod.snd := rfl
example (Q : Over S) : ((printedH axioms implication).obj Q).left =
    (Ax ⨿ pullback (prod.lift prod.fst implication) (prod.map Q.hom Q.hom)) := rfl
example (Q : Over S) : ((printedH axioms implication).obj Q).hom =
    coprod.desc axioms (pullback.fst (prod.lift prod.fst implication)
      (prod.map Q.hom Q.hom) ≫ prod.snd) := rfl

example (Q : Over S) : (rules axioms implication).ruleObject Q 0 ≅ Ax :=
  nullaryInputIso axioms implication Q
example (Q : Over S) : IsInitial ((rules axioms implication).ruleObject Q 1) :=
  unaryInputInitial axioms implication Q
example (Q : Over S) : (rules axioms implication).ruleObject Q 2 ≅
    pullback (prod.lift prod.fst implication) (prod.map Q.hom Q.hom) :=
  binaryInputIso axioms implication Q

example : (rules axioms implication).inference ≅ printedH axioms implication :=
  inferenceIso axioms implication
example (Q : Over S) : (rules axioms implication).nullaryRule Q ≫
    Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫
      (inputIso axioms implication Q).hom.left = coprod.inl := inputIso_nullary axioms implication Q
example (Q : Over S) : Sigma.ι ((rules axioms implication).ruleObject Q) 2 ≫
    (inputIso axioms implication Q).hom.left =
      (binaryInputIso axioms implication Q).hom ≫ coprod.inr := inputIso_binary axioms implication Q
example (Q : Over S) : coprod.inl ≫ (inputIso axioms implication Q).inv.left =
    (rules axioms implication).nullaryRule Q ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 0 :=
  inputIso_inv_nullary axioms implication Q
example (Q : Over S) : coprod.inr ≫ (inputIso axioms implication Q).inv.left =
    (binaryInputIso axioms implication Q).inv ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 2 :=
  inputIso_inv_binary axioms implication Q

example (Q : Over S) : (inputIso axioms implication Q).hom.left ≫
    coprod.desc axioms (pullback.fst (prod.lift prod.fst implication) (prod.map Q.hom Q.hom) ≫ prod.snd) =
    Sigma.desc ((rules axioms implication).ruleConclusion Q) := inputIso_conclusion axioms implication Q
example (Q : Over S) : (inputIso axioms implication Q).inv.left ≫
    Sigma.desc ((rules axioms implication).ruleConclusion Q) =
    coprod.desc axioms (pullback.fst (prod.lift prod.fst implication) (prod.map Q.hom Q.hom) ≫ prod.snd) :=
  inputIso_inverse_conclusion axioms implication Q
example {Q Q' : Over S} (f : Q ⟶ Q') :
    (rules axioms implication).inference.map f ≫ (inferenceIso axioms implication).hom.app Q' =
      (inferenceIso axioms implication).hom.app Q ≫ (printedH axioms implication).map f :=
  (inferenceIso axioms implication).hom.naturality f
end CategoricalEssentialIncompleteness.V46.ForkInference
