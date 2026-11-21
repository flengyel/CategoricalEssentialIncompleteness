/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationOptionPowers
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationCheckedRoot
public import CategoricalEssentialIncompleteness.V46SyntacticDerivationPolynomialComparison

/-! The total option algebra and validator for the finite rule presentation. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionAlgebra
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {F : D} {N : ℕ} (R : RulePresentation F N)
variable (E : ∀ i : Fin (N + 1), DecidableVariables (finitePower F i.val))

def component (Q : Over F) (i : Fin (N + 1)) {Z : D} (h : R.ruleObject Q i ⟶ Z) :
    R.instances i ⨯ finitePower (OptionSyntax.obj Q.left) i.val ⟶ OptionSyntax.obj Z :=
  prod.map (𝟙 _) (OptionPowers.collect Q.left i.val) ≫
    OptionPowers.liftRoot (CheckedRoot.operation R Q i (E i) h)

@[simp, reassoc] theorem component_matching (Q : Over F) (i : Fin (N + 1))
    {Z : D} (h : R.ruleObject Q i ⟶ Z) :
    (CheckedRoot.matchingMap R Q i ≫ prod.map (𝟙 _)
      (finitePowerMap (coprod.inr : Q.left ⟶ OptionSyntax.obj Q.left) i.val)) ≫
      component R E Q i h = h ≫ coprod.inr := by
  unfold component
  simp only [Category.assoc]
  rw [← Category.assoc (prod.map _ _) (prod.map _ _), prod.map_map,
    Category.comp_id, OptionPowers.collect_some,
    OptionPowers.liftRoot_some, CheckedRoot.operation_matching]

/-- The supplied H_R-algebra is used only on the ordered-premise pullbacks. Every other
branch is a computed mismatch or child failure. -/
def algebra (Q : Over F) (α : R.inference.obj Q ⟶ Q) :
    Endofunctor.Algebra (PolynomialComparison.ordinary R) where
  a := OptionSyntax.obj Q.left
  str := Sigma.desc (fun i => component R E Q i
    (Sigma.ι (R.ruleObject Q) i ≫ α.left))

def judgementAlgebra : R.inference.obj (Over.mk (𝟙 F)) ⟶ Over.mk (𝟙 F) :=
  Over.homMk (R.inference.obj (Over.mk (𝟙 F))).hom (by simp)

/-- Validation is a total algebra, hence its fold is obtained from the finite-tree
initiality proved in 5.5. Its success fiber is not assumed. -/
def validator : Endofunctor.Algebra (PolynomialComparison.ordinary R) where
  a := OptionSyntax.obj F
  str := Sigma.desc (fun i => component R E (Over.mk (𝟙 F)) i
    (R.ruleConclusion (Over.mk (𝟙 F)) i))

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.OptionAlgebra
