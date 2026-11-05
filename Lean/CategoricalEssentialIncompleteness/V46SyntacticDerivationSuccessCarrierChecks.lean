import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessCarrier

/-! The success carrier retains the tree code, and its isomorphism respects the tree inclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessCarrier
variable {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {W F : PredicateCategory T}
  (v : @Quiver.Hom (PredicateCategory T) inferInstance W (OptionSyntax.obj F))
example : GraphMorphism T (carrier v) F := conclusion v
example : Over.mk (representedArrow T (conclusion v)) ≅
    (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v) := overIso v
example : (overIso v).hom.left ≫ pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F) =
    representedArrow T (inclusion v) := overIso_tree v
