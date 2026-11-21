/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedPolynomialRepresentation


/-! # Exact scalar graph of the polynomial input chart -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family) (X Y : PredicateCategory 𝗣𝗔) (X' Y' : Total.TotalCategory P)
  (iX : X' ≅ (Syntax.predicateFunctor P).obj X)
  (iY : Y' ≅ (Syntax.predicateFunctor P).obj Y)
  (hX : ∀ u v,v∈Total.val iX.hom.hom u ↔ u∈X'.obj.support ∧ v=u)
  (hY : ∀ u v,v∈Total.val iY.hom.hom u ↔ u∈Y'.obj.support ∧ v=u)

example (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (u : ℕ)
    (z : PredicateInterpretation.Obj ℕ (p.eval.obj (X,Y))) :
    z.val∈Total.val (inputIso P X Y X' Y' iX iY p).hom.hom u ↔
      (SyntacticSyntax.baseRepresentation 𝗣𝗔 X Y p).val.Evalb (M := ℕ) ![u,z.val] :=
  inputIso_graph P X Y X' Y' iX iY hX hY p u z

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
