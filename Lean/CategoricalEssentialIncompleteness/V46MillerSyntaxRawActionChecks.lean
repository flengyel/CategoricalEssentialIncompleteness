import CategoricalEssentialIncompleteness.V46MillerSyntaxRawAction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P:Uniform.Family} (R:Total.TotalCategory P) (X Y X' Y':Over R)

example (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) :
    Raw.object R X Y p⟶Raw.object R X' Y' p := Raw.rawAction R X Y X' Y' f g p

example (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) :
    Raw.rawAction R X Y X' Y' f g p ≫ (Raw.comparison R X' Y' p).hom=
      (Raw.comparison R X Y p).hom ≫ (p.withParameters R).eval.map (f,g) :=
  Raw.rawAction_comparison R X Y X' Y' f g p

example (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) :
    Raw.rawAction R X Y X' Y' f g p=(Raw.comparison R X Y p).hom ≫
      (p.withParameters R).eval.map (f,g) ≫ (Raw.comparison R X' Y' p).inv :=
  Raw.rawAction_eq_transported R X Y X' Y' f g p

example (p:SyntaxPolynomial (Total.TotalCategory P)) : Raw.rawAction R X Y X Y (𝟙 X) (𝟙 Y) p=𝟙 _ :=
  Raw.rawAction_id R X Y p

example {X'' Y'':Over R} (f:X⟶X') (g:Y⟶Y') (f':X'⟶X'') (g':Y'⟶Y'')
    (p:SyntaxPolynomial (Total.TotalCategory P)) :
    Raw.rawAction R X Y X'' Y'' (f≫f') (g≫g') p=
      Raw.rawAction R X Y X' Y' f g p ≫ Raw.rawAction R X' Y' X'' Y'' f' g' p :=
  Raw.rawAction_comp R X Y X' Y' f g f' g' p
