import CategoricalEssentialIncompleteness.V46MillerNamedProofImagePoints
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedFiniteSyntax NamedPostfixEncoding
open NamedProofImage
open NamedProofImage.Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P:=P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) :
    (U).map (prod.fst : X ⨯ Y ⟶ X) (pairPoint x y)=x := pairPoint_fst x y
example {X Y : Total.TotalCategory P} (x : (U).obj X) (y : (U).obj Y) :
    (U).map (prod.snd : X ⨯ Y ⟶ Y) (pairPoint x y)=y := pairPoint_snd x y
example (φ ψ : Fm) :
    (U).map (S).implicationConstructor (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ))=
      formulaPoint P σ π d (.imp φ ψ) := implication_point P σ π d φ ψ
example (u v : Tm) :
    (U).map (S).equalityConstructor (pairPoint (termPoint P σ π d u) (termPoint P σ π d v))=
      formulaPoint P σ π d (.equal u v) := equality_point P σ π d u v
example (x : ℕ) (φ : Fm) :
    (U).map (S).quantifierConstructor (pairPoint (namePoint P x) (formulaPoint P σ π d φ))=
      formulaPoint P σ π d (.all x φ) := quantifier_point P σ π d x φ
