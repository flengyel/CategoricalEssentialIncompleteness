import CategoricalEssentialIncompleteness.V46MillerNamedProofImageAbsenceReflection

/-! # All actual seven-scheme parameters yield finite native Γ proofs

The target success points prove both native FreeFor conditions and their
literal substitution results. The distribution parameter is reflected
through the actual false classifier and the PA false fiber. No logical
scheme coverage, source axiom admissibility or semantic validity premise
is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace V46MillerNamedProofImageAbsenceReflectionChecks
open CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.SchemeReflection
open NamedFiniteSyntax NamedPostfixEncoding
open Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (p : (U).obj (S).distributionParameters) :
    let base := (U).map (S).distributionInclusion p
    ((U).map prod.fst base).val ∉
      (decodeFormula P σ π d ((U).map prod.fst ((U).map prod.snd base))).freeVariables := distribution_absent P σ π d p

example (A₀ B₀ : PredicateCategory 𝗣𝗔)
    (X₀ Y₀ : Total.TotalCategory P) (e : (F).obj A₀ ≅ X₀) (β : (F).obj B₀ ≅ Y₀)
    (f a : A₀ ⟶ B₀) (g c : X₀ ⟶ Y₀)
    (hs : e.hom ≫ g=(F).map f ≫ β.hom)
    (hc : e.hom ≫ c=(F).map a ≫ β.hom)
    (q₀ : (N).obj A₀) (x : (U).obj X₀)
    (hq : (U).map e.hom (sourcePoint P A₀ q₀)=x)
    (ht : (U).map g x=(U).map c x) : (N).map f q₀=(N).map a q₀ := source_point_reflection P A₀ B₀ X₀ Y₀ e β f a g c hs hc q₀ x hq ht

end V46MillerNamedProofImageAbsenceReflectionChecks
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
