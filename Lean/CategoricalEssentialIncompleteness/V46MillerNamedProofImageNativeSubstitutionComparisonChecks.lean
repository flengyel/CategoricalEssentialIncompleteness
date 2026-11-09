import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionComparisonChecks
open NamedProofImage.NativeSubstitution
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "S₀" => NamedSyntaxComparison.sourceSyntax
  (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

example (x : ℕ) (t r : Tm) :
    termLeaf P σ π d (parameterPoint P σ π d x t) r ≫ (S).substitutionFold.1=
      PointFrame.constant (S).substitutionParameters (parameterPoint P σ π d x t)
        (S).substitutionCarriers.1 (termState P σ π d x t r) := termLeaf_fold P σ π d x t r

example (x : ℕ) (t r : Tm) :
    termState P σ π d x t r=expectedTermState P σ π d x t r := termState_comparison P σ π d x t r

example (x : ℕ) (t r : Tm) :
    (Total.underlying (P := P)).map
      (CategoricalSyntax.termSubstitution (NamedProofImage.syntaxData P σ π d))
      (Points.pairPoint (NamedProofImage.termPoint P σ π d r)
        (Points.pairPoint (Points.namePoint P x) (NamedProofImage.termPoint P σ π d t)))=
      NamedProofImage.termPoint P σ π d (r.substitute x t) := termValue_eq_native P σ π d x t r

example (x : ℕ) (t r : Tm) :
    NamedPostfixEncoding.termCode (r.substitute x t)∈Total.val (S).termSubstitution.hom
      (termInput P σ π d x t r).val := by
  have h := (Total.totalFunction_eq_iff (S).termSubstitution (termInput P σ π d x t r)
    (NamedProofImage.termPoint P σ π d (r.substitute x t))).mp (termValue_eq_native P σ π d x t r)
  simpa only [NamedProofImage.termPoint_value] using h

example (x : ℕ) (t : Tm) (y : ℕ) :
    termValue P σ π d x t (.var y)=NamedProofImage.termPoint P σ π d
      (if y=x then t else .var y) := by
  simpa only [NamedFiniteSyntax.Term.substitute] using termValue_eq_native P σ π d x t (.var y)

example (x : ℕ) (t : Tm) (k : Fin (d+1)) (label : NamedPostfixEncoding.Symbols σ k.val)
    (children : Fin k.val → Tm) :
    termValue P σ π d x t (.app k label children)=NamedProofImage.termPoint P σ π d
      (.app k label (fun i => (children i).substitute x t)) :=
  termValue_eq_native P σ π d x t (.app k label children)

example (x : ℕ) (t : Tm) (label : NamedPostfixEncoding.Symbols σ 0) :
    termValue P σ π d x t (.app (0 : Fin (d+1)) label (fun i => Fin.elim0 i))=
      NamedProofImage.termPoint P σ π d (.app 0 label (fun i => Fin.elim0 i)) := by
  have hf : (fun i : Fin 0 => (Fin.elim0 i : Tm).substitute x t)=
      (fun i : Fin 0 => (Fin.elim0 i : Tm)) := by
    funext i
    exact Fin.elim0 i
  have ht := congrArg (fun children : Fin 0 → Tm =>
    (NamedFiniteSyntax.Term.app (0 : Fin (d+1)) label children : Tm)) hf
  exact (termValue_eq_native P σ π d x t (.app 0 label (fun i => Fin.elim0 i))).trans
    (congrArg (NamedProofImage.termPoint P σ π d) ht)

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionComparisonChecks
