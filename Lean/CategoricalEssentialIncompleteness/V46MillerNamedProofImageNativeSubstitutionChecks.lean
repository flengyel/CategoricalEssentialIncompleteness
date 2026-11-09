import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitution

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionChecks
open NamedProofImage.NativeSubstitution
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "U" => Total.underlying (P := P)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula
  (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

example : Function.Bijective (optionPoint P σ π d) :=
  ⟨optionPoint_injective P σ π d,optionPoint_surjective P σ π d⟩

example (φ : Fm) : optionPoint P σ π d none ≠ optionPoint P σ π d (some φ) :=
  optionPoint_none_ne_some P σ π d φ

example (v : Option Fm) : decodeOption P σ π d (optionPoint P σ π d v)=v :=
  decode_optionPoint P σ π d v

example (q : (U).obj (OptionSyntax.obj (S).algebra.a.2)) :
    optionPoint P σ π d (decodeOption P σ π d q)=q := optionPoint_decode P σ π d q

example (x : ℕ) :
    (U).map (S).variableConstructor (Points.namePoint P x)=NamedProofImage.termPoint P σ π d (.var x) :=
  variable_point P σ π d x

example (x : ℕ) (r : Tm) :
    termValue P σ π d x (.var x) r=NamedProofImage.termPoint P σ π d r := identity_term P σ π d x r

example (x : ℕ) (φ : Fm) :
    formulaOptionValue P σ π d x (.var x) φ=optionPoint P σ π d (some φ) :=
  identity_option P σ π d x φ

example (x : ℕ) (t : Tm) (φ : Fm) (v : Option Fm) :
    (optionPoint P σ π d v).val∈Total.val (S).formulaSubstitutionOption.hom
      (formulaInput P σ π d x t φ).val ↔ decodedResult P σ π d x t φ=v :=
  option_graph P σ π d x t φ v

example (x : ℕ) (t : Tm) (φ ψ : Fm) :
    (∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t ∧
      (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ) ↔
        decodedResult P σ π d x t φ=some ψ := success_iff P σ π d x t φ ψ

example (x : ℕ) (t : Tm) (φ : Fm) :
    decodedResult P σ π d x t φ=none ↔
      ¬ ∃ a : (U).obj (S).admissibleSubstitution,
        (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x φ t :=
  failure_iff P σ π d x t φ

example (x : ℕ) (t r : Tm) :
    (U).map (prod.fst : (S).substitutionCarriers.1 ⟶ (S).algebra.a.1)
      (termState P σ π d x t r)=NamedProofImage.termPoint P σ π d r :=
  termState_original P σ π d x t r

example (x : ℕ) (t : Tm) (φ : Fm) :
    (U).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)
      (formulaState P σ π d x t φ)=NamedProofImage.formulaPoint P σ π d φ :=
  formulaState_original P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    (U).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj (S).algebra.a.2)
      (formulaState P σ π d x t φ)=formulaOptionValue P σ π d x t φ :=
  formulaState_result P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    formulaOptionValue P σ π d x t (.all x φ)=optionPoint P σ π d (some (.all x φ)) :=
  equal_binder_option P σ π d x t φ

example (x : ℕ) (t : Tm) (φ : Fm) :
    ∃ a : (U).obj (S).admissibleSubstitution,
      (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x (.all x φ) t ∧
      (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d (.all x φ) :=
  equal_binder_success P σ π d x t φ

example (x : ℕ) (t : Tm) (φ ψ : Fm) (a : (U).obj (S).admissibleSubstitution)
    (hi : (U).map (S).admissibleInclusion a=Points.substitutionPoint P σ π d x (.all x φ) t)
    (hr : (U).map (S).formulaSubstitution a=NamedProofImage.formulaPoint P σ π d ψ) :
    ψ=.all x φ := equal_binder_reflection P σ π d x t φ ψ a hi hr

section ActualRoot
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "p" => SyntaxPolynomial.termExpression
  (Functor.obj (Syntax.predicateFunctor P) (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "A" => SyntaxPolynomial.algebraWithParameters p q
  (CategoricalSyntax.algebra (NamedProofImage.syntaxData P σ π d)) R

example (r : (U).obj (R)) (z : PointFrame.Data (R) r (A).a (p)) :
    PointFrame.realize (R) r (A).a (p) z ≫ (A).str.1 ≫ (S).substitutionFold.1=
      PointFrame.realize (R) r (S).substitutionAlgebra.a (p)
        (PointFrame.mapData (R) r (S).substitutionFold (p) z) ≫ (S).substitutionAlgebra.str.1 :=
  term_root_framed P σ π d r z

example (r : (U).obj (R)) (z : PointFrame.Data (R) r (A).a (q)) :
    PointFrame.realize (R) r (A).a (q) z ≫ (A).str.2 ≫ (S).substitutionFold.2=
      PointFrame.realize (R) r (S).substitutionAlgebra.a (q)
        (PointFrame.mapData (R) r (S).substitutionFold (q) z) ≫ (S).substitutionAlgebra.str.2 :=
  formula_root_framed P σ π d r z

example (r : (U).obj (R)) (x : ℕ) (body : Fm) :
    PointFrame.mapData (R) r (S).substitutionFold (q)
      (formulaNodeInput P σ π d r (.all x body))=
        Sum.inr (Points.namePoint P x,formulaLeaf P σ π d r body ≫ (S).substitutionFold.2) :=
  quantified_node_map P σ π d r x body

end ActualRoot

section Frame
variable (R : Total.TotalCategory P) (r : (Total.underlying (P := P)).obj R)
variable (A B : Over R × Over R) (f : A ⟶ B) (p : SyntaxPolynomial (Total.TotalCategory P))

example (z : PointFrame.Data R r A p) :
    PointFrame.realize R r A p z ≫ (p.withParameters R).eval.map f=
      PointFrame.realize R r B p (PointFrame.mapData R r f p z) :=
  PointFrame.realize_natural R r f p z

example (z : PointFrame.Data R r A p) :
    (Total.underlying (P := P)).map ((p.withParameters R).eval.map f).left
      ((Total.underlying (P := P)).map (PointFrame.realize R r A p z).left ⟨0,rfl⟩)=
        (Total.underlying (P := P)).map
          (PointFrame.realize R r B p (PointFrame.mapData R r f p z)).left ⟨0,rfl⟩ :=
  PointFrame.realize_map_point R r f p z

example (n : ℕ) (children : Fin n → (PointFrame.source R r ⟶ A.1)) :
    PointFrame.mapData R r f (SyntaxPolynomial.power .term n)
        (PointFrame.powerData R r A n children)=
      PointFrame.powerData R r B n (fun i => children i ≫ f.1) :=
  PointFrame.powerData_natural R r f n children

example (τ : ℕ → Total.TotalCategory P) (n : ℕ) (k : Fin (n+1))
    (c : (Total.underlying (P := P)).obj (τ k.val))
    (children : Fin k.val → (PointFrame.source R r ⟶ A.1)) :
    PointFrame.mapData R r f (SyntaxPolynomial.constructors τ n)
        (PointFrame.arityData R r A τ n k c children)=
      PointFrame.arityData R r B τ n k c (fun i => children i ≫ f.1) :=
  PointFrame.arityData_natural R r f τ n k c children

end Frame
end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionChecks
