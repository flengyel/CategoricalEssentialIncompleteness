import CategoricalEssentialIncompleteness.V46MillerFiniteAxiomProofs
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open NamedFiniteSyntax NamedPostfixEncoding
variable (σ π:ℕ→SyntacticPredicates.Carrier) (d:ℕ)
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula
  (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

example (L:List ℕ) (n:ℕ) : (finiteCarrier L).val.Evalb (M:=ℕ) ![n] ↔ n∈L := finiteCarrier_eval L n

example {A:Set ℕ} (φ:Fm) (hφ:formulaCode φ∈A) (hclosed:φ.freeVariables=[]) :
    FiniteAxiomProof σ π d A φ := FiniteAxiomProof.axiom_of_mem σ π d φ hφ hclosed

example {A:Set ℕ} (φ ψ:Fm) : FiniteAxiomProof σ π d A (.imp φ (.imp ψ φ)) :=
  FiniteAxiomProof.one σ π d φ ψ

example {A:Set ℕ} (φ ψ χ:Fm) :
    FiniteAxiomProof σ π d A (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))) :=
  FiniteAxiomProof.two σ π d φ ψ χ

example {A:Set ℕ} (φ ψ:Fm) :
    FiniteAxiomProof σ π d A (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) :=
  FiniteAxiomProof.three σ π d φ ψ

example {A:Set ℕ} (x:ℕ) (φ:Fm) (t:Tm) (ψ:Fm)
    (hf:φ.FreeFor x t) (hs:φ.substitute x t=some ψ) :
    FiniteAxiomProof σ π d A (.imp (.all x φ) ψ) := FiniteAxiomProof.instantiation σ π d x φ t ψ hf hs

example {A:Set ℕ} (x:ℕ) (φ ψ:Fm) (hx:x∉φ.freeVariables) :
    FiniteAxiomProof σ π d A (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) :=
  FiniteAxiomProof.distribution σ π d x φ ψ hx

example {A:Set ℕ} (t:Tm) : FiniteAxiomProof σ π d A (.equal t t) := FiniteAxiomProof.reflexivity σ π d t

example {A:Set ℕ} (x:ℕ) (φ:Fm) (u t:Tm) (ψ χ:Fm)
    (hu:φ.FreeFor x u) (ht:φ.FreeFor x t) (hψ:φ.substitute x u=some ψ) (hχ:φ.substitute x t=some χ) :
    FiniteAxiomProof σ π d A (.imp (.equal u t) (.imp ψ χ)) :=
  FiniteAxiomProof.equality σ π d x φ u t ψ χ hu ht hψ hχ

example {A:Set ℕ} (x:ℕ) {φ:Fm} (hφ:FiniteAxiomProof σ π d A φ) :
    FiniteAxiomProof σ π d A (.all x φ) := FiniteAxiomProof.generalization σ π d x hφ

example {A:Set ℕ} {φ ψ:Fm} (hφ:FiniteAxiomProof σ π d A φ)
    (himp:FiniteAxiomProof σ π d A (.imp φ ψ)) : FiniteAxiomProof σ π d A ψ :=
  FiniteAxiomProof.modusPonens σ π d hφ himp

example {A B:Set ℕ} {φ ψ:Fm} (hφ:FiniteAxiomProof σ π d A φ) (hψ:FiniteAxiomProof σ π d B ψ) :
    ∃L:List ℕ,(∀c∈L,c∈A∪B) ∧ SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) ψ :=
  FiniteAxiomProof.common_support σ π d hφ hψ

example {A B:Set ℕ}
    (hAxiom:∀ψ:Fm,formulaCode ψ∈A → ψ.freeVariables=[] → FiniteAxiomProof σ π d B ψ)
    {φ:Fm} (hφ:FiniteAxiomProof σ π d A φ) : FiniteAxiomProof σ π d B φ :=
  FiniteAxiomProof.replace_axioms σ π d hAxiom hφ

example (Γ:SyntacticPredicates.Carrier) {φ:Fm} (h:SyntacticNamedHilbert.Derives σ π d Γ φ) :
    ∃L:List ℕ,(∀c∈L,Γ.val.Evalb (M:=ℕ) ![c]) ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ :=
  FiniteAxiomProof.native_finite_support σ π d Γ h

example (Γ:SyntacticPredicates.Carrier) (φ:Fm) : SyntacticNamedHilbert.Derives σ π d Γ φ ↔
    ∃L:List ℕ,(∀c∈L,Γ.val.Evalb (M:=ℕ) ![c]) ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ := FiniteAxiomProof.native_iff σ π d Γ φ

example {A:Set ℕ} {φ:Fm} (h:FiniteAxiomProof σ π d A φ) :
    ∃L:List ℕ,(∀c∈L,c∈A) ∧ (∀c∈L,∃ψ:Fm,formulaCode ψ=c ∧ ψ.freeVariables=[]) ∧
      SyntacticNamedHilbert.Derives σ π d (finiteCarrier L) φ := FiniteAxiomProof.closed_support σ π d h
