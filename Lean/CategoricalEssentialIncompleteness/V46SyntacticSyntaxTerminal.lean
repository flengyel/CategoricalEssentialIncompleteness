/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitution

/-! # The constant-family equivalence at the terminal parameter -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax

section ConstantFamilies
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- The usual inverse to forgetting a terminal parameter agrees with constant families
through the product left unitor. -/
def terminalCFIso :
    (Over.equivalenceOfIsTerminal (terminalIsTerminal (C := C))).inverse ≅
      constantFamilyFunctor (⊤_ C) :=
  NatIso.ofComponents (fun X =>
    Over.isoMk (Limits.prod.leftUnitor X).symm (by
      change prod.lift (terminal.from X) (𝟙 X) ≫ prod.fst = terminal.from X
      exact prod.lift_fst _ _))
    (by
      intro X Y f
      apply Over.OverMorphism.ext
      change f ≫ (Limits.prod.leftUnitor Y).inv =
        (Limits.prod.leftUnitor X).inv ≫ prod.map (𝟙 _) f
      exact (prod.leftUnitor_inv_naturality f).symm)

/-- The functor is literally the constant-family functor. This makes transported algebra
structures comparable to algebraWithParameters by an equality of their structure
morphisms. -/
def terminalCFEquivalence : C ≌ Over (⊤_ C) := by
  let : (constantFamilyFunctor (⊤_ C)).IsEquivalence :=
    Functor.isEquivalence_of_iso (terminalCFIso (C := C))
  exact (constantFamilyFunctor (⊤_ C)).asEquivalence

@[simp] theorem terminalCFEquivalence_functor :
    (terminalCFEquivalence (C := C)).functor = constantFamilyFunctor (⊤_ C) := rfl

omit [Category.{v} C] [HasFiniteLimits C] in
theorem mapCoefficients_id (a : SyntaxPolynomial C) : a.mapCoefficients id = a := by
  induction a with
  | term => rfl
  | formula => rfl
  | coefficient X => rfl
  | unit => rfl
  | product a b ia ib => simp only [SyntaxPolynomial.mapCoefficients, ia, ib]
  | sum a b ia ib => simp only [SyntaxPolynomial.mapCoefficients, ia, ib]

theorem mapCoefficients_constantFamily (P : C) (a : SyntaxPolynomial C) :
    a.mapCoefficients (constantFamily P) = a.withParameters P := by
  induction a with
  | term => rfl
  | formula => rfl
  | coefficient X => rfl
  | unit => rfl
  | product a b ia ib =>
      simp only [SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.withParameters, ia, ib]
  | sum a b ia ib =>
      simp only [SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.withParameters, ia, ib]

end ConstantFamilies

section BaseInitiality
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

/-- The terminal slice comparison is an isomorphism before any initial
algebra is supplied. Products use the already proved constant-family
product isomorphism, and sums use preservation by the CF equivalence. -/
theorem terminalParameterComparison_isIso (X : D × D) (p : SyntaxPolynomial D) :
    IsIso (SyntaxPolynomial.parameterComparison (⊤_ D) X p) := by
  let F := constantFamilyFunctor (⊤_ D)
  let : F.IsEquivalence := Functor.isEquivalence_of_iso (terminalCFIso (C := D))
  induction p with
  | term => change IsIso (𝟙 _); infer_instance
  | formula => change IsIso (𝟙 _); infer_instance
  | coefficient C => change IsIso (𝟙 _); infer_instance
  | unit =>
      have hF : IsTerminal (F.obj (⊤_ D)) :=
        terminalIsTerminal.ofIso (asIso (terminalComparison F)).symm
      exact isIso_of_isTerminal terminalIsTerminal hF (constantUnitComparison (⊤_ D))
  | product p q hp hq =>
      let := hp
      let := hq
      let : IsIso (constantProductComparison (⊤_ D) (p.eval.obj X) (q.eval.obj X)) :=
        (parameterStepIso (⊤_ D) (p.eval.obj X) (q.eval.obj X)).isIso_inv
      change IsIso (prod.map (SyntaxPolynomial.parameterComparison (⊤_ D) X p)
        (SyntaxPolynomial.parameterComparison (⊤_ D) X q) ≫
          constantProductComparison (⊤_ D) (p.eval.obj X) (q.eval.obj X))
      infer_instance
  | sum p q hp hq =>
      let := hp
      let := hq
      change IsIso (coprod.map (SyntaxPolynomial.parameterComparison (⊤_ D) X p)
        (SyntaxPolynomial.parameterComparison (⊤_ D) X q) ≫
          coprodComparison F (p.eval.obj X) (q.eval.obj X))
      infer_instance

/-- The inverse components are the parameterComparison morphisms. No coefficient-relabel
transport or constructor comparison is assumed. -/
def terminalPolynomialIso (p : SyntaxPolynomial D) :
    p.eval ⋙ constantFamilyFunctor (⊤_ D) ≅
      (constantFamilyFunctor (⊤_ D)).prod (constantFamilyFunctor (⊤_ D)) ⋙
        (p.withParameters (⊤_ D)).eval := by
  let P := ⊤_ D
  let F := constantFamilyFunctor P
  let β : F.prod F ⋙ (p.withParameters P).eval ≅ p.eval ⋙ F :=
    NatIso.ofComponents (fun X => by
      letI := terminalParameterComparison_isIso X p
      exact asIso (SyntaxPolynomial.parameterComparison P X p)) (by
        intro X Y f
        change (p.withParameters P).eval.map (F.map f.1, F.map f.2) ≫
          SyntaxPolynomial.parameterComparison P Y p =
            SyntaxPolynomial.parameterComparison P X p ≫ F.map (p.eval.map f)
        exact SyntaxPolynomial.parameterComparison_natural P f p)
  exact β.symm

theorem terminalPolynomialIso_inv_app (p : SyntaxPolynomial D) (X : D × D) :
    (terminalPolynomialIso p).inv.app X =
      SyntaxPolynomial.parameterComparison (⊤_ D) X p := rfl

/-- The paired endofunctor comparison retains both term/formula structure morphisms and
all algebra morphisms. -/
def terminalJointIso (p q : SyntaxPolynomial D) :
    SyntaxPolynomial.jointFunctor p q ⋙
      (constantFamilyFunctor (⊤_ D)).prod (constantFamilyFunctor (⊤_ D)) ≅
        (constantFamilyFunctor (⊤_ D)).prod (constantFamilyFunctor (⊤_ D)) ⋙
          SyntaxPolynomial.jointFunctor (p.withParameters (⊤_ D))
            (q.withParameters (⊤_ D)) := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact
      { hom := ((terminalPolynomialIso p).hom.app X, (terminalPolynomialIso q).hom.app X)
        inv := ((terminalPolynomialIso p).inv.app X, (terminalPolynomialIso q).inv.app X)
        hom_inv_id := by
          apply Prod.ext
          · exact Iso.hom_inv_id_app (terminalPolynomialIso p) X
          · exact Iso.hom_inv_id_app (terminalPolynomialIso q) X
        inv_hom_id := by
          apply Prod.ext
          · exact Iso.inv_hom_id_app (terminalPolynomialIso p) X
          · exact Iso.inv_hom_id_app (terminalPolynomialIso q) X }
  · intro X Y f
    exact Prod.ext ((terminalPolynomialIso p).hom.naturality f)
      ((terminalPolynomialIso q).hom.naturality f)

/-- Under this equivalence the transported structure is literally the
parameterized structure, rather than an isomorphic replacement carrier. -/
theorem terminalMappedAlgebra_eq (p q : SyntaxPolynomial D)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    AlgebraTransport.mappedAlgebra
      ((terminalCFEquivalence (C := D)).prod (terminalCFEquivalence (C := D)))
      (terminalJointIso p q) A =
        SyntaxPolynomial.algebraWithParameters p q A (⊤_ D) := rfl

/-- Terminal-parameter initiality reflects to base initiality only after
the complete algebra-category equivalence has been constructed. -/
def initialOfTerminalParameters (p q : SyntaxPolynomial D)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (h : IsInitial (SyntaxPolynomial.algebraWithParameters p q A (⊤_ D))) : IsInitial A := by
  exact (AlgebraTransport.initialIff
    ((terminalCFEquivalence (C := D)).prod (terminalCFEquivalence (C := D)))
    (terminalJointIso p q) A).symm (by
      change IsInitial (SyntaxPolynomial.algebraWithParameters p q A (⊤_ D))
      exact h)

end BaseInitiality

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
