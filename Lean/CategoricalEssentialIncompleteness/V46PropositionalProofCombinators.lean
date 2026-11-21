/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationInference
public import CategoricalEssentialIncompleteness.V46FirstOrderInference
public import CategoricalEssentialIncompleteness.V46ErasureLogicalSchemes

/-! # Uniform finite propositional derivations in an inference algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PropositionalProofCombinators
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {F Ax W U : C} {axioms : Ax ⟶ F} {imp : F ⨯ F ⟶ F}
variable (A : Endofunctor.Algebra (ForkInference.rules axioms imp).inference)

def implies (imp : F ⨯ F ⟶ F) (f g : W ⟶ F) : W ⟶ F := prod.lift f g ≫ imp

/-- A uniform derivation on its parameter object. -/
structure Proof (f : W ⟶ F) where
  hom : W ⟶ A.a.left
  conclusion : hom ≫ A.a.hom = f

namespace Proof
variable {A}

def precomp {f : W ⟶ F} (p : Proof A f) (k : U ⟶ W) : Proof A (k ≫ f) where
  hom := k ≫ p.hom
  conclusion := by rw [Category.assoc, p.conclusion]

def restate {f g : W ⟶ F} (p : Proof A f) (h : f = g) : Proof A g where
  hom := p.hom
  conclusion := p.conclusion.trans h

def axiomInstance (k : W ⟶ Ax) : Proof A (k ≫ axioms) where
  hom := k ≫ (ForkInference.rules axioms imp).nullaryToProof A
  conclusion := by rw [Category.assoc, RulePresentation.nullaryToProof_conclusion]; rfl

/-- The two children retain their order: H, then H ⇒ K. -/
def mp {f g : W ⟶ F} (p : Proof A f) (q : Proof A (implies imp f g)) : Proof A g where
  hom := (pullback.lift (prod.lift f g) (prod.lift p.hom q.hom) (by
      change prod.lift f g ≫ ForkInference.premise imp =
        prod.lift p.hom q.hom ≫ prod.map A.a.hom A.a.hom
      apply prod.hom_ext <;>
        simp [ForkInference.premise, implies, p.conclusion, q.conclusion])) ≫
    Sigma.ι ((ForkInference.rules axioms imp).ruleObject A.a) 2 ≫ A.str.left
  conclusion := by
    have hc : A.str.left ≫ A.a.hom =
        Sigma.desc ((ForkInference.rules axioms imp).ruleConclusion A.a) := Over.w A.str
    rw [Category.assoc, Category.assoc, hc]
    erw [Sigma.ι_comp_desc]
    change (pullback.lift (prod.lift f g) (prod.lift p.hom q.hom) _) ≫
      pullback.fst _ _ ≫ (prod.snd : F ⨯ F ⟶ F) = g
    simp only [pullback.lift_fst_assoc, prod.lift_snd]


end Proof

/-- These are witnesses for the three nullary propositional schemes.
The concrete fork witnesses are constructed from its Fin 5 axiom presentation. -/
structure Schemes (neg : F ⟶ F) where
  one : Proof A (ErasureLogicalSchemes.one imp)
  two : Proof A (ErasureLogicalSchemes.two imp)
  three : Proof A (ErasureLogicalSchemes.three neg imp)

namespace Schemes
variable {A} {neg : F ⟶ F} (H : Schemes A neg)

def oneProof (f g : W ⟶ F) : Proof A (implies imp f (implies imp g f)) where
  hom := prod.lift f g ≫ H.one.hom
  conclusion := by
    rw [Category.assoc, H.one.conclusion]
    simp [ErasureLogicalSchemes.one, implies, prod.comp_lift_assoc]

def twoProof (f g h : W ⟶ F) : Proof A
    (implies imp (implies imp f (implies imp g h))
      (implies imp (implies imp f g) (implies imp f h))) where
  hom := prod.lift (prod.lift f g) h ≫ H.two.hom
  conclusion := by
    rw [Category.assoc, H.two.conclusion]
    simp [ErasureLogicalSchemes.two, implies, prod.comp_lift_assoc]

/-- The two-modus-ponens derivation of H ⇒ H, uniformly in H. -/
def identity (f : W ⟶ F) : Proof A (implies imp f f) :=
  Proof.mp (H.oneProof f f)
    (Proof.mp (H.oneProof f (implies imp f f)) (H.twoProof f (implies imp f f) f))

def weaken {f : W ⟶ F} (p : Proof A f) (g : W ⟶ F) : Proof A (implies imp g f) :=
  Proof.mp p (H.oneProof f g)

end Schemes

end CategoricalEssentialIncompleteness.V46.PropositionalProofCombinators
