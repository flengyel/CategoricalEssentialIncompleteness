/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionLists

/-! # Positive axiom records in the signed first-order derivation polynomial -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation

/-- The nullary rule labels are logical labels or signed nonlogical labels. -/
def axiomCarrier (L A B : Carrier) : Carrier :=
  PredicateInterpretation.sumCarrier L (PredicateInterpretation.sumCarrier A B)

def ruleCoefficients (L A B R₁ R₂ : Carrier) : ℕ → Carrier
  | 0 => axiomCarrier L A B
  | 1 => R₁
  | _ + 2 => R₂

def rulePolynomial (L A B R₁ R₂ : Carrier) : RawPolynomial :=
  SyntaxPolynomial.constructors (ruleCoefficients L A B R₁ R₂) 2

/-- The outer tag is the term sort. The next two tags select a nullary
rule; its coefficient selects a nonlogical axiom and then its sign. -/
def leafGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “o n sign. ∃ a b c d e, !pairDef.val a n sign ∧ !pairDef.val b a 1 ∧
    !pairDef.val c b 0 ∧ !pairDef.val d c 0 ∧ !pairDef.val e d 0 ∧ !pairDef.val o e 0”

def labelGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “n r. ∃ a b c d e, !pi₁Def.val a r ∧ !pi₁Def.val b a ∧
    !pi₁Def.val c b ∧ !pi₁Def.val d c ∧ !pi₁Def.val e d ∧ !pi₁Def.val n e”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def leaf (n sign : M) : M := ⟪⟪⟪⟪⟪⟪n, sign⟫, 1⟫, 0⟫, 0⟫, 0⟫, 0⟫

def label (r : M) : M := π₁ (π₁ (π₁ (π₁ (π₁ (π₁ r)))))

@[simp] theorem leafGraph_eval (o n sign : M) :
    leafGraph.val.Evalb ![o, n, sign] ↔ o = leaf n sign := by
  simp [leafGraph, leaf]

@[simp] theorem labelGraph_eval (n r : M) :
    labelGraph.val.Evalb ![n, r] ↔ n = label r := by
  simp [labelGraph, label, pi₁_defined.iff]

instance leaf_defined : 𝚺₁-Function₂ (leaf : M → M → M) via leafGraph :=
  .mk fun v => by
    have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
    simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using
      leafGraph_eval (v 0) (v 1) (v 2)
instance leaf_definable : 𝚺₁-Function₂ (leaf : M → M → M) := leaf_defined.to_definable
instance leaf_definable' (Γ m) : Γ-[m + 1]-Function₂ (leaf : M → M → M) :=
  leaf_definable.of_sigmaOne
instance label_defined : 𝚺₁-Function₁ (label : M → M) via labelGraph :=
  .mk fun v => by
    have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
    simpa only [hv, Fin.succ_zero_eq_one] using labelGraph_eval (v 0) (v 1)
instance label_definable : 𝚺₁-Function₁ (label : M → M) := label_defined.to_definable
instance label_definable' (Γ m) : Γ-[m + 1]-Function₁ (label : M → M) :=
  label_definable.of_sigmaOne

@[simp] theorem label_leaf (n sign : M) : label (leaf n sign) = n := by simp [label, leaf]

@[simp] theorem leaf_inj (n m s t : M) : leaf n s = leaf m t ↔ n = m ∧ s = t := by
  simp [leaf]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem rawCarrier_coefficient (X Y A : Carrier) (n : M) :
    (rawCarrier X Y (.coefficient A)).val.Evalb ![n] ↔ A.val.Evalb ![n] := Iff.rfl

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem rawCarrier_unit (X Y : Carrier) (n : M) :
    (rawCarrier X Y .unit).val.Evalb ![n] ↔ n = 0 := by simp [rawCarrier]

/-- The records are those of the ordinary ordered rule tree, before
successful conclusion validation. Their coefficients already certify the
positive or negative axiom predicate. -/
@[simp] theorem positive_record (L A B R₁ R₂ : Carrier) (n : M) :
    (Coding.recordCarrier (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![leaf n 0] ↔
      A.val.Evalb ![n] := by
  simp only [Coding.recordCarrier_eval, rulePolynomial, SyntaxPolynomial.constructors,
    SyntaxPolynomial.power, ruleCoefficients, rawCarrier_sum_eval,
    rawCarrier_product_eval, rawCarrier_coefficient, rawCarrier_unit]
  simp only [axiomCarrier, PredicateInterpretation.sumCarrier_eval]
  simp [leaf]

@[simp] theorem negative_record (L A B R₁ R₂ : Carrier) (n : M) :
    (Coding.recordCarrier (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![leaf n 1] ↔
      B.val.Evalb ![n] := by
  simp only [Coding.recordCarrier_eval, rulePolynomial, SyntaxPolynomial.constructors,
    SyntaxPolynomial.power, ruleCoefficients, rawCarrier_sum_eval,
    rawCarrier_product_eval, rawCarrier_coefficient, rawCarrier_unit]
  simp only [axiomCarrier, PredicateInterpretation.sumCarrier_eval]
  simp [leaf]

end Models

open SyntacticSyntax.NatVectors

theorem leaf_primrec : Primrec₂ (leaf : ℕ → ℕ → ℕ) := by
  exact pair_primrec.comp (pair_primrec.comp (pair_primrec.comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.const 1)) (Primrec.const 0)) (Primrec.const 0)) (Primrec.const 0))
    (Primrec.const 0)

theorem label_primrec : Primrec (label : ℕ → ℕ) := by
  exact pi1_primrec.comp (pi1_primrec.comp (pi1_primrec.comp
    (pi1_primrec.comp (pi1_primrec.comp pi1_primrec))))

end CategoricalEssentialIncompleteness.V46.SignedDerivation
