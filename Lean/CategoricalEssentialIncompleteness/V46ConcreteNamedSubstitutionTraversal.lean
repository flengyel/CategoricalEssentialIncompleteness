/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! A numerical forward stack traversal with explicit root computations.
Every error test concerns only a sort tag, stack shape, or numerical equality.
The root graphs are total numerical functions in PA; no signature-predicate
nonmembership test and no categorical evaluator is supplied. -/

@[expose] public section
noncomputable section
local instance primitiveNamedTraversalDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
open SyntacticSyntax SyntacticSyntax.Coding

/-- Root graphs have order (output, encoded external parameters, raw tuple).
They compute even on tuples outside the eventual typed source. -/
def stepGraph (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 4 :=
  let A := refillGraph a
  let B := refillGraph b
  .mkSigma “out param record state. ∃ s k st l lv ls r rv rs tv fv tb fb ts fs,
    !pi₁Def.val s record ∧ !pi₂Def.val k record ∧ !subDef.val st state 1 ∧
    !A.val l s st ∧ !fstIdxDef.val lv l ∧ !sndIdxDef.val ls l ∧
    !B.val r s st ∧ !fstIdxDef.val rv r ∧ !sndIdxDef.val rs r ∧
    !F.val tv param lv ∧ !G.val fv param rv ∧
    !pairDef.val tb tv 0 ∧ !pairDef.val fb fv 1 ∧
    !adjoinDef.val ts tb ls ∧ !adjoinDef.val fs fb rs ∧
    (((state = 0 ∨ (k = 0 ∧ l = 0) ∨ (k = 1 ∧ r = 0) ∨ (k ≠ 0 ∧ k ≠ 1)) ∧ out = 0) ∨
      (state ≠ 0 ∧ k = 0 ∧ l ≠ 0 ∧ out = ts + 1) ∨
      (state ≠ 0 ∧ k = 1 ∧ r ≠ 0 ∧ out = fs + 1))”

def blueprint (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) : PR.Blueprint 3 where
  zero := .mkSigma “out param word initial. out = initial”
  succ := let S := stepGraph a b F G
    .mkSigma “out prev i param word initial. ∃ record, !nthDef.val record word i ∧
      !S.val out param record prev”

def prefixGraph (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 5 :=
  (blueprint a b F G).resultDef

def prefixValueGraph (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 5 :=
  let R := prefixGraph a b F G
  .mkSigma “out param word n initial. !R.val out n param word initial”

def runGraph (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 4 :=
  let R := prefixGraph a b F G
  .mkSigma “out param word initial. ∃ n, !lenDef.val n word ∧ !R.val out n param word initial”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
  (f g : M → M → M) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
local instance primitiveNamedTraversalModelDecidableEq : DecidableEq M := Classical.decEq M

def step (param record state : M) : M :=
  let l := refill a (π₁ record) (state - 1)
  let r := refill b (π₁ record) (state - 1)
  if state = 0 then 0 else
    if π₂ record = 0 then
      if l = 0 then 0 else adjoin ⟪f param (fstIdx l), 0⟫ (sndIdx l) + 1
    else if π₂ record = 1 then
      if r = 0 then 0 else adjoin ⟪g param (fstIdx r), 1⟫ (sndIdx r) + 1
    else 0

@[simp] theorem stepGraph_eval (out param record state : M) :
    (stepGraph a b F G).val.Evalb ![out,param,record,state] ↔
      out = step a b f g param record state := by
  have hh : (stepGraph a b F G).val.Evalb ![out,param,record,state] ↔
      (((state = 0 ∨ (π₂ record = 0 ∧ refill a (π₁ record) (state - 1) = 0) ∨
          (π₂ record = 1 ∧ refill b (π₁ record) (state - 1) = 0) ∨
          (π₂ record ≠ 0 ∧ π₂ record ≠ 1)) ∧ out = 0) ∨
        (state ≠ 0 ∧ π₂ record = 0 ∧ refill a (π₁ record) (state - 1) ≠ 0 ∧
          out = adjoin ⟪f param (fstIdx (refill a (π₁ record) (state - 1))), 0⟫
            (sndIdx (refill a (π₁ record) (state - 1))) + 1) ∨
        (state ≠ 0 ∧ π₂ record = 1 ∧ refill b (π₁ record) (state - 1) ≠ 0 ∧
          out = adjoin ⟪g param (fstIdx (refill b (π₁ record) (state - 1))), 1⟫
            (sndIdx (refill b (π₁ record) (state - 1))) + 1)) := by
    simp [stepGraph, (show 𝚺₁-Function₂ f via F from inferInstance).iff,
      (show 𝚺₁-Function₂ g via G from inferInstance).iff]
  rw [hh]
  by_cases hz : state = 0 <;> by_cases hk₀ : π₂ record = 0 <;>
    by_cases hk₁ : π₂ record = 1 <;>
    by_cases hl : refill a (π₁ record) (state - 1) = 0 <;>
    by_cases hr : refill b (π₁ record) (state - 1) = 0 <;> simp_all [step]

def construction : PR.Construction M (blueprint a b F G) where
  zero p := p 2
  succ p i prev := step a b f g (p 0) (nth (p 1) i) prev
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by simp [blueprint]

def runPrefix (param word n initial : M) : M :=
  (construction a b F G f g).result ![param,word,initial] n

def run (param word initial : M) : M := runPrefix a b F G f g param word (len word) initial

@[simp] theorem prefix_zero (param word initial : M) :
    runPrefix a b F G f g param word 0 initial = initial := by
  simp [runPrefix, construction]
@[simp] theorem prefix_succ (param word n initial : M) :
    runPrefix a b F G f g param word (n + 1) initial =
      step a b f g param (nth word n) (runPrefix a b F G f g param word n initial) := by
  simp [runPrefix, construction]

@[simp] theorem prefixGraph_eval (out n param word initial : M) :
    (prefixGraph a b F G).val.Evalb ![out,n,param,word,initial] ↔
      out = runPrefix a b F G f g param word n initial := by
  have hp : (fun i : Fin 3 => ![out,n,param,word,initial] i.succ.succ) =
      ![param,word,initial] := by funext i; fin_cases i <;> rfl
  simpa [prefixGraph,runPrefix,hp] using
    (construction a b F G f g).result_defined_iff ![out,n,param,word,initial]

@[simp] theorem prefixGraph_eval_vec (v : Fin 5 → M) :
    (prefixGraph a b F G).val.Evalb v ↔
      v 0 = runPrefix a b F G f g (v 2) (v 3) (v 1) (v 4) := by
  have hv : ![v 0,v 1,v 2,v 3,v 4] = v := by funext i; fin_cases i <;> rfl
  simpa [hv] using prefixGraph_eval a b F G f g (v 0) (v 1) (v 2) (v 3) (v 4)

theorem prefix_defined :
    𝚺₁-Function₄ (runPrefix a b F G f g : M → M → M → M → M) via
      prefixValueGraph a b F G := .mk fun v => by
  simp [prefixValueGraph,prefixGraph_eval_vec a b F G f g]
instance prefix_definable : 𝚺₁-Function₄ (runPrefix a b F G f g : M → M → M → M → M) :=
  (prefix_defined a b F G f g).to_definable
instance prefix_definable' (Γ m) :
    Γ-[m + 1]-Function₄ (runPrefix a b F G f g : M → M → M → M → M) :=
  (prefix_definable a b F G f g).of_sigmaOne

@[simp] theorem runGraph_eval (out param word initial : M) :
    (runGraph a b F G).val.Evalb ![out,param,word,initial] ↔
      out = run a b F G f g param word initial := by
  simp [runGraph,run,prefixGraph_eval_vec a b F G f g]
theorem run_defined : 𝚺₁-Function₃ (run a b F G f g : M → M → M → M) via runGraph a b F G :=
  .mk fun v => by
    have hv : ![v 0,v 1,v 2,v 3] = v := (Matrix.fun_eq_vec_four v).symm
    simpa [hv] using runGraph_eval a b F G f g (v 0) (v 1) (v 2) (v 3)
instance run_definable : 𝚺₁-Function₃ (run a b F G f g : M → M → M → M) :=
  (run_defined a b F G f g).to_definable
instance run_definable' (Γ m) : Γ-[m + 1]-Function₃ (run a b F G f g : M → M → M → M) :=
  (run_definable a b F G f g).of_sigmaOne

@[simp] theorem step_zero (param record : M) : step a b f g param record 0 = 0 := by simp [step]
@[simp] theorem run_nil (param initial : M) : run a b F G f g param 0 initial = initial := by simp [run]
end Models

open SyntacticSyntax.NatVectors

/-- A certificate is derived from the actual numerical root functions.
This lemma does not infer primitive recursion from an arbitrary T-total graph. -/
theorem step_primrec (a b : RawPolynomial) (f g : ℕ → ℕ → ℕ)
    (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec (fun p : ℕ × ℕ × ℕ => step a b f g p.1 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hr : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hshape := pi1_primrec.comp hr
  have htag := pi2_primrec.comp hr
  have hstack := arithmetic_sub_primrec.comp hs (Primrec.const 1)
  have hl := (refill_primrec a).comp hshape hstack
  have hu := (refill_primrec b).comp hshape hstack
  have hleft := Primrec.succ.comp <| adjoin_primrec.comp
    (pair_primrec.comp (hf.comp hp (fstIdx_primrec.comp hl)) (Primrec.const 0))
    (sndIdx_primrec.comp hl)
  have hright := Primrec.succ.comp <| adjoin_primrec.comp
    (pair_primrec.comp (hg.comp hp (fstIdx_primrec.comp hu)) (Primrec.const 1))
    (sndIdx_primrec.comp hu)
  exact Primrec.ite (Primrec.eq.comp hs (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp hl (Primrec.const 0)) (Primrec.const 0) hleft)
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
        (Primrec.ite (Primrec.eq.comp hu (Primrec.const 0)) (Primrec.const 0) hright)
        (Primrec.const 0)))

theorem runPrefix_primrec (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
    (f g : ℕ → ℕ → ℕ) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
    (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec (fun p : (ℕ × ℕ × ℕ) × ℕ =>
      runPrefix a b F G f g p.1.1 p.1.2.1 p.2 p.1.2.2) := by
  have hz : Primrec (fun p : ℕ × ℕ × ℕ =>
      (construction a b F G f g).zero ![p.1,p.2.1,p.2.2]) :=
    Primrec.snd.comp Primrec.snd
  have hs : Primrec₂ (fun (p : ℕ × ℕ × ℕ) (t : ℕ × ℕ) =>
      (construction a b F G f g).succ ![p.1,p.2.1,p.2.2] t.1 t.2) :=
    (step_primrec a b f g hf hg).comp (Primrec.pair
      (Primrec.fst.comp Primrec.fst)
      (Primrec.pair
        (nth_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)))
  exact pr_primrec (construction a b F G f g)
    (fun p : ℕ × ℕ × ℕ => ![p.1,p.2.1,p.2.2]) hz hs

private theorem atLength_primrec {r : ((ℕ × ℕ × ℕ) × ℕ) → ℕ} (hr : Primrec r) :
    Primrec (fun p : ℕ × ℕ × ℕ => r (p,len p.2.1)) :=
  hr.comp (Primrec.pair Primrec.id (len_primrec.comp (Primrec.fst.comp Primrec.snd)))

theorem run_primrec (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
    (f g : ℕ → ℕ → ℕ) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
    (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Primrec (fun p : ℕ × ℕ × ℕ => run a b F G f g p.1 p.2.1 p.2.2) := by
  exact Primrec.of_eq (atLength_primrec (runPrefix_primrec a b F G f g hf hg)) (fun _ => rfl)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
