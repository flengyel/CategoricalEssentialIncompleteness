/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionTraversalLaws
public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionMap
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSize
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition

/-! Exact arithmetic constructor laws for the globally total numeric root
traversal. Its output code is a numerical value, with no model-dependent choice. -/

@[expose] public section
noncomputable section
local instance primitiveNamedTraversalConstructorsDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
open SyntacticSyntax SyntacticSyntax.Coding

def numericCarrier : Carrier := .mkSigma “x. x = x”

def outputGraph (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 3 :=
  let R := runGraph a b F G
  .mkSigma “out param word. ∃ state stack block, !R.val state param word 1 ∧
    !subDef.val stack state 1 ∧ !fstIdxDef.val block stack ∧ !pi₁Def.val out block”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
  (f g : M → M → M) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
  (param : M)
local instance primitiveNamedTraversalConstructorsModelDecidableEq : DecidableEq M := Classical.decEq M

def output (word : M) : M := π₁ (fstIdx (run a b F G f g param word 1 - 1))

@[simp] theorem runGraph_eval_any (v : Fin 4 → M) :
    (runGraph a b F G).val.Evalb v ↔ v 0 = run a b F G f g (v 1) (v 2) (v 3) := by
  have hv : ![v 0,v 1,v 2,v 3] = v := (Matrix.fun_eq_vec_four v).symm
  simpa [hv] using runGraph_eval a b F G f g (v 0) (v 1) (v 2) (v 3)

@[simp] theorem outputGraph_eval (out word : M) :
    (outputGraph a b F G).val.Evalb ![out,param,word] ↔ out = output a b F G f g param word := by
  simp [outputGraph,output,runGraph_eval_any a b F G f g]

@[simp] theorem outputGraph_eval_any (v : Fin 3 → M) :
    (outputGraph a b F G).val.Evalb v ↔ v 0 = output a b F G f g (v 1) (v 2) := by
  have hv : ![v 0,v 1,v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using outputGraph_eval a b F G f g (v 1) (v 0) (v 2)

theorem output_defined : 𝚺₁-Function₂ (output a b F G f g : M → M → M) via outputGraph a b F G :=
  .mk fun v => outputGraph_eval_any a b F G f g v
instance output_definable : 𝚺₁-Function₂ (output a b F G f g : M → M → M) :=
  (output_defined a b F G f g).to_definable
instance output_definable' (Γ m) : Γ-[m + 1]-Function₂ (output a b F G f g : M → M → M) :=
  (output_definable a b F G f g).of_sigmaOne

/-- This states a property of the actual numerical computation; it is not
an input to the final totality theorem. -/
def Good (formula : Bool) (word : M) : Prop :=
  run a b F G f g param word 1 =
    adjoin ⟪output a b F G f g param word,if formula then 1 else 0⟫ 0 + 1

theorem children_run (q : RawPolynomial) (n u stack : M)
    (hu : (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b) q).val.Evalb ![u])
    (hsize : ChildSize q n u)
    (hterm : ∀ word : M,len word < n → (Postfix.carrier false a b).val.Evalb ![word] →
      Good a b F G f g param false word)
    (hformula : ∀ word : M,len word < n → (Postfix.carrier true a b).val.Evalb ![word] →
      Good a b F G f g param true word) :
    run a b F G f g param (childrenWord q u) (stack + 1) =
      childStack q (mapChildren (output a b F G f g param) (output a b F G f g param) q u) stack + 1 := by
  induction q generalizing u stack with
  | term =>
      have hr := hterm u hsize hu
      have hh := run_frame a b F G f g param u 0
        (adjoin ⟪output a b F G f g param u,0⟫ 0) stack (by simpa [Good] using hr)
      simpa [childrenWord,childStack,mapChildren] using hh
  | formula =>
      have hr := hformula u hsize hu
      have hh := run_frame a b F G f g param u 0
        (adjoin ⟪output a b F G f g param u,1⟫ 0) stack (by simpa [Good] using hr)
      simpa [childrenWord,childStack,mapChildren] using hh
  | coefficient _ => simp [childrenWord,childStack]
  | unit => simp [childrenWord,childStack]
  | product c d ic id =>
      obtain ⟨x,y,rfl,hx,hy⟩ :=
        (rawCarrier_product_eval (Postfix.carrier false a b) (Postfix.carrier true a b) c d u).mp hu
      have hc : ChildSize c n x := by simpa [ChildSize] using hsize.1
      have hd : ChildSize d n y := by simpa [ChildSize] using hsize.2
      simp [childrenWord,childStack,mapChildren,run_append,ic x stack hx hc,
        id y (childStack c (mapChildren (output a b F G f g param)
          (output a b F G f g param) c x) stack) hy hd]
  | sum c d ic id =>
      rcases (rawCarrier_sum_eval (Postfix.carrier false a b) (Postfix.carrier true a b) c d u).mp hu with
        ⟨x,rfl,hx⟩ | ⟨y,rfl,hy⟩
      · have hc : ChildSize c n x := by simpa [ChildSize] using hsize
        simpa [childrenWord,childStack,mapChildren] using ic x stack hx hc
      · have hd : ChildSize d n y := by simpa [ChildSize] using hsize
        simpa [childrenWord,childStack,mapChildren] using id y stack hy hd

/-- An actual term root consumes exactly the computed child values.
The coefficient labels and sum tags are preserved by mapChildren. -/
theorem step_term_constructor (u stack : M)
    (hu : (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b) a).val.Evalb ![u]) :
    step a b f g param ⟪shape a u,0⟫
      (childStack a (mapChildren (output a b F G f g param) (output a b F G f g param) a u) stack + 1) =
      adjoin ⟪f param (mapChildren (output a b F G f g param)
        (output a b F G f g param) a u),0⟫ stack + 1 := by
  let v := mapChildren (output a b F G f g param) (output a b F G f g param) a u
  have hv : (rawCarrier numericCarrier numericCarrier a).val.Evalb ![v] :=
    rawCarrier_mapChildren a _ _ (by intro x _; simp [numericCarrier])
      (by intro x _; simp [numericCarrier]) u hu
  have hs : shape a v = shape a u := shape_mapChildren a _ _ u
  have hr := refill_shape a v stack hv
  rw [hs] at hr
  simp [step,v,hr]

theorem step_formula_constructor (u stack : M)
    (hu : (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b) b).val.Evalb ![u]) :
    step a b f g param ⟪shape b u,1⟫
      (childStack b (mapChildren (output a b F G f g param) (output a b F G f g param) b u) stack + 1) =
      adjoin ⟪g param (mapChildren (output a b F G f g param)
        (output a b F G f g param) b u),1⟫ stack + 1 := by
  let v := mapChildren (output a b F G f g param) (output a b F G f g param) b u
  have hv : (rawCarrier numericCarrier numericCarrier b).val.Evalb ![v] :=
    rawCarrier_mapChildren b _ _ (by intro x _; simp [numericCarrier])
      (by intro x _; simp [numericCarrier]) u hu
  have hs : shape b v = shape b u := shape_mapChildren b _ _ u
  have hr := refill_shape b v stack hv
  rw [hs] at hr
  simp [step,v,hr]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
private theorem sourceCarrier_definable (C : Carrier) :
    𝚺₁.DefinablePred (fun word : M => C.val.Evalb ![word]) := by
  have h : 𝚺₁.Definable (fun v : Fin 1 → M => C.val.Evalb v) :=
    HierarchySymbol.Defined.to_definable C (.mk (fun _ => Iff.rfl))
  exact h.of_iff fun v => by
    have hv : ![v 0] = v := (Matrix.fun_eq_vec_one v).symm
    change C.val.Evalb ![v 0] ↔ C.val.Evalb v
    rw [hv]

private theorem goodComparison_definable (formula : Bool) :
    𝚷₁.DefinablePred (fun n : M => ∀ word : M,len word = n →
      (Postfix.carrier formula a b).val.Evalb ![word] → Good a b F G f g param formula word) := by
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp (by definability)
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.DefinablePred.comp (sourceCarrier_definable (Postfix.carrier formula a b))
      (by definability)
  · dsimp [Good]
    definability

/-- Internal Pi-one strong induction on node count proves that the
numeric traversal succeeds on every accepted word, even at nonstandard
lengths. Only structural stack failures exist in this traversal. -/
theorem accepted_good (formula : Bool) (word : M)
    (hw : (Postfix.carrier formula a b).val.Evalb ![word]) :
    Good a b F G f g param formula word := by
  let Q (formula : Bool) (n : M) : Prop := ∀ word : M,len word = n →
    (Postfix.carrier formula a b).val.Evalb ![word] → Good a b F G f g param formula word
  have h : ∀ n : M,Q false n ∧ Q true n := by
    intro n
    induction n using ISigma1.pi1_order_induction
    · exact HierarchySymbol.Definable.and
        (goodComparison_definable a b F G f g param false)
        (goodComparison_definable a b F G f g param true)
    case ind n ih =>
      constructor
      · intro word hn hw
        obtain ⟨u,hu,he⟩ := Postfix.carrier_decomposition false a b word hw
        subst word
        have hsize : ChildSize a n u := by
          rw [← childSizeGraph_eval,← hn]
          exact children_smaller false a u
        have hc := children_run a b F G f g param a n u 0 hu hsize
          (fun w hlt hsrc => (ih (len w) hlt).1 w rfl hsrc)
          (fun w hlt hsrc => (ih (len w) hlt).2 w rfl hsrc)
        have hr : run a b F G f g param (constructor false a u) 1 =
            adjoin ⟪f param (mapChildren (output a b F G f g param)
              (output a b F G f g param) a u),0⟫ 0 + 1 := by
          rw [constructor,run_snoc]
          rw [show run a b F G f g param (childrenWord a u) 1 =
            childStack a (mapChildren (output a b F G f g param)
              (output a b F G f g param) a u) 0 + 1 by simpa using hc]
          exact step_term_constructor a b F G f g param u 0 hu
        simp [Good,output,hr]
      · intro word hn hw
        obtain ⟨u,hu,he⟩ := Postfix.carrier_decomposition true a b word hw
        subst word
        have hsize : ChildSize b n u := by
          rw [← childSizeGraph_eval,← hn]
          exact children_smaller true b u
        have hc := children_run a b F G f g param b n u 0 hu hsize
          (fun w hlt hsrc => (ih (len w) hlt).1 w rfl hsrc)
          (fun w hlt hsrc => (ih (len w) hlt).2 w rfl hsrc)
        have hr : run a b F G f g param (constructor true b u) 1 =
            adjoin ⟪g param (mapChildren (output a b F G f g param)
              (output a b F G f g param) b u),1⟫ 0 + 1 := by
          rw [constructor,run_snoc]
          rw [show run a b F G f g param (childrenWord b u) 1 =
            childStack b (mapChildren (output a b F G f g param)
              (output a b F G f g param) b u) 0 + 1 by simpa using hc]
          exact step_formula_constructor a b F G f g param u 0 hu
        simp [Good,output,hr]
  cases formula
  · exact (h (len word)).1 word rfl hw
  · exact (h (len word)).2 word rfl hw

/-- This is the PA defining equation of the actual numeric term fold. -/
theorem output_term_constructor (u : M)
    (hu : (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b) a).val.Evalb ![u]) :
    output a b F G f g param (constructor false a u) =
      f param (mapChildren (output a b F G f g param) (output a b F G f g param) a u) := by
  have hc := children_run a b F G f g param a (len (constructor false a u)) u 0 hu
    ((childSizeGraph_eval a _ u).mp (children_smaller false a u))
    (fun w _ hw => accepted_good a b F G f g param false w hw)
    (fun w _ hw => accepted_good a b F G f g param true w hw)
  have hr : run a b F G f g param (constructor false a u) 1 =
      adjoin ⟪f param (mapChildren (output a b F G f g param)
        (output a b F G f g param) a u),0⟫ 0 + 1 := by
    rw [constructor,run_snoc]
    rw [show run a b F G f g param (childrenWord a u) 1 =
      childStack a (mapChildren (output a b F G f g param)
        (output a b F G f g param) a u) 0 + 1 by simpa using hc]
    exact step_term_constructor a b F G f g param u 0 hu
  simp [output,hr]

/-- This is the PA defining equation of the actual numeric formula fold. -/
theorem output_formula_constructor (u : M)
    (hu : (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b) b).val.Evalb ![u]) :
    output a b F G f g param (constructor true b u) =
      g param (mapChildren (output a b F G f g param) (output a b F G f g param) b u) := by
  have hc := children_run a b F G f g param b (len (constructor true b u)) u 0 hu
    ((childSizeGraph_eval b _ u).mp (children_smaller true b u))
    (fun w _ hw => accepted_good a b F G f g param false w hw)
    (fun w _ hw => accepted_good a b F G f g param true w hw)
  have hr : run a b F G f g param (constructor true b u) 1 =
      adjoin ⟪g param (mapChildren (output a b F G f g param)
        (output a b F G f g param) b u),1⟫ 0 + 1 := by
    rw [constructor,run_snoc]
    rw [show run a b F G f g param (childrenWord b u) 1 =
      childStack b (mapChildren (output a b F G f g param)
        (output a b F G f g param) b u) 0 + 1 by simpa using hc]
    exact step_formula_constructor a b F G f g param u 0 hu
  simp [output,hr]

end Models
open SyntacticSyntax.NatVectors

private theorem initialValue_primrec {r : (ℕ × ℕ × ℕ) → ℕ} (hr : Primrec r) :
    Primrec (fun p : ℕ × ℕ => r (p.1,p.2,1)) :=
  hr.comp (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd (Primrec.const 1)))

private theorem extractedValue_primrec {r : (ℕ × ℕ) → ℕ} (hr : Primrec r) :
    Primrec (fun p : ℕ × ℕ => π₁ (fstIdx (Arithmetic.sub (r p) 1))) :=
  pi1_primrec.comp (fstIdx_primrec.comp (arithmetic_sub_primrec.comp hr (Primrec.const 1)))

theorem output_primrec (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
    (f g : ℕ → ℕ → ℕ) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
    (hf : Primrec₂ f) (hg : Primrec₂ g) : Primrec₂ (output a b F G f g : ℕ → ℕ → ℕ) := by
  exact Primrec.of_eq (extractedValue_primrec (initialValue_primrec
    (run_primrec a b F G f g hf hg))) (fun _ => rfl)

theorem output_natPrimrec (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
    (f g : ℕ → ℕ → ℕ) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
    (hf : Primrec₂ f) (hg : Primrec₂ g) :
    Nat.Primrec (Nat.unpaired (output a b F G f g : ℕ → ℕ → ℕ)) :=
  Primrec₂.unpaired'.mpr (output_primrec a b F G f g hf hg)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
