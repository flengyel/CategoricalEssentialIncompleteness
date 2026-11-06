/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticNamedFormulaTranslation
import Foundation.FirstOrder.LK.Simplified

/-! # Named elaboration of arithmetic eigenvariables

The free-variable map is explicit. Bound-variable names and all quantifier
names are retained separately, so LK's shift/free rewrites can be compared
syntactically before any proof-compatibility theorem is stated.
-/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedOpenTranslation
open NamedArithmeticSignature

universe u v

/-- Prepend the fresh eigenvariable name to a Nat-indexed name map. -/
def freeCons (x : ℕ) (fn : ℕ → ℕ) : ℕ → ℕ
  | 0 => x
  | n+1 => fn n

@[simp] theorem freeCons_zero (x : ℕ) (fn : ℕ → ℕ) : freeCons x fn 0 = x := rfl
@[simp] theorem freeCons_succ (x : ℕ) (fn : ℕ → ℕ) (n : ℕ) :
    freeCons x fn (n+1) = fn n := rfl

def term {ξ : Type u} {n : ℕ} (boundNames : Fin n → ℕ) (freeNames : ξ → ℕ) :
    Semiterm ℒₒᵣ ξ n → NamedArithmeticSignature.Term
  | .bvar i => .var (boundNames i)
  | .fvar x => .var (freeNames x)
  | .func .zero _ => zero
  | .func .one _ => one
  | .func .add children => add (term boundNames freeNames (children 0)) (term boundNames freeNames (children 1))
  | .func .mul children => mul (term boundNames freeNames (children 0)) (term boundNames freeNames (children 1))

def formula {ξ : Type u} : {n : ℕ} → ℕ → (Fin n → ℕ) → (ξ → ℕ) →
    Semiformula ℒₒᵣ ξ n → NamedArithmeticSignature.Formula
  | _, _, _, _, .verum => ArithmeticNamedTranslation.truth
  | _, _, _, _, .falsum => ArithmeticNamedTranslation.falsity
  | _, _, bn, fn, .rel .eq children => .equal (term bn fn (children 0)) (term bn fn (children 1))
  | _, _, bn, fn, .rel .lt children => less (term bn fn (children 0)) (term bn fn (children 1))
  | _, _, bn, fn, .nrel .eq children => .neg (.equal (term bn fn (children 0)) (term bn fn (children 1)))
  | _, _, bn, fn, .nrel .lt children => .neg (less (term bn fn (children 0)) (term bn fn (children 1)))
  | _, next, bn, fn, .and φ ψ =>
      ArithmeticNamedTranslation.conjunction (formula next bn fn φ) (formula next bn fn ψ)
  | _, next, bn, fn, .or φ ψ =>
      ArithmeticNamedTranslation.disjunction (formula next bn fn φ) (formula next bn fn ψ)
  | _, next, bn, fn, .all φ => .all next (formula (next+1) (Matrix.vecCons next bn) fn φ)
  | _, next, bn, fn, .exs φ => ArithmeticNamedTranslation.existential next
      (formula (next+1) (Matrix.vecCons next bn) fn φ)

/-- The previously fixed sentence translation is the Empty-free-variable
case of this elaboration, by syntax recursion rather than semantics. -/
theorem term_empty {n : ℕ} (bn : Fin n → ℕ) (r : ArithmeticSemiterm Empty n) :
    term bn Empty.elim r = ArithmeticNamedTranslation.translateTerm bn r := by
  induction r with
  | bvar i => rfl
  | fvar x => exact x.elim
  | func f children ih =>
      cases f with
      | zero => rfl
      | one => rfl
      | add => exact congrArg₂ NamedArithmeticSignature.add (ih 0) (ih 1)
      | mul => exact congrArg₂ NamedArithmeticSignature.mul (ih 0) (ih 1)

theorem formula_empty {n : ℕ} (φ : ArithmeticSemisentence n) :
    ∀ (next : ℕ) (bn : Fin n → ℕ),
      formula next bn Empty.elim φ = ArithmeticNamedTranslation.translateFormula next bn φ := by
  induction φ with
  | verum => intros; rfl
  | falsum => intros; rfl
  | rel r children =>
      intro next bn
      cases r <;> simp only [formula,ArithmeticNamedTranslation.translateFormula,term_empty]
  | nrel r children =>
      intro next bn
      cases r <;> simp only [formula,ArithmeticNamedTranslation.translateFormula,term_empty]
  | and φ ψ il ir =>
      intro next bn
      exact congrArg₂ ArithmeticNamedTranslation.conjunction (il next bn) (ir next bn)
  | or φ ψ il ir =>
      intro next bn
      exact congrArg₂ ArithmeticNamedTranslation.disjunction (il next bn) (ir next bn)
  | all φ ih =>
      intro next bn
      exact congrArg (NamedFiniteSyntax.Formula.all next) (ih (next+1) (Matrix.vecCons next bn))
  | exs φ ih =>
      intro next bn
      exact congrArg (ArithmeticNamedTranslation.existential next) (ih (next+1) (Matrix.vecCons next bn))

/-- A variable-valued source rewriting has its exact action on every
arithmetic term. These are local leaf equalities, not proof conclusions. -/
theorem term_rew {ξ : Type u} {ζ : Type v} {n m : ℕ}
    (ω : Rew ℒₒᵣ ξ n ζ m) (bn : Fin m → ℕ) (fn : ζ → ℕ)
    (sb : Fin n → ℕ) (sf : ξ → ℕ)
    (hb : ∀ i, term bn fn (ω (.bvar i)) = .var (sb i))
    (hf : ∀ x, term bn fn (ω (.fvar x)) = .var (sf x))
    (r : Semiterm ℒₒᵣ ξ n) : term bn fn (ω r) = term sb sf r := by
  induction r with
  | bvar i => exact hb i
  | fvar x => exact hf x
  | func f children ih =>
      rw [Rew.func]
      cases f with
      | zero => rfl
      | one => rfl
      | add => exact congrArg₂ NamedArithmeticSignature.add (ih 0) (ih 1)
      | mul => exact congrArg₂ NamedArithmeticSignature.mul (ih 0) (ih 1)

/-- Source variable renaming is kept as literal named variable renaming. -/
theorem term_map {ξ : Type u} {ζ : Type v} {n m : ℕ}
    (b : Fin n → Fin m) (f : ξ → ζ) (bn : Fin m → ℕ) (fn : ζ → ℕ)
    (r : Semiterm ℒₒᵣ ξ n) :
    term bn fn (Rew.map b f r) = term (bn ∘ b) (fn ∘ f) r :=
  term_rew (Rew.map b f) bn fn (bn ∘ b) (fn ∘ f) (by intro i; rfl) (by intro x; rfl) r

theorem term_bShift {ξ : Type u} {n : ℕ} (name : ℕ)
    (bn : Fin n → ℕ) (fn : ξ → ℕ) (r : Semiterm ℒₒᵣ ξ n) :
    term (Matrix.vecCons name bn) fn (Rew.bShift r) = term bn fn r := by
  simpa [Rew.bShift,Function.comp_def] using
    term_map Fin.succ id (Matrix.vecCons name bn) fn r

/-- LK's eigenvariable shift changes only the explicit free-name map. -/
theorem term_shift {n : ℕ} (bn : Fin n → ℕ) (fn : ℕ → ℕ)
    (r : SyntacticSemiterm ℒₒᵣ n) :
    term bn fn (Rew.shift r) = term bn (fun i => fn (i+1)) r := by
  simpa [Rew.shift,Function.comp_def] using term_map id Nat.succ bn fn r

/-- The last source bound variable is freed as eigenvariable zero;
all old free eigenvariables are shifted, exactly as Foundation defines. -/
theorem term_free {n : ℕ} (bn : Fin n → ℕ) (fn : ℕ → ℕ)
    (r : SyntacticSemiterm ℒₒᵣ (n+1)) :
    term bn fn (Rew.free r) = term (Fin.snoc bn (fn 0)) (fun i => fn (i+1)) r := by
  apply term_rew (Rew.free (L := ℒₒᵣ)) bn fn (Fin.snoc bn (fn 0)) (fun i => fn (i+1))
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Rew.free_bvar_last,term,Fin.snoc_last]
    · simp only [Rew.free_bvar_castSucc,term,Fin.snoc_castSucc]
  · intro i
    simp only [Rew.free_fvar,term]

/-- The exact variable-valued rewrite comparison extends through every
NNF constructor. Quantifiers use the actual lifted source rewriting q. -/
theorem formula_rew {ξ : Type u} {ζ : Type v} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    ∀ {m : ℕ} (ω : Rew ℒₒᵣ ξ n ζ m) (next : ℕ)
      (bn : Fin m → ℕ) (fn : ζ → ℕ) (sb : Fin n → ℕ) (sf : ξ → ℕ),
      (∀ i, term bn fn (ω (.bvar i)) = .var (sb i)) →
      (∀ x, term bn fn (ω (.fvar x)) = .var (sf x)) →
      formula next bn fn (ω ▹ φ) = formula next sb sf φ := by
  induction φ with
  | verum => intros; rfl
  | falsum => intros; rfl
  | rel r children =>
      intro m ω next bn fn sb sf hb hf
      cases r with
      | eq =>
          change NamedFiniteSyntax.Formula.equal (term bn fn (ω (children 0)))
              (term bn fn (ω (children 1))) = _
          exact congrArg₂ NamedFiniteSyntax.Formula.equal
            (term_rew ω bn fn sb sf hb hf (children 0))
            (term_rew ω bn fn sb sf hb hf (children 1))
      | lt =>
          exact congrArg₂ NamedArithmeticSignature.less
            (term_rew ω bn fn sb sf hb hf (children 0))
            (term_rew ω bn fn sb sf hb hf (children 1))
  | nrel r children =>
      intro m ω next bn fn sb sf hb hf
      cases r with
      | eq =>
          exact congrArg NamedFiniteSyntax.Formula.neg
            (congrArg₂ NamedFiniteSyntax.Formula.equal
              (term_rew ω bn fn sb sf hb hf (children 0))
              (term_rew ω bn fn sb sf hb hf (children 1)))
      | lt =>
          exact congrArg NamedFiniteSyntax.Formula.neg
            (congrArg₂ NamedArithmeticSignature.less
              (term_rew ω bn fn sb sf hb hf (children 0))
              (term_rew ω bn fn sb sf hb hf (children 1)))
  | and φ ψ il ir =>
      intro m ω next bn fn sb sf hb hf
      exact congrArg₂ ArithmeticNamedTranslation.conjunction
        (il ω next bn fn sb sf hb hf) (ir ω next bn fn sb sf hb hf)
  | or φ ψ il ir =>
      intro m ω next bn fn sb sf hb hf
      exact congrArg₂ ArithmeticNamedTranslation.disjunction
        (il ω next bn fn sb sf hb hf) (ir ω next bn fn sb sf hb hf)
  | all φ ih =>
      intro m ω next bn fn sb sf hb hf
      have hqb : ∀ i, term (Matrix.vecCons next bn) fn (ω.q (.bvar i)) =
          .var (Matrix.vecCons next sb i) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Rew.q_bvar_zero,term,Matrix.cons_val_zero]
        · simpa only [Rew.q_bvar_succ,term_bShift,Matrix.cons_val_succ] using hb j
      have hqf : ∀ x, term (Matrix.vecCons next bn) fn (ω.q (.fvar x)) = .var (sf x) := by
        intro x
        simpa only [Rew.q_fvar,term_bShift] using hf x
      exact congrArg (NamedFiniteSyntax.Formula.all next)
        (ih ω.q (next+1) (Matrix.vecCons next bn) fn (Matrix.vecCons next sb) sf hqb hqf)
  | exs φ ih =>
      intro m ω next bn fn sb sf hb hf
      have hqb : ∀ i, term (Matrix.vecCons next bn) fn (ω.q (.bvar i)) =
          .var (Matrix.vecCons next sb i) := by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Rew.q_bvar_zero,term,Matrix.cons_val_zero]
        · simpa only [Rew.q_bvar_succ,term_bShift,Matrix.cons_val_succ] using hb j
      have hqf : ∀ x, term (Matrix.vecCons next bn) fn (ω.q (.fvar x)) = .var (sf x) := by
        intro x
        simpa only [Rew.q_fvar,term_bShift] using hf x
      exact congrArg (ArithmeticNamedTranslation.existential next)
        (ih ω.q (next+1) (Matrix.vecCons next bn) fn (Matrix.vecCons next sb) sf hqb hqf)

/-- The exact eigenvariable-shift equation keeps all target binder names. -/
theorem formula_shift {n : ℕ} (φ : Semiproposition ℒₒᵣ n)
    (next : ℕ) (bn : Fin n → ℕ) (fn : ℕ → ℕ) :
    formula next bn fn (Rewriting.shift φ) = formula next bn (fun i => fn (i+1)) φ := by
  exact formula_rew φ Rew.shift next bn fn bn (fun i => fn (i+1))
    (by intro i; rfl) (by intro i; rfl)

/-- The exact eigenvariable-free equation retains the source convention
of freeing the last bound variable, including beneath nested binders. -/
theorem formula_free {n : ℕ} (φ : Semiproposition ℒₒᵣ (n+1))
    (next : ℕ) (bn : Fin n → ℕ) (fn : ℕ → ℕ) :
    formula next bn fn (Rewriting.free φ) =
      formula next (Fin.snoc bn (fn 0)) (fun i => fn (i+1)) φ := by
  apply formula_rew φ Rew.free next bn fn (Fin.snoc bn (fn 0)) (fun i => fn (i+1))
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Rew.free_bvar_last,term,Fin.snoc_last]
    · simp only [Rew.free_bvar_castSucc,term,Fin.snoc_castSucc]
  · intro i
    simp only [Rew.free_fvar,term]

/-- Closed theory axioms embed into the open LK language without
changing their fixed named translation or target word. -/
theorem formula_emb {n : ℕ} (φ : ArithmeticSemisentence n)
    (next : ℕ) (bn : Fin n → ℕ) (fn : ℕ → ℕ) :
    formula next bn fn (Rewriting.emb φ : Semiproposition ℒₒᵣ n) =
      ArithmeticNamedTranslation.translateFormula next bn φ := by
  exact (formula_rew φ Rew.emb next bn fn bn Empty.elim
    (by intro i; rfl) (by intro x; exact x.elim)).trans (formula_empty φ next bn)

/-- Every name in an elaborated arithmetic term comes from an explicit
source-variable map; this is a literal finite-list statement. -/
theorem term_names {ξ : Type u} {n : ℕ} (r : Semiterm ℒₒᵣ ξ n)
    (bn : Fin n → ℕ) (fn : ξ → ℕ) (z : ℕ)
    (hz : z ∈ (term bn fn r).freeVariables) :
    (∃ i, bn i = z) ∨ ∃ x, fn x = z := by
  induction r with
  | bvar i =>
      exact Or.inl ⟨i,(show z = bn i by simpa [term,NamedFiniteSyntax.Term.freeVariables] using hz).symm⟩
  | fvar x =>
      exact Or.inr ⟨x,(show z = fn x by simpa [term,NamedFiniteSyntax.Term.freeVariables] using hz).symm⟩
  | func f children ih =>
      cases f with
      | zero => simp [term] at hz
      | one => simp [term] at hz
      | add =>
          rcases List.mem_append.mp (by simpa only [term,add_freeVariables] using hz) with h | h
          · exact ih 0 h
          · exact ih 1 h
      | mul =>
          rcases List.mem_append.mp (by simpa only [term,mul_freeVariables] using hz) with h | h
          · exact ih 0 h
          · exact ih 1 h

theorem term_names_bound {ξ : Type u} {n : ℕ} (r : Semiterm ℒₒᵣ ξ n)
    (bn : Fin n → ℕ) (fn : ξ → ℕ) (limit : ℕ)
    (hb : ∀ i, bn i < limit) (hf : ∀ x, fn x < limit)
    (z : ℕ) (hz : z ∈ (term bn fn r).freeVariables) : z < limit := by
  rcases term_names r bn fn z hz with ⟨i,rfl⟩ | ⟨x,rfl⟩
  · exact hb i
  · exact hf x

/-- A replacement whose names are below the binder seed is independently
free for every query. Nested target binders only increase that seed. -/
theorem formula_freeFor_bounded {ξ : Type u} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    ∀ (next : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ) (x : ℕ)
      (t : NamedArithmeticSignature.Term),
      (∀ z, z ∈ t.freeVariables → z < next) →
      (formula next bn fn φ).FreeFor x t := by
  induction φ with
  | verum => intros; trivial
  | falsum => intros; trivial
  | rel r children => intros; cases r <;> trivial
  | nrel r children => intros; cases r <;> trivial
  | and φ ψ il ir =>
      intro next bn fn x t ht
      exact ⟨il next bn fn x t ht,ir next bn fn x t ht⟩
  | or φ ψ il ir =>
      intro next bn fn x t ht
      exact ⟨il next bn fn x t ht,ir next bn fn x t ht⟩
  | all φ ih =>
      intro next bn fn x t ht
      by_cases he : next = x
      · exact Or.inl he
      · have hn : next ∉ t.freeVariables := fun h => (Nat.lt_irrefl next) (ht next h)
        exact Or.inr ⟨he,Or.inr hn,ih (next+1) (Matrix.vecCons next bn) fn x t
          (fun z hz => Nat.lt_succ_of_lt (ht z hz))⟩
  | exs φ ih =>
      intro next bn fn x t ht
      by_cases he : next = x
      · exact Or.inl he
      · have hn : next ∉ t.freeVariables := fun h => (Nat.lt_irrefl next) (ht next h)
        exact Or.inr ⟨he,Or.inr hn,ih (next+1) (Matrix.vecCons next bn) fn x t
          (fun z hz => Nat.lt_succ_of_lt (ht z hz))⟩

private theorem substitute_zero (x : ℕ) (t : NamedArithmeticSignature.Term) :
    NamedArithmeticSignature.zero.substitute x t = NamedArithmeticSignature.zero := by
  change NamedFiniteSyntax.Term.app _ _ _ = NamedFiniteSyntax.Term.app _ _ _
  congr 1
  funext i
  exact i.elim0

private theorem substitute_one (x : ℕ) (t : NamedArithmeticSignature.Term) :
    NamedArithmeticSignature.one.substitute x t = NamedArithmeticSignature.one := by
  change NamedFiniteSyntax.Term.app _ _ _ = NamedFiniteSyntax.Term.app _ _ _
  congr 1
  funext i
  exact i.elim0

private theorem substitute_add (r s : NamedArithmeticSignature.Term) (x : ℕ) (t : NamedArithmeticSignature.Term) :
    (NamedArithmeticSignature.add r s).substitute x t =
      NamedArithmeticSignature.add (r.substitute x t) (s.substitute x t) := by
  change NamedFiniteSyntax.Term.app _ _ _ = NamedFiniteSyntax.Term.app _ _ _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem substitute_mul (r s : NamedArithmeticSignature.Term) (x : ℕ) (t : NamedArithmeticSignature.Term) :
    (NamedArithmeticSignature.mul r s).substitute x t =
      NamedArithmeticSignature.mul (r.substitute x t) (s.substitute x t) := by
  change NamedFiniteSyntax.Term.app _ _ _ = NamedFiniteSyntax.Term.app _ _ _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Substitution compatibility for arithmetic terms is proved from the
actual source rewriting's variable leaves, not inferred from evaluation. -/
theorem term_substitution_rew {ξ : Type u} {ζ : Type v} {n m : ℕ}
    (ω : Rew ℒₒᵣ ξ n ζ m) (bn : Fin m → ℕ) (fn : ζ → ℕ)
    (sb : Fin n → ℕ) (sf : ξ → ℕ) (x : ℕ) (t : NamedArithmeticSignature.Term)
    (hb : ∀ i, (NamedFiniteSyntax.Term.var (sb i)).substitute x t = term bn fn (ω (.bvar i)))
    (hf : ∀ y, (NamedFiniteSyntax.Term.var (sf y)).substitute x t = term bn fn (ω (.fvar y)))
    (r : Semiterm ℒₒᵣ ξ n) :
    (term sb sf r).substitute x t = term bn fn (ω r) := by
  induction r with
  | bvar i => exact hb i
  | fvar y => exact hf y
  | func f children ih =>
      rw [Rew.func]
      cases f with
      | zero => exact substitute_zero x t
      | one => exact substitute_one x t
      | add => exact (substitute_add _ _ x t).trans (congrArg₂ NamedArithmeticSignature.add (ih 0) (ih 1))
      | mul => exact (substitute_mul _ _ x t).trans (congrArg₂ NamedArithmeticSignature.mul (ih 0) (ih 1))

private theorem substitute_less (r s : NamedArithmeticSignature.Term) (x : ℕ) (t : NamedArithmeticSignature.Term) :
    (NamedArithmeticSignature.less r s).substitute x t =
      some (NamedArithmeticSignature.less (r.substitute x t) (s.substitute x t)) := by
  change some (NamedFiniteSyntax.Formula.relation _ _ _) = some (NamedFiniteSyntax.Formula.relation _ _ _)
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem substitution_q_bvar {ξ : Type u} {ζ : Type v} {n m : ℕ}
    (ω : Rew ℒₒᵣ ξ n ζ m) (bn : Fin m → ℕ) (fn : ζ → ℕ)
    (sb : Fin n → ℕ) (x next : ℕ) (t : NamedArithmeticSignature.Term) (hx : x < next)
    (hb : ∀ i, (NamedFiniteSyntax.Term.var (sb i)).substitute x t = term bn fn (ω (.bvar i))) :
    ∀ i, (NamedFiniteSyntax.Term.var (Matrix.vecCons next sb i)).substitute x t =
      term (Matrix.vecCons next bn) fn (ω.q (.bvar i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Matrix.cons_val_zero,NamedFiniteSyntax.Term.substitute,Rew.q_bvar_zero,term]
    exact ite_eq_right (Ne.symm (Nat.ne_of_lt hx))
  · simpa only [Matrix.cons_val_succ,Rew.q_bvar_succ,term_bShift] using hb j

/-- Actual named substitution commutes with an arithmetic source rewrite
when its variable leaves match. The explicit bounds ensure that every
new binder is distinct from the query and absent from the replacement. -/
theorem formula_substitution_rew {ξ : Type u} {ζ : Type v} {n : ℕ}
    (φ : Semiformula ℒₒᵣ ξ n) :
    ∀ {m : ℕ} (ω : Rew ℒₒᵣ ξ n ζ m) (next : ℕ)
      (bn : Fin m → ℕ) (fn : ζ → ℕ) (sb : Fin n → ℕ) (sf : ξ → ℕ)
      (x : ℕ) (t : NamedArithmeticSignature.Term),
      x < next → (∀ z, z ∈ t.freeVariables → z < next) →
      (∀ i, (NamedFiniteSyntax.Term.var (sb i)).substitute x t = term bn fn (ω (.bvar i))) →
      (∀ y, (NamedFiniteSyntax.Term.var (sf y)).substitute x t = term bn fn (ω (.fvar y))) →
      (formula next sb sf φ).substitute x t = some (formula next bn fn (ω ▹ φ)) := by
  induction φ with
  | verum =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      change ArithmeticNamedTranslation.truth.substitute x t = some ArithmeticNamedTranslation.truth
      simp [ArithmeticNamedTranslation.truth,NamedFiniteSyntax.Formula.substitute,substitute_zero]
  | falsum =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      change ArithmeticNamedTranslation.falsity.substitute x t = some ArithmeticNamedTranslation.falsity
      simp [ArithmeticNamedTranslation.falsity,ArithmeticNamedTranslation.truth,
        NamedFiniteSyntax.Formula.substitute,substitute_zero]
  | rel r children =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      cases r with
      | eq =>
          have h₀ := term_substitution_rew ω bn fn sb sf x t hb hf (children 0)
          have h₁ := term_substitution_rew ω bn fn sb sf x t hb hf (children 1)
          change some (NamedFiniteSyntax.Formula.equal _ _) = some (NamedFiniteSyntax.Formula.equal _ _)
          exact congrArg some (congrArg₂ NamedFiniteSyntax.Formula.equal h₀ h₁)
      | lt =>
          have h₀ := term_substitution_rew ω bn fn sb sf x t hb hf (children 0)
          have h₁ := term_substitution_rew ω bn fn sb sf x t hb hf (children 1)
          change (NamedArithmeticSignature.less (term sb sf (children 0))
            (term sb sf (children 1))).substitute x t =
              some (NamedArithmeticSignature.less (term bn fn (ω (children 0))) (term bn fn (ω (children 1))))
          exact (substitute_less _ _ x t).trans (congrArg some
            (congrArg₂ NamedArithmeticSignature.less h₀ h₁))
  | nrel r children =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      cases r with
      | eq =>
          have h₀ := term_substitution_rew ω bn fn sb sf x t hb hf (children 0)
          have h₁ := term_substitution_rew ω bn fn sb sf x t hb hf (children 1)
          exact congrArg (Option.map NamedFiniteSyntax.Formula.neg)
            (congrArg some (congrArg₂ NamedFiniteSyntax.Formula.equal h₀ h₁))
      | lt =>
          have h₀ := term_substitution_rew ω bn fn sb sf x t hb hf (children 0)
          have h₁ := term_substitution_rew ω bn fn sb sf x t hb hf (children 1)
          exact congrArg (Option.map NamedFiniteSyntax.Formula.neg)
            ((substitute_less _ _ x t).trans (congrArg some (congrArg₂ NamedArithmeticSignature.less h₀ h₁)))
  | and φ ψ il ir =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      have hl := il ω next bn fn sb sf x t hx ht hb hf
      have hr := ir ω next bn fn sb sf x t hx ht hb hf
      change (ArithmeticNamedTranslation.conjunction (formula next sb sf φ) (formula next sb sf ψ)).substitute x t =
        some (ArithmeticNamedTranslation.conjunction (formula next bn fn (ω ▹ φ)) (formula next bn fn (ω ▹ ψ)))
      simp [ArithmeticNamedTranslation.conjunction,NamedFiniteSyntax.Formula.substitute,hl,hr]
  | or φ ψ il ir =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      have hl := il ω next bn fn sb sf x t hx ht hb hf
      have hr := ir ω next bn fn sb sf x t hx ht hb hf
      change (ArithmeticNamedTranslation.disjunction (formula next sb sf φ) (formula next sb sf ψ)).substitute x t =
        some (ArithmeticNamedTranslation.disjunction (formula next bn fn (ω ▹ φ)) (formula next bn fn (ω ▹ ψ)))
      simp [ArithmeticNamedTranslation.disjunction,NamedFiniteSyntax.Formula.substitute,hl,hr]
  | all φ ih =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      have hqb := substitution_q_bvar ω bn fn sb x next t hx hb
      have hqf : ∀ y, (NamedFiniteSyntax.Term.var (sf y)).substitute x t =
          term (Matrix.vecCons next bn) fn (ω.q (.fvar y)) := by
        intro y
        simpa only [Rew.q_fvar,term_bShift] using hf y
      have hi := ih ω.q (next+1) (Matrix.vecCons next bn) fn
        (Matrix.vecCons next sb) sf x t (Nat.lt_succ_of_lt hx)
        (fun z hz => Nat.lt_succ_of_lt (ht z hz)) hqb hqf
      have hn : next ∉ t.freeVariables := fun h => (Nat.lt_irrefl next) (ht next h)
      change (NamedFiniteSyntax.Formula.all next (formula (next+1) (Matrix.vecCons next sb) sf φ)).substitute x t =
        some (.all next (formula (next+1) (Matrix.vecCons next bn) fn (ω.q ▹ φ)))
      simp [NamedFiniteSyntax.Formula.substitute,Ne.symm (Nat.ne_of_lt hx),hn,hi]
  | exs φ ih =>
      intro m ω next bn fn sb sf x t hx ht hb hf
      have hqb := substitution_q_bvar ω bn fn sb x next t hx hb
      have hqf : ∀ y, (NamedFiniteSyntax.Term.var (sf y)).substitute x t =
          term (Matrix.vecCons next bn) fn (ω.q (.fvar y)) := by
        intro y
        simpa only [Rew.q_fvar,term_bShift] using hf y
      have hi := ih ω.q (next+1) (Matrix.vecCons next bn) fn
        (Matrix.vecCons next sb) sf x t (Nat.lt_succ_of_lt hx)
        (fun z hz => Nat.lt_succ_of_lt (ht z hz)) hqb hqf
      have hn : next ∉ t.freeVariables := fun h => (Nat.lt_irrefl next) (ht next h)
      change (ArithmeticNamedTranslation.existential next (formula (next+1) (Matrix.vecCons next sb) sf φ)).substitute x t =
        some (ArithmeticNamedTranslation.existential next
          (formula (next+1) (Matrix.vecCons next bn) fn (ω.q ▹ φ)))
      simp [ArithmeticNamedTranslation.existential,NamedFiniteSyntax.Formula.substitute,
        Ne.symm (Nat.ne_of_lt hx),hn,hi]

/-- The actual substitution equation needed at an LK existential step.
All replacement names lie below the fresh outer name by an explicit map bound. -/
theorem instance_substitution (φ : Semiproposition ℒₒᵣ 1)
    (t : SyntacticTerm ℒₒᵣ) (next : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < next) :
    (formula (next+1) ![next] fn φ).substitute next (term ![] fn t) =
      some (formula (next+1) ![] fn (φ/[t])) := by
  apply formula_substitution_rew φ (Rew.subst ![t]) (next+1) ![] fn ![next] fn next (term ![] fn t)
  · exact Nat.lt_succ_self next
  · intro z hz
    exact Nat.lt_succ_of_lt (term_names_bound t ![] fn next (fun i => i.elim0) hf z hz)
  · intro i
    fin_cases i
    change (if next = next then term ![] fn t else NamedFiniteSyntax.Term.var next) = term ![] fn t
    exact ite_eq_left rfl
  · intro i
    simp only [NamedFiniteSyntax.Term.substitute,ite_eq_right (Nat.ne_of_lt (hf i)),Rew.subst_fvar,term]

/-- Free target names come from source variable maps; target quantifier
names are removed by the actual named FV filter. No freshness is assumed. -/
theorem formula_names {ξ : Type u} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    ∀ (next : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ) (z : ℕ),
      z ∈ (formula next bn fn φ).freeVariables →
        (∃ i, bn i = z) ∨ ∃ x, fn x = z := by
  induction φ with
  | verum => intro next bn fn z hz; simp [formula,ArithmeticNamedTranslation.truth,NamedFiniteSyntax.Formula.freeVariables] at hz
  | falsum => intro next bn fn z hz; simp [formula,ArithmeticNamedTranslation.falsity,ArithmeticNamedTranslation.truth,NamedFiniteSyntax.Formula.freeVariables] at hz
  | rel r children =>
      intro next bn fn z hz
      cases r with
      | eq =>
          have h : z ∈ (term bn fn (children 0)).freeVariables ∨
              z ∈ (term bn fn (children 1)).freeVariables := by
            simpa [formula,NamedFiniteSyntax.Formula.freeVariables] using hz
          exact h.elim (term_names (children 0) bn fn z) (term_names (children 1) bn fn z)
      | lt =>
          have h : z ∈ (term bn fn (children 0)).freeVariables ∨
              z ∈ (term bn fn (children 1)).freeVariables := by
            simpa [formula,NamedArithmeticSignature.less,NamedFiniteSyntax.Formula.freeVariables,List.ofFn_succ] using hz
          exact h.elim (term_names (children 0) bn fn z) (term_names (children 1) bn fn z)
  | nrel r children =>
      intro next bn fn z hz
      cases r with
      | eq =>
          have h : z ∈ (term bn fn (children 0)).freeVariables ∨
              z ∈ (term bn fn (children 1)).freeVariables := by
            simpa [formula,NamedFiniteSyntax.Formula.freeVariables] using hz
          exact h.elim (term_names (children 0) bn fn z) (term_names (children 1) bn fn z)
      | lt =>
          have h : z ∈ (term bn fn (children 0)).freeVariables ∨
              z ∈ (term bn fn (children 1)).freeVariables := by
            simpa [formula,NamedArithmeticSignature.less,NamedFiniteSyntax.Formula.freeVariables,List.ofFn_succ] using hz
          exact h.elim (term_names (children 0) bn fn z) (term_names (children 1) bn fn z)
  | and φ ψ il ir =>
      intro next bn fn z hz
      have h : z ∈ (formula next bn fn φ).freeVariables ∨
          z ∈ (formula next bn fn ψ).freeVariables := by
        simpa [formula,ArithmeticNamedTranslation.conjunction,NamedFiniteSyntax.Formula.freeVariables] using hz
      exact h.elim (il next bn fn z) (ir next bn fn z)
  | or φ ψ il ir =>
      intro next bn fn z hz
      have h : z ∈ (formula next bn fn φ).freeVariables ∨
          z ∈ (formula next bn fn ψ).freeVariables := by
        simpa [formula,ArithmeticNamedTranslation.disjunction,NamedFiniteSyntax.Formula.freeVariables] using hz
      exact h.elim (il next bn fn z) (ir next bn fn z)
  | all φ ih =>
      intro next bn fn z hz
      have h : z ∈ (formula (next+1) (Matrix.vecCons next bn) fn φ).freeVariables ∧ z ≠ next := by
        simpa [formula,NamedFiniteSyntax.Formula.freeVariables] using hz
      rcases ih (next+1) (Matrix.vecCons next bn) fn z h.1 with ⟨i,hi⟩ | hf
      · revert hi
        refine Fin.cases ?_ (fun j => ?_) i
        · intro hi
          exact False.elim (h.2 (by simpa only [Matrix.cons_val_zero] using hi.symm))
        · intro hi
          exact Or.inl ⟨j,by simpa only [Matrix.cons_val_succ] using hi⟩
      · exact Or.inr hf
  | exs φ ih =>
      intro next bn fn z hz
      have h : z ∈ (formula (next+1) (Matrix.vecCons next bn) fn φ).freeVariables ∧ z ≠ next := by
        simpa [formula,ArithmeticNamedTranslation.existential,NamedFiniteSyntax.Formula.freeVariables] using hz
      rcases ih (next+1) (Matrix.vecCons next bn) fn z h.1 with ⟨i,hi⟩ | hf
      · revert hi
        refine Fin.cases ?_ (fun j => ?_) i
        · intro hi
          exact False.elim (h.2 (by simpa only [Matrix.cons_val_zero] using hi.symm))
        · intro hi
          exact Or.inl ⟨j,by simpa only [Matrix.cons_val_succ] using hi⟩
      · exact Or.inr hf

theorem formula_names_bound {ξ : Type u} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n)
    (next : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ) (limit : ℕ)
    (hb : ∀ i, bn i < limit) (hf : ∀ x, fn x < limit)
    (z : ℕ) (hz : z ∈ (formula next bn fn φ).freeVariables) : z < limit := by
  rcases formula_names φ next bn fn z hz with ⟨i,rfl⟩ | ⟨x,rfl⟩
  · exact hb i
  · exact hf x

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedOpenTranslation
