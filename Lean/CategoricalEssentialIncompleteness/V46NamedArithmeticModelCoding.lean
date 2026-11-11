/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticStandardCodes

/-! Finite named constructor charts in an arbitrary PA model. These are
external finite tuples of model values, without replacing the internal
postfix word carrier by an externally finite syntax type. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticModelCoding
open NamedPostfixEncoding NamedArithmeticStandardCodes ConcreteNamedSubstitution
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedArithmeticModelCodingDecidableEq : DecidableEq M := Classical.decEq M

def childTuple : (n : ℕ) → (Fin n → M) → M
  | 0, _ => 0
  | 1, f => f 0
  | n + 2, f => ⟪childTuple (n + 1) (fun i => f i.castSucc),f (Fin.last (n + 1))⟫

def arityInput : (d : ℕ) → Fin (d + 1) → M → M
  | 0, _, value => value
  | d + 1, k, value => Fin.lastCases ⟪value,1⟫
      (fun j => ⟪arityInput d j value,0⟫) k

def equalInput (s t : M) : M := ⟪⟪⟪⟪⟪s,t⟫,0⟫,0⟫,0⟫,0⟫
def relationInput (d : ℕ) (k : Fin (d+1)) (s : M) (c : Fin k.val → M) : M :=
  ⟪⟪⟪⟪arityInput d k ⟪s,childTuple k.val c⟫,1⟫,0⟫,0⟫,0⟫
def negInput (s : M) : M := ⟪⟪⟪s,1⟫,0⟫,0⟫
def impInput (s t : M) : M := ⟪⟪⟪s,t⟫,1⟫,0⟫
def allInput (x s : M) : M := ⟪⟪x,s⟫,1⟫

theorem childTuple_natCast (n : ℕ) (f : Fin n → ℕ) :
    ((NamedPostfixEncoding.childTuple n f : ℕ) : M) = childTuple n (fun i => (f i : M)) := by
  induction n with
  | zero => simp [NamedPostfixEncoding.childTuple,childTuple]
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      rw [NamedPostfixEncoding.childTuple,childTuple,pair_natCast,ih]

theorem arityInput_natCast (d : ℕ) (k : Fin (d+1)) (value : ℕ) :
    ((NamedPostfixEncoding.arityInput d k value : ℕ) : M) = arityInput d k (value : M) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [NamedPostfixEncoding.arityInput,arityInput,Fin.lastCases_last]
      rw [pair_natCast]
      simp only [Nat.cast_one]
    · simp only [NamedPostfixEncoding.arityInput,arityInput,Fin.lastCases_castSucc]
      rw [pair_natCast,ih]
      simp only [Nat.cast_zero]

theorem childTuple_member (X Y : Carrier) (n : ℕ) (f : Fin n → M)
    (h : ∀ i,X.val.Evalb ![f i]) :
    (rawCarrier X Y (SyntaxPolynomial.power .term n)).val.Evalb ![childTuple n f] := by
  induction n with
  | zero => simp [SyntaxPolynomial.power,childTuple,rawCarrier]
  | succ n ih =>
    cases n with
    | zero => simpa [SyntaxPolynomial.power,childTuple,rawCarrier] using h 0
    | succ n =>
      rw [SyntaxPolynomial.power,childTuple,rawCarrier_product_eval]
      exact ⟨_,_,rfl,ih (fun i => f i.castSucc) (fun i => h i.castSucc),h (Fin.last (n+1))⟩

theorem arityInput_member (X Y : Carrier) (σ : ℕ → Carrier) (d : ℕ)
    (k : Fin (d+1)) (value : M)
    (h : (rawCarrier X Y (.product (.coefficient (σ k.val))
      (SyntaxPolynomial.power .term k.val))).val.Evalb ![value]) :
    (rawCarrier X Y (SyntaxPolynomial.constructors σ d)).val.Evalb ![arityInput d k value] := by
  induction d with
  | zero =>
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact h
  | succ d ih =>
    refine Fin.lastCases ?_ (fun j => ?_) k h
    · intro hl
      rw [arityInput,Fin.lastCases_last,SyntaxPolynomial.constructors,rawCarrier_sum_eval]
      exact Or.inr ⟨value,rfl,hl⟩
    · intro hl
      rw [arityInput,Fin.lastCases_castSucc,SyntaxPolynomial.constructors,rawCarrier_sum_eval]
      exact Or.inl ⟨arityInput d j value,rfl,ih j hl⟩

@[simp] theorem mapChildren_childTuple (f g : M → M) (n : ℕ) (c : Fin n → M) :
    mapChildren f g (SyntaxPolynomial.power .term n) (childTuple n c) =
      childTuple n (fun i => f (c i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [SyntaxPolynomial.power,childTuple,mapChildren,ih]

@[simp] theorem mapChildren_arityInput (σ : ℕ → Carrier) (f g : M → M)
    (d : ℕ) (k : Fin (d+1)) (s : M) (c : Fin k.val → M) :
    mapChildren f g (SyntaxPolynomial.constructors σ d)
      (arityInput d k ⟪s,childTuple k.val c⟫) =
      arityInput d k ⟪s,childTuple k.val (fun i => f (c i))⟫ := by
  induction d with
  | zero =>
    have hk : k = 0 := Fin.eq_zero k
    subst k
    simp [SyntaxPolynomial.constructors,arityInput,mapChildren]
  | succ d ih =>
    revert c
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro c
      simp [SyntaxPolynomial.constructors,arityInput,Fin.lastCases_last,mapChildren]
    · intro c
      simp [SyntaxPolynomial.constructors,arityInput,Fin.lastCases_castSucc,mapChildren,ih]

/-- Append in the same left-associated finite-power order. -/
def gatherTuple : (n : ℕ) → (Fin n → M) → M
  | 0, _ => 0
  | 1, f => f 0
  | n+2, f => Words.append (gatherTuple (n+1) (fun i => f i.castSucc))
      (f (Fin.last (n+1)))

@[simp] theorem gather_childTuple (n : ℕ) (c : Fin n → M) :
    gather (SyntaxPolynomial.power .term n) (childTuple n c) = gatherTuple n c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simp [SyntaxPolynomial.power,childTuple,gather,gatherTuple,ih]

@[simp] theorem gather_arityInput (σ : ℕ → Carrier) (d : ℕ)
    (k : Fin (d+1)) (s : M) (c : Fin k.val → M) :
    gather (SyntaxPolynomial.constructors σ d) (arityInput d k ⟪s,childTuple k.val c⟫) =
      gatherTuple k.val c := by
  induction d with
  | zero =>
    have hk : k = 0 := Fin.eq_zero k
    subst k
    simp [SyntaxPolynomial.constructors,arityInput,gather]
  | succ d ih =>
    revert c
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro c
      simp [SyntaxPolynomial.constructors,arityInput,Fin.lastCases_last,gather]
    · intro c
      simp [SyntaxPolynomial.constructors,arityInput,Fin.lastCases_castSucc,gather,ih]

private theorem member_append_one (name s t : M) :
    member name (Words.append s t) = 1 ↔ member name s = 1 ∨ member name t = 1 := by
  rw [member_append]
  by_cases h : member name s = 1 <;> simp [h]

theorem member_gatherTuple (name : M) (n : ℕ) (c : Fin n → M) :
    member name (gatherTuple n c) = 1 ↔ ∃ i,member name (c i) = 1 := by
  induction n with
  | zero => simp [gatherTuple]
  | succ n ih =>
    cases n with
    | zero => simp [gatherTuple]
    | succ n =>
      rw [gatherTuple,member_append_one,ih]
      constructor
      · rintro (⟨i,hi⟩ | hl)
        · exact ⟨i.castSucc,hi⟩
        · exact ⟨Fin.last (n+1),hl⟩
      · rintro ⟨i,hi⟩
        refine Fin.lastCases ?_ (fun j => ?_) i hi
        · exact Or.inr
        · intro hj
          exact Or.inl ⟨j,hj⟩

variable {σ π : ℕ → Carrier} {d : ℕ}
def termWord : NamedFiniteSyntax.Term (Symbols σ) d → M
  | .var x => constructor false (termPolynomial σ d) ⟪(x : M),0⟫
  | .app k s children => constructor false (termPolynomial σ d)
      ⟪arityInput d k ⟪(s.val : M),childTuple k.val (fun i => termWord (children i))⟫,1⟫

def formulaWord : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d → M
  | .equal s t => constructor true (formulaPolynomial π d) (equalInput (termWord s) (termWord t))
  | .relation k s children => constructor true (formulaPolynomial π d)
      (relationInput d k (s.val : M) (fun i => termWord (children i)))
  | .neg body => constructor true (formulaPolynomial π d) (negInput (formulaWord body))
  | .imp left right => constructor true (formulaPolynomial π d) (impInput (formulaWord left) (formulaWord right))
  | .all x body => constructor true (formulaPolynomial π d) (allInput (x : M) (formulaWord body))

theorem termWord_natCast (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    (termCode s : M) = termWord s := by
  induction s with
  | var x =>
    change ((constructor false (termPolynomial σ d) (Arithmetic.pair x 0) : ℕ) : M) = _
    rw [constructor_natCast,pair_natCast]
    simp only [Nat.cast_zero]
    rfl
  | app k s children ih =>
    change ((constructor false (termPolynomial σ d) (Arithmetic.pair
      (NamedPostfixEncoding.arityInput d k (Arithmetic.pair s.val
        (NamedPostfixEncoding.childTuple k.val (fun i => termCode (children i))))) 1) : ℕ) : M) = _
    rw [constructor_natCast,pair_natCast,arityInput_natCast,pair_natCast,childTuple_natCast]
    simp only [Nat.cast_one]
    rw [funext ih]
    rfl

theorem formulaWord_natCast (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (formulaCode φ : M) = formulaWord φ := by
  induction φ with
  | equal s t =>
    simp only [formulaCode,formulaWord,NamedPostfixEncoding.equalInput,equalInput,
      constructor_natCast,pair_natCast,Nat.cast_zero,termWord_natCast]
  | relation k s children =>
    simp only [formulaCode,formulaWord,NamedPostfixEncoding.relationInput,relationInput,
      constructor_natCast,pair_natCast,Nat.cast_zero,Nat.cast_one,arityInput_natCast,
      childTuple_natCast,termWord_natCast]
  | neg body ih =>
    simp only [formulaCode,formulaWord,NamedPostfixEncoding.negInput,negInput,
      constructor_natCast,pair_natCast,Nat.cast_zero,Nat.cast_one,ih]
  | imp left right il ir =>
    simp only [formulaCode,formulaWord,NamedPostfixEncoding.impInput,impInput,
      constructor_natCast,pair_natCast,Nat.cast_zero,Nat.cast_one,il,ir]
  | all x body ih =>
    simp only [formulaCode,formulaWord,NamedPostfixEncoding.allInput,allInput,
      constructor_natCast,pair_natCast,Nat.cast_one,ih]

theorem termWord_member (π : ℕ → Carrier) (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![(termWord s : M)] := by
  rw [← termWord_natCast (M := M)]
  exact carrier_natCast _ _ (termCode_member π s)

theorem formulaWord_member (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![(formulaWord φ : M)] := by
  rw [← formulaWord_natCast (M := M)]
  exact carrier_natCast _ _ (formulaCode_member φ)

def termInput : NamedFiniteSyntax.Term (Symbols σ) d → M
  | .var x => ⟪(x : M),0⟫
  | .app k s children => ⟪arityInput d k
      ⟪(s.val : M),childTuple k.val (fun i => termWord (children i))⟫,1⟫

def formulaInput : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d → M
  | .equal s t => equalInput (termWord s) (termWord t)
  | .relation k s children => relationInput d k (s.val : M) (fun i => termWord (children i))
  | .neg body => negInput (formulaWord body)
  | .imp left right => impInput (formulaWord left) (formulaWord right)
  | .all x body => allInput (x : M) (formulaWord body)

 theorem termWord_root (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    (termWord s : M) = constructor false (termPolynomial σ d) (termInput s) := by
  cases s <;> rfl

 theorem formulaWord_root (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (formulaWord φ : M) = constructor true (formulaPolynomial π d) (formulaInput φ) := by
  cases φ <;> rfl

 theorem termInput_natCast (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    (NamedPostfixEncoding.termInput s : M) = termInput s := by
  cases s with
  | var x =>
    simp only [NamedPostfixEncoding.termInput,termInput,pair_natCast,Nat.cast_zero]
  | app k s children =>
    simp only [NamedPostfixEncoding.termInput,termInput,pair_natCast,arityInput_natCast,
      childTuple_natCast,termWord_natCast,Nat.cast_one]

 theorem formulaInput_natCast (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (NamedPostfixEncoding.formulaInput φ : M) = formulaInput φ := by
  cases φ with
  | equal s t =>
    simp only [NamedPostfixEncoding.formulaInput,formulaInput,NamedPostfixEncoding.equalInput,equalInput,
      pair_natCast,termWord_natCast,Nat.cast_zero]
  | relation k s children =>
    simp only [NamedPostfixEncoding.formulaInput,formulaInput,NamedPostfixEncoding.relationInput,relationInput,
      pair_natCast,termWord_natCast,arityInput_natCast,childTuple_natCast,Nat.cast_zero,Nat.cast_one]
  | neg body =>
    simp only [NamedPostfixEncoding.formulaInput,formulaInput,NamedPostfixEncoding.negInput,negInput,
      pair_natCast,formulaWord_natCast,Nat.cast_zero,Nat.cast_one]
  | imp left right =>
    simp only [NamedPostfixEncoding.formulaInput,formulaInput,NamedPostfixEncoding.impInput,impInput,
      pair_natCast,formulaWord_natCast,Nat.cast_zero,Nat.cast_one]
  | all x body =>
    simp only [NamedPostfixEncoding.formulaInput,formulaInput,NamedPostfixEncoding.allInput,allInput,
      pair_natCast,formulaWord_natCast,Nat.cast_one]

 theorem termInput_member (π : ℕ → Carrier) (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    (rawCarrier (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d))
      (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d))
      (termPolynomial σ d)).val.Evalb ![(termInput s : M)] := by
  rw [← termInput_natCast (M := M)]
  exact carrier_natCast _ _ (NamedPostfixEncoding.termInput_member π s)

 theorem formulaInput_member (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (rawCarrier (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d))
      (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d))
      (formulaPolynomial π d)).val.Evalb ![(formulaInput φ : M)] := by
  rw [← formulaInput_natCast (M := M)]
  exact carrier_natCast _ _ (NamedPostfixEncoding.formulaInput_member φ)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticModelCoding
