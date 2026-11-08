import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser
import CategoricalEssentialIncompleteness.V46MillerStrictRationalCuts

/-! # Literal ordered-field syntax and the actual uniformly enumerable cut axioms

The arity bound is two. Nullary labels are zero, one and the named c_n;
the other labels are unary minus, binary addition/multiplication and strict
order. Rational inequalities are integer-coefficient inequalities in this
language. No real-closed-field axiom set is defined or assumed here.
-/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSyntax
open NamedPostfixEncoding SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors

abbrev bound : ℕ := 2
abbrev variableSymbols : Carrier := NamedPostfixEncoding.variableCarrier

def functionSymbols (arity : ℕ) : Carrier :=
  if arity=0 then .mkSigma “c. 0 = 0”
  else if arity=1 then .mkSigma “c. c = 0”
  else if arity=2 then .mkSigma “c. c = 0 ∨ c = 1”
  else .mkSigma “c. 0 = 1”

def relationSymbols (arity : ℕ) : Carrier :=
  if arity=2 then .mkSigma “c. c = 0” else .mkSigma “c. 0 = 1”

abbrev σ := functionSymbols
abbrev π := relationSymbols
abbrev FunctionSymbols := NamedPostfixEncoding.Symbols functionSymbols
abbrev RelationSymbols := NamedPostfixEncoding.Symbols relationSymbols
abbrev Term := NamedFiniteSyntax.Term FunctionSymbols bound
abbrev Formula := NamedFiniteSyntax.Formula FunctionSymbols RelationSymbols bound

@[simp] theorem functionSymbols_zero (c : ℕ) : (functionSymbols 0).val.Evalb ![c] := by
  simp [functionSymbols]
@[simp] theorem functionSymbols_one (c : ℕ) :
    (functionSymbols 1).val.Evalb ![c] ↔ c=0 := by simp [functionSymbols]
@[simp] theorem functionSymbols_two (c : ℕ) :
    (functionSymbols 2).val.Evalb ![c] ↔ c=0 ∨ c=1 := by simp [functionSymbols]
@[simp] theorem relationSymbols_two (c : ℕ) :
    (relationSymbols 2).val.Evalb ![c] ↔ c=0 := by simp [relationSymbols]

theorem functionSymbols_iff (arity c : ℕ) : (functionSymbols arity).val.Evalb ![c] ↔
    arity=0 ∨ (arity=1 ∧ c=0) ∨ (arity=2 ∧ (c=0 ∨ c=1)) := by
  by_cases h0 : arity=0 <;> by_cases h1 : arity=1 <;> by_cases h2 : arity=2 <;>
    simp [functionSymbols,h0,h1,h2]

theorem relationSymbols_iff (arity c : ℕ) : (relationSymbols arity).val.Evalb ![c] ↔
    arity=2 ∧ c=0 := by
  by_cases h2 : arity=2 <;> simp [relationSymbols,h2]

theorem functionSymbols_primrec : PrimrecPred
    (fun x : ℕ × ℕ => (functionSymbols x.1).val.Evalb ![x.2]) := by
  have h0 := Primrec.eq.comp (Primrec.fst (α := ℕ) (β := ℕ)) (Primrec.const 0)
  have h1 := Primrec.eq.comp (Primrec.fst (α := ℕ) (β := ℕ)) (Primrec.const 1)
  have h2 := Primrec.eq.comp (Primrec.fst (α := ℕ) (β := ℕ)) (Primrec.const 2)
  have c0 := Primrec.eq.comp (Primrec.snd (α := ℕ) (β := ℕ)) (Primrec.const 0)
  have c1 := Primrec.eq.comp (Primrec.snd (α := ℕ) (β := ℕ)) (Primrec.const 1)
  exact (h0.or ((h1.and c0).or (h2.and (c0.or c1)))).of_eq
    (fun x => (functionSymbols_iff x.1 x.2).symm)

theorem relationSymbols_primrec : PrimrecPred
    (fun x : ℕ × ℕ => (relationSymbols x.1).val.Evalb ![x.2]) :=
  ((Primrec.eq.comp Primrec.fst (Primrec.const 2)).and
    (Primrec.eq.comp Primrec.snd (Primrec.const 0))).of_eq
      (fun x => (relationSymbols_iff x.1 x.2).symm)

def zeroSymbol : FunctionSymbols 0 := ⟨0,by simp⟩
def oneSymbol : FunctionSymbols 0 := ⟨1,by simp⟩
def constantSymbol (n : ℕ) : FunctionSymbols 0 := ⟨n+2,by simp⟩
def negSymbol : FunctionSymbols 1 := ⟨0,by simp⟩
def addSymbol : FunctionSymbols 2 := ⟨0,by simp⟩
def mulSymbol : FunctionSymbols 2 := ⟨1,by simp⟩
def ltSymbol : RelationSymbols 2 := ⟨0,by simp⟩

def var (name : ℕ) : Term := .var name
def zero : Term := .app ⟨0,by decide⟩ zeroSymbol Fin.elim0
def one : Term := .app ⟨0,by decide⟩ oneSymbol Fin.elim0
def c (n : ℕ) : Term := .app ⟨0,by decide⟩ (constantSymbol n) Fin.elim0
def neg (t : Term) : Term := .app ⟨1,by decide⟩ negSymbol ![t]
def add (s t : Term) : Term := .app ⟨2,by decide⟩ addSymbol ![s,t]
def mul (s t : Term) : Term := .app ⟨2,by decide⟩ mulSymbol ![s,t]
def lt (s t : Term) : Formula := .relation ⟨2,by decide⟩ ltSymbol ![s,t]
def all (name : ℕ) (φ : Formula) : Formula := .all name φ
def imp (φ ψ : Formula) : Formula := .imp φ ψ
def negation (φ : Formula) : Formula := .neg φ

@[simp] theorem zero_freeVariables : zero.freeVariables=[] := by
  simp [zero,NamedFiniteSyntax.Term.freeVariables]
@[simp] theorem one_freeVariables : one.freeVariables=[] := by
  simp [one,NamedFiniteSyntax.Term.freeVariables]
@[simp] theorem c_freeVariables (n : ℕ) : (c n).freeVariables=[] := by
  simp [c,NamedFiniteSyntax.Term.freeVariables]
@[simp] theorem neg_freeVariables (t : Term) : (neg t).freeVariables=t.freeVariables := by
  simp [neg,NamedFiniteSyntax.Term.freeVariables,List.ofFn_succ]
@[simp] theorem add_freeVariables (s t : Term) :
    (add s t).freeVariables=s.freeVariables++t.freeVariables := by
  simp [add,NamedFiniteSyntax.Term.freeVariables,List.ofFn_succ]
@[simp] theorem mul_freeVariables (s t : Term) :
    (mul s t).freeVariables=s.freeVariables++t.freeVariables := by
  simp [mul,NamedFiniteSyntax.Term.freeVariables,List.ofFn_succ]
@[simp] theorem lt_freeVariables (s t : Term) :
    (lt s t).freeVariables=s.freeVariables++t.freeVariables := by
  simp [lt,NamedFiniteSyntax.Formula.freeVariables,List.ofFn_succ]

def positiveNatural : ℕ → Term
  | 0 => one
  | n+1 => add (positiveNatural n) one

def natural (n : ℕ) : Term := if n=0 then zero else positiveNatural (n-1)

def integerTerm (signedCode : ℕ) : Term :=
  if signedCode%2=0 then natural (signedCode/2) else neg (natural (signedCode/2+1))

@[simp] theorem natural_zero : natural 0=zero := rfl
@[simp] theorem natural_one : natural 1=one := rfl
@[simp] theorem natural_two : natural 2=add one one := rfl
@[simp] theorem positiveNatural_freeVariables (n : ℕ) : (positiveNatural n).freeVariables=[] := by
  induction n with
  | zero => exact one_freeVariables
  | succ n ih => simp [positiveNatural,ih]
@[simp] theorem natural_freeVariables (n : ℕ) : (natural n).freeVariables=[] := by
  by_cases h : n=0 <;> simp [natural,h]
@[simp] theorem integerTerm_freeVariables (s : ℕ) : (integerTerm s).freeVariables=[] := by
  by_cases h : s%2=0 <;> simp [integerTerm,h]

abbrev termPolynomial := NamedPostfixEncoding.termPolynomial functionSymbols bound
abbrev formulaPolynomial := NamedPostfixEncoding.formulaPolynomial relationSymbols bound
abbrev termCode : Term → ℕ := NamedPostfixEncoding.termCode
abbrev formulaCode : Formula → ℕ := NamedPostfixEncoding.formulaCode

def varWord (name : ℕ) : ℕ := constructor false termPolynomial (Arithmetic.pair name 0)
def nullaryWord (symbol : ℕ) : ℕ := constructor false termPolynomial
  (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair symbol 0) 0) 0) 1)
def unaryWord (symbol child : ℕ) : ℕ := constructor false termPolynomial
  (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair symbol child) 1) 0) 1)
def binaryWord (symbol left right : ℕ) : ℕ := constructor false termPolynomial
  (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair symbol (Arithmetic.pair left right)) 1) 1)
def ltWord (left right : ℕ) : ℕ := constructor true formulaPolynomial
  (NamedPostfixEncoding.relationInput bound ⟨2,by decide⟩ 0 ![left,right])
def negationWord (word : ℕ) : ℕ := constructor true formulaPolynomial (negInput word)
def allWord (name word : ℕ) : ℕ := constructor true formulaPolynomial (allInput name word)
def impWord (left right : ℕ) : ℕ := constructor true formulaPolynomial (impInput left right)
def equalWord (left right : ℕ) : ℕ := constructor true formulaPolynomial (equalInput left right)

@[simp] theorem termCode_var (name : ℕ) : termCode (var name)=varWord name := rfl
@[simp] theorem termCode_zero : termCode zero=nullaryWord 0 := rfl
@[simp] theorem termCode_one : termCode one=nullaryWord 1 := rfl
@[simp] theorem termCode_c (n : ℕ) : termCode (c n)=nullaryWord (n+2) := rfl
@[simp] theorem termCode_neg (t : Term) : termCode (neg t)=unaryWord 0 (termCode t) := rfl
@[simp] theorem termCode_add (s t : Term) : termCode (add s t)=binaryWord 0 (termCode s) (termCode t) := rfl
@[simp] theorem termCode_mul (s t : Term) : termCode (mul s t)=binaryWord 1 (termCode s) (termCode t) := rfl
@[simp] theorem formulaCode_lt (s t : Term) : formulaCode (lt s t)=ltWord (termCode s) (termCode t) := rfl
@[simp] theorem formulaCode_negation (φ : Formula) : formulaCode (negation φ)=negationWord (formulaCode φ) := rfl
@[simp] theorem formulaCode_all (name : ℕ) (φ : Formula) : formulaCode (all name φ)=allWord name (formulaCode φ) := rfl
@[simp] theorem formulaCode_imp (φ ψ : Formula) : formulaCode (imp φ ψ)=impWord (formulaCode φ) (formulaCode ψ) := rfl
@[simp] theorem formulaCode_equal (s t : Term) :
    formulaCode (.equal s t)=equalWord (termCode s) (termCode t) := rfl

theorem varWord_primrec : Primrec varWord :=
  (constructor_primrec false termPolynomial).comp (pair_primrec.comp Primrec.id (Primrec.const 0))

theorem nullaryWord_primrec : Primrec nullaryWord :=
  (constructor_primrec false termPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp
      (pair_primrec.comp Primrec.id (Primrec.const 0)) (Primrec.const 0))
      (Primrec.const 0)) (Primrec.const 1))

theorem unaryWord_primrec (symbol : ℕ) : Primrec (unaryWord symbol) :=
  (constructor_primrec false termPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp
      (pair_primrec.comp (Primrec.const symbol) Primrec.id) (Primrec.const 1))
      (Primrec.const 0)) (Primrec.const 1))

theorem binaryWord_primrec (symbol : ℕ) : Primrec₂ (binaryWord symbol) :=
  (constructor_primrec false termPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp
      (Primrec.const symbol) (pair_primrec.comp Primrec.fst Primrec.snd))
      (Primrec.const 1)) (Primrec.const 1))

theorem ltWord_primrec : Primrec₂ ltWord := by
  change Primrec₂ (fun left right : ℕ => constructor true formulaPolynomial
    (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
      (Arithmetic.pair (Arithmetic.pair 0 (Arithmetic.pair left right)) 1) 1) 0) 0) 0))
  exact (constructor_primrec true formulaPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp
      (pair_primrec.comp (pair_primrec.comp (Primrec.const 0)
        (pair_primrec.comp Primrec.fst Primrec.snd)) (Primrec.const 1))
      (Primrec.const 1)) (Primrec.const 0)) (Primrec.const 0)) (Primrec.const 0))

theorem negationWord_primrec : Primrec negationWord :=
  (constructor_primrec true formulaPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp Primrec.id (Primrec.const 1))
      (Primrec.const 0)) (Primrec.const 0))

theorem allWord_primrec : Primrec₂ allWord :=
  (constructor_primrec true formulaPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp Primrec.fst Primrec.snd) (Primrec.const 1))

theorem impWord_primrec : Primrec₂ impWord :=
  (constructor_primrec true formulaPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp Primrec.fst Primrec.snd)
      (Primrec.const 1)) (Primrec.const 0))

theorem equalWord_primrec : Primrec₂ equalWord :=
  (constructor_primrec true formulaPolynomial).comp
    (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp (pair_primrec.comp
      (pair_primrec.comp Primrec.fst Primrec.snd) (Primrec.const 0))
      (Primrec.const 0)) (Primrec.const 0)) (Primrec.const 0))

def positiveWord : ℕ → ℕ
  | 0 => nullaryWord 1
  | n+1 => binaryWord 0 (positiveWord n) (nullaryWord 1)
def naturalWord (n : ℕ) : ℕ := if n=0 then nullaryWord 0 else positiveWord (n-1)
def integerWord (n : ℕ) : ℕ :=
  if n%2=0 then naturalWord (n/2) else unaryWord 0 (naturalWord (n/2+1))

@[simp] theorem termCode_positiveNatural (n : ℕ) : termCode (positiveNatural n)=positiveWord n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [positiveNatural,termCode_add,termCode_one,positiveWord,ih]
@[simp] theorem termCode_natural (n : ℕ) : termCode (natural n)=naturalWord n := by
  by_cases h : n=0 <;> simp [natural,naturalWord,h]
@[simp] theorem termCode_integerTerm (n : ℕ) : termCode (integerTerm n)=integerWord n := by
  by_cases h : n%2=0 <;> simp [integerTerm,integerWord,h]

theorem positiveWord_primrec : Primrec positiveWord := by
  apply (Primrec.nat_rec₁ (nullaryWord 1)
    ((binaryWord_primrec 0).comp Primrec.snd (Primrec.const (nullaryWord 1))).to₂).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun w => binaryWord 0 w (nullaryWord 1)) ih

theorem naturalWord_primrec : Primrec naturalWord :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const (nullaryWord 0))
    (positiveWord_primrec.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem integerWord_primrec : Primrec integerWord :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
    (naturalWord_primrec.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)))
    ((unaryWord_primrec 0).comp (naturalWord_primrec.comp
      (Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.id (Primrec.const 2)) (Primrec.const 1))))

/-- `q_j<c_n`, cleared through the positive denominator of the fixed index. -/
def belowSentence (n j : ℕ) : Formula :=
  lt (integerTerm (Nat.unpair j).1) (mul (natural ((Nat.unpair j).2+1)) (c n))

/-- `c_n<q_j`, with exactly the same positive-denominator convention. -/
def aboveSentence (n j : ℕ) : Formula :=
  lt (mul (natural ((Nat.unpair j).2+1)) (c n)) (integerTerm (Nat.unpair j).1)

def belowWord (n j : ℕ) : ℕ := ltWord (integerWord (Nat.unpair j).1)
  (binaryWord 1 (naturalWord ((Nat.unpair j).2+1)) (nullaryWord (n+2)))
def aboveWord (n j : ℕ) : ℕ := ltWord
  (binaryWord 1 (naturalWord ((Nat.unpair j).2+1)) (nullaryWord (n+2)))
    (integerWord (Nat.unpair j).1)

@[simp] theorem formulaCode_belowSentence (n j : ℕ) : formulaCode (belowSentence n j)=belowWord n j := by
  simp only [belowSentence,belowWord,formulaCode_lt,termCode_integerTerm,termCode_mul,termCode_natural,termCode_c]
@[simp] theorem formulaCode_aboveSentence (n j : ℕ) : formulaCode (aboveSentence n j)=aboveWord n j := by
  simp only [aboveSentence,aboveWord,formulaCode_lt,termCode_integerTerm,termCode_mul,termCode_natural,termCode_c]
@[simp] theorem belowSentence_closed (n j : ℕ) : (belowSentence n j).freeVariables=[] := by
  simp [belowSentence]
@[simp] theorem aboveSentence_closed (n j : ℕ) : (aboveSentence n j).freeVariables=[] := by
  simp [aboveSentence]

theorem belowWord_primrec : Primrec₂ belowWord := by
  have hj := Primrec.unpair.comp (Primrec.snd (α := ℕ) (β := ℕ))
  have hi := integerWord_primrec.comp (Primrec.fst.comp hj)
  have hd := naturalWord_primrec.comp (Primrec.nat_add.comp (Primrec.snd.comp hj) (Primrec.const 1))
  have hc : Primrec (fun x : ℕ × ℕ => nullaryWord (x.1+2)) :=
    nullaryWord_primrec.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
  exact ltWord_primrec.comp hi ((binaryWord_primrec 1).comp hd hc)

theorem aboveWord_primrec : Primrec₂ aboveWord := by
  have hj := Primrec.unpair.comp (Primrec.snd (α := ℕ) (β := ℕ))
  have hi := integerWord_primrec.comp (Primrec.fst.comp hj)
  have hd := naturalWord_primrec.comp (Primrec.nat_add.comp (Primrec.snd.comp hj) (Primrec.const 1))
  have hc : Primrec (fun x : ℕ × ℕ => nullaryWord (x.1+2)) :=
    nullaryWord_primrec.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
  exact ltWord_primrec.comp ((binaryWord_primrec 1).comp hd hc) hi

def thetaSentence (n : ℕ) : Formula := lt (mul (natural 2) (c n)) one
def theta (n : ℕ) : ℕ := formulaCode (thetaSentence n)
def halfIndex : ℕ := Rationals.positiveIndex 1 2

theorem halfIndex_value : Rationals.q halfIndex=(1 : ℚ)/2 :=
  Rationals.q_positiveIndex 1 2 (by decide)
theorem below_half_shape (n : ℕ) : belowSentence n halfIndex=lt one (mul (natural 2) (c n)) := by
  simp [belowSentence,halfIndex,Rationals.positiveIndex,Nat.unpair_pair,integerTerm,natural,positiveNatural]
theorem above_half_shape (n : ℕ) : aboveSentence n halfIndex=thetaSentence n := by
  simp [aboveSentence,thetaSentence,halfIndex,Rationals.positiveIndex,Nat.unpair_pair,integerTerm,natural,positiveNatural]
theorem theta_above_half (n : ℕ) : theta n=aboveWord n halfIndex :=
  (congrArg formulaCode (above_half_shape n)).symm.trans (formulaCode_aboveSentence n halfIndex)
theorem theta_primrec : Primrec theta :=
  (aboveWord_primrec.comp Primrec.id (Primrec.const halfIndex)).of_eq (fun n => (theta_above_half n).symm)
@[simp] theorem thetaSentence_closed (n : ℕ) : (thetaSentence n).freeVariables=[] := by
  simp [thetaSentence]

def sentencePredicate : Carrier := ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔
  variableSymbols functionSymbols relationSymbols bound

theorem sentence_formulaCode (φ : Formula) :
    sentencePredicate.val.Evalb ![formulaCode φ] ↔ φ.freeVariables=[] := by
  refine (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound ℕ (formulaCode φ)).trans ?_
  have hf := (Postfix.carrier_plain_model true termPolynomial formulaPolynomial (formulaCode φ)).mp
    (NamedPostfixEncoding.formulaCode_member φ)
  constructor
  · intro h
    exact (NamedPostfixEncoding.sentence_formulaCode_iff φ).mp h.2
  · intro h
    exact ⟨hf,(NamedPostfixEncoding.sentence_formulaCode_iff φ).mpr h⟩

theorem belowWord_accepted (n j : ℕ) :
    (Postfix.carrier true termPolynomial formulaPolynomial).val.Evalb ![belowWord n j] := by
  rw [← formulaCode_belowSentence]
  exact NamedPostfixEncoding.formulaCode_member _
theorem aboveWord_accepted (n j : ℕ) :
    (Postfix.carrier true termPolynomial formulaPolynomial).val.Evalb ![aboveWord n j] := by
  rw [← formulaCode_aboveSentence]
  exact NamedPostfixEncoding.formulaCode_member _
theorem belowWord_sentence (n j : ℕ) : sentencePredicate.val.Evalb ![belowWord n j] := by
  rw [← formulaCode_belowSentence,sentence_formulaCode]
  exact belowSentence_closed n j
theorem aboveWord_sentence (n j : ℕ) : sentencePredicate.val.Evalb ![aboveWord n j] := by
  rw [← formulaCode_aboveSentence,sentence_formulaCode]
  exact aboveSentence_closed n j
theorem theta_sentence (n : ℕ) : sentencePredicate.val.Evalb ![theta n] :=
  (sentence_formulaCode (thetaSentence n)).mpr (thetaSentence_closed n)

theorem negation_constructor (word : ℕ) :
    negationWord word=constructor true formulaPolynomial (negInput word) := rfl
theorem negation_sentence (φ : Formula) (hφ : φ.freeVariables=[]) :
    sentencePredicate.val.Evalb ![negationWord (formulaCode φ)] := by
  rw [← formulaCode_negation,sentence_formulaCode]
  exact hφ

/-- The order-asymmetry sentence retains the distinct literal names 0 and 1. -/
def orderAsymmetry : Formula := all 0 (all 1
  (imp (lt (var 0) (var 1)) (negation (lt (var 1) (var 0)))))

theorem orderAsymmetry_closed : orderAsymmetry.freeVariables=[] := by
  simp [orderAsymmetry,all,imp,negation,var,NamedFiniteSyntax.Formula.freeVariables,
    NamedFiniteSyntax.Term.freeVariables]
theorem orderAsymmetry_sentence : sentencePredicate.val.Evalb ![formulaCode orderAsymmetry] :=
  (sentence_formulaCode _).mpr orderAsymmetry_closed

abbrev asymmetrySentence : Formula := orderAsymmetry
abbrev asymmetryWord : ℕ := formulaCode asymmetrySentence
theorem asymmetrySentence_closed : asymmetrySentence.freeVariables=[] := orderAsymmetry_closed
theorem asymmetryWord_sentence : sentencePredicate.val.Evalb ![asymmetryWord] := orderAsymmetry_sentence

def cutAxioms (a : Point) : Set ℕ := {word |
  (∃ n j,(Rationals.q j : ℝ)<(a n : ℝ) ∧ belowWord n j=word) ∨
  (∃ n j,(a n : ℝ)<(Rationals.q j : ℝ) ∧ aboveWord n j=word)}

private theorem image_enumerable {P : Uniform.Family} {α : Type} [Primcodable α]
    (A : α → Prop) (hA : Uniform.Enumerable P A) (f : α → ℕ) (hf : Primrec f) :
    Uniform.Enumerable P (fun word => ∃ x,A x ∧ f x=word) := by
  have he : REPred (fun x : ℕ × α => f x.2=x.1) :=
    (Primrec.eq.comp (hf.comp Primrec.snd) Primrec.fst).computablePred.to_re
  exact ((Uniform.Enumerable.comp Computable.snd hA).and (Uniform.Enumerable.of_re he)).projection

theorem cutAxioms_enumerable (a : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈cutAxioms a) := by
  have hlo := image_enumerable _ (StrictRational.rational_below_enumerable a)
    (fun x : ℕ × ℕ => belowWord x.1 x.2) belowWord_primrec
  have hhi := image_enumerable _ (StrictRational.rational_above_enumerable a)
    (fun x : ℕ × ℕ => aboveWord x.1 x.2) aboveWord_primrec
  exact (hlo.or hhi).of_eq (fun word => by simp only [cutAxioms,Set.mem_ofPred_eq,Prod.exists])

theorem cutAxioms_sentences (a : Point) (word : ℕ) (h : word∈cutAxioms a) :
    sentencePredicate.val.Evalb ![word] := by
  rcases h with ⟨n,j,_,rfl⟩ | ⟨n,j,_,rfl⟩
  · exact belowWord_sentence n j
  · exact aboveWord_sentence n j

theorem lower_cut_axiom (a : Point) (n : ℕ) (h : (a n : ℝ)<1/2) : theta n∈cutAxioms a := by
  refine Or.inr ⟨n,halfIndex,?_,(theta_above_half n).symm⟩
  simpa only [halfIndex_value,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h

theorem upper_cut_axiom (a : Point) (n : ℕ) (h : 1/2<(a n : ℝ)) :
    formulaCode (lt one (mul (natural 2) (c n)))∈cutAxioms a := by
  refine Or.inl ⟨n,halfIndex,?_,?_⟩
  · simpa only [halfIndex_value,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  · exact (formulaCode_belowSentence n halfIndex).symm.trans (congrArg formulaCode (below_half_shape n))

end CategoricalEssentialIncompleteness.V46.Miller.OrderedFieldSyntax
