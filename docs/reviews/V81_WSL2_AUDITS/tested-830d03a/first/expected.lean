import Init

/- Independent proposition types reconstructed with no project imports. `def ... : Prop` names
   a test to be instantiated at the printed data. No theorem in this file asserts these tests. -/
namespace FirstReading
universe u v

abbrev Family (α : Type u) := α → Prop
abbrev Oracle := Nat → Bool
abbrev Run := Nat → Oracle → Nat → Nat → Prop

def Included {α : Type u} (p q : Family α) := ∀ x, p x → q x
def SeparatedBy {α : Type u} (p q d : Family α) := Included p d ∧ ∀ x, q x → ¬ d x

def MillerProperty {R : Type} (rep : Oracle → (Nat → R) → Prop) (eval : Run)
    (accurate : Nat → Nat → R → Prop) (a : Nat → R) : Prop :=
  ∀ d r, (∀ p, rep p a → ∀ k, ∃ j, eval d p k j ∧ accurate k j r) → a d = r

/-- R must be [0,1], rep the binary expansion fiber and accurate k j r the strict
    approximation of r by rational q_j. All three identifications need witnesses. -/
def MillerExists {R : Type} (rep : Oracle → (Nat → R) → Prop) (eval : Run)
    (accurate : Nat → Nat → R → Prop) : Prop := ∃ a, MillerProperty rep eval accurate a

def Unanimity {R : Type} (rep : Oracle → (Nat → R) → Prop) (eval : Run)
    (pair : Nat → Nat → Nat) : Prop :=
  ∃ machine, ∀ z p, rep p z → ∀ e n m,
    eval machine p (pair e n) m ↔ ∀ q, rep q z → eval e q n m

def NumericalReduction (a₀ a₁ left right : Family Nat)
    (recursive : (Nat → Nat) → Prop) : Prop :=
  ∃ h, recursive h ∧ (∀ n, left (h n) ↔ a₀ n) ∧ (∀ n, right (h n) ↔ a₁ n)

def IndividualAndUniform (rep : Family Oracle) (eval : Run) (left right : Family Nat) : Prop :=
  (∀ p, rep p → ∃ (d : Family Nat) (e : Nat), SeparatedBy left right d ∧
    (∀ n, (eval e p n 1 ↔ d n) ∧ (eval e p n 0 ↔ ¬ d n))) ∧
  ¬ ∃ (d : Family Nat) (e : Nat), SeparatedBy left right d ∧
    ∀ p, rep p → ∀ n, (eval e p n 1 ↔ d n) ∧ (eval e p n 0 ↔ ¬ d n)

/-- σ ranges over genuine finite sentences of the printed field language. The axiom set
    may be presented by different proof objects, but a single index semidecides it on all names. -/
def FieldIndependence {Sent : Type} (rep : Family Oracle) (eval : Run)
    (code : Sent → Nat) (neg : Sent → Sent) (derives : Family Sent → Sent → Prop)
    (base : Family Sent) : Prop :=
  ∀ axioms : Family Sent,
    (∀ s, base s → derives axioms s) →
    (¬ ∃ s, derives axioms s ∧ derives axioms (neg s)) →
    (∃ i, ∀ p, rep p → ∀ s, (∃ v, eval i p (code s) v) ↔ axioms s) →
    ∃ s, ¬ derives axioms s ∧ ¬ derives axioms (neg s)

/-- Hom must come from the specified syntactic split *total* category, with E=ω, S the
    actual arithmetic sentence object, interpretation the standard graph interpretation. -/
def ArithmeticUniform {Hom Sent : Type} (interpret : Hom → Nat → Sent)
    (nel : Nat → Sent → Prop) (neg : Sent → Sent) (consistent : Nat → Prop) : Prop :=
  ∃ q : Hom, ∀ e, consistent e → ¬ nel e (interpret q e) ∧ ¬ nel e (neg (interpret q e))

def CommonEvaluation {Proof Sentence : Type} (pos neg : Family Nat)
    (derivationFrom : Proof → Prop) (concl : Proof → Sentence)
    (notF : Sentence → Sentence) (support : Proof → List Nat)
    (holds : List Nat → Sentence → Prop) : Prop :=
  (∀ n, pos n → ¬ neg n) → ∀ p q, derivationFrom p → derivationFrom q →
    holds (support p ++ support q) (concl p) ∧ holds (support p ++ support q) (concl q) ∧
    (∀ s, holds (support p ++ support q) (notF s) ↔ ¬ holds (support p ++ support q) s)

def InitialOver {P F D : Type u} (concl : D → P × F)
    (IsAlgebra : (Q : Type u) → (Q → P × F) → Type u)
    (construction : IsAlgebra D concl)
    (commutes : ∀ {Q : Type u} {q : Q → P × F},
      (D → Q) → IsAlgebra D concl → IsAlgebra Q q → Prop) : Prop :=
  ∀ (Q : Type u) (q : Q → P × F) (β : IsAlgebra Q q),
    ∃ e : D → Q, (∀ d, q (e d) = concl d) ∧ commutes e construction β ∧
      ∀ e' : D → Q, (∀ d, q (e' d) = concl d) → commutes e' construction β → e' = e

/-- Both proof translations are computable on their carriers. Equality of theorem sets
    alone drops the bijection of derivation witnesses. -/
def ProofCorrespondence {N S C : Type} (num : N → C) (syn : S → C)
    (effectiveTo : (N → S) → Prop) (effectiveFrom : (S → N) → Prop) : Prop :=
  ∃ f : N → S, ∃ g : S → N, effectiveTo f ∧ effectiveFrom g ∧
    (∀ d, g (f d) = d) ∧ (∀ d, f (g d) = d) ∧ ∀ d, syn (f d) = num d

def Complete {A : Type u} (T : Family A) (neg : A → A) := ∀ s, T s ∨ T (neg s)
def Consistent {A : Type u} (T : Family A) (neg : A → A) := ∀ s, ¬ (T s ∧ T (neg s))
def SetEssential {A : Type u} (T : Family A) (neg : A → A) (closed : Family A → Prop) :=
  Consistent T neg ∧ ∀ U, closed U → Included T U → Consistent U neg → ¬ Complete U neg

/-- Sub, Closed, consistency and completeness must be instantiated at categorical
    subobjects, including arbitrary U in D/U, even where there are few global elements. -/
def CategoricalEssential {Sub : Type u} (le : Sub → Sub → Prop)
    (closed consistent complete : Sub → Prop) (t : Sub) :=
  consistent t ∧ ∀ w, closed w → le t w → consistent w → ¬ complete w

def SliceEssential {A B : Type u} (base : A → Prop) (slice : B → Prop) (bu : A → B)
    (consistent : A → Prop) := ∀ u, consistent u → (base u ↔ slice (bu u))

def DiagonalComparison {src dom : Type u} (total : src → Prop) (zero : dom)
    (pre : src → dom → dom) (p n : dom) := ∃ g : src, total g ∧ pre g p = zero ∧ pre g n = zero

def NontrivialTerminalPredicate {T : Type u} (zero one : T) : Prop :=
  ∃ e, e ≠ zero ∧ e ≠ one

def CountableDedekindReals {Topos : Type u} (Object : Topos → Type v)
    (Hom : (E : Topos) → Object E → Object E → Type v)
    (nno dedekind : (E : Topos) → Object E) (isParameterizedRealizability : Topos → Prop)
    (epi : ∀ E {A B}, Hom E A B → Prop) : Prop :=
  ∃ E, isParameterizedRealizability E ∧ ∃ f : Hom E (nno E) (dedekind E), epi E f

def MpvAntecedent (ce : Family Nat → Prop) (recursive : Family Nat → Prop)
    (signedClassTheory : Family Nat → Family Nat → Type) (eundec : Type → Prop) : Prop :=
  ∀ a b, ce a → ce b → (∀ n, a n → ¬ b n) →
    (eundec (signedClassTheory a b) ↔ ¬ ∃ d, recursive d ∧ SeparatedBy a b d)

def QuotientFailure {Index : Type} (eq : Index → Index → Prop) (comp : Index → Index → Index) :=
  ∃ e e' f f', eq e e' ∧ eq f f' ∧ ¬ eq (comp f e) (comp f' e')

def DpmNonlocal {Hom Dom : Type u} (restrict : Hom → Dom → Hom)
    (conn : Dom → Prop) : Prop :=
  ∃ f g, f ≠ g ∧ ∀ a, conn a → restrict f a = restrict g a

def EndpointNumbering {Word : Type} (atom : Nat × Nat → Word) (neg : Word → Word)
    (ce : Family Word → Prop) (base : Family Word) (proves : Family Word → Word → Prop) : Prop :=
  ∀ A, ce A → (∀ w, base w → proves A w) → (∀ w, ¬ (proves A w ∧ proves A (neg w))) →
    ∃ x, ¬ proves A (atom x) ∧ ¬ proves A (neg (atom x))
end FirstReading
