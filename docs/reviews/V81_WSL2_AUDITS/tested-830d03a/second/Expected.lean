import Mathlib

/-!
Expected types reconstructed by the second reader from the manuscript. Every definition
below *names a proposition or a data type*. There are no declarations postulating
inhabitants. Abstract categorical data are parameters in this comparison vocabulary.
The reconstruction gives their printed hypotheses, constructions, and witnesses.
-/
namespace SecondReading

universe u v w u' v'

abbrev Pred (X : Type u) := X → Prop

def Contained {X : Type u} (A B : Pred X) : Prop := ∀ x, A x → B x

def DisjointPred {X : Type u} (A B : Pred X) : Prop := ∀ x, ¬ (A x ∧ B x)

def ImagePred {X : Type u} {Y : Type v} (f : X → Y) (A : Pred X) : Pred Y :=
  fun y => ∃ x, A x ∧ f x = y

structure Domains (D : Type u) where
  le : D → D → Prop
  meet : D → D → D
  join : D → D → D
  zero top : D

def Domains.Complement {D : Type u} (d : Domains D) (a b : D) : Prop :=
  d.meet a b = d.zero ∧ d.join a b = d.top

def Domains.Inseparable {D : Type u} (d : Domains D) (a b : D) : Prop :=
  d.meet a b = d.zero ∧ ¬ ∃ c c', d.Complement c c' ∧ d.le a c ∧ d.le b c'

def Domains.Essential {D : Type u} (d : Domains D) (negPB : D → D)
    (closed : D → Prop) (t : D) : Prop :=
  d.meet t (negPB t) = d.zero ∧
  ∀ u, closed u → d.le t u → d.meet u (negPB u) = d.zero → d.join u (negPB u) ≠ d.top

def SignedEquivalence {D : Type u} {S : Type v} (d : Domains D) (s : Domains S)
    (negPB : S → S) (closed : S → Prop) (generated : D → D → S) : Prop :=
  ∀ a b, d.meet a b = d.zero →
    s.meet (generated a b) (negPB (generated a b)) = s.zero →
    (s.Essential negPB closed (generated a b) ↔ d.Inseparable a b)

def DiagonalComparison {D : Type u} {G : Type v} (d : Domains D) (total : G → Prop)
    (pb : G → D → D) (a₀ a₁ : D) (liftedSwap : D → D → Prop) : Prop :=
  ∀ p n, d.le a₀ p → d.le a₁ n → d.meet p n = d.zero → liftedSwap p n →
  ∃ g, total g ∧ pb g p = d.zero ∧ pb g n = d.zero

def DiagonalProper {D : Type u} {G : Type v} (d : Domains D) (total : G → Prop)
    (pb : G → D → D) : Prop :=
  ∀ g p n, total g → d.top ≠ d.zero → pb g p = d.zero → pb g n = d.zero →
    pb g (d.join p n) = d.join (pb g p) (pb g n) → d.join p n ≠ d.top

def PullbackInseparability {X : Type u} {S : Type v} (x : Domains X) (s : Domains S)
    (pb : S → X) (negPB : S → S) (a b : X) (t₀ : S) : Prop :=
  x.Inseparable a b → x.le a (pb t₀) → x.le b (pb (negPB t₀)) →
  ∀ t, s.le t₀ t → s.meet t (negPB t) = s.zero →
    s.Inseparable t (negPB t) ∧ s.join t (negPB t) ≠ s.top

open CategoryTheory

def FreeSigned {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (generate : A ⥤ B) (observe : B ⥤ A) := generate ⊣ observe

def GenerationReflection {D : Type u} (d : Domains D) (gen : D → D) : Prop :=
  (∀ a, d.le a (gen a)) ∧ (∀ a b, d.le a b → d.le (gen a) (gen b)) ∧
  (∀ a, gen (gen a) = gen a) ∧ (∀ a t, gen t = t → (d.le (gen a) t ↔ d.le a t))

def GenerationNaturality {D : Type u} {E : Type v} (gD : D → D) (gE : E → E)
    (image : D → E) : Prop := ∀ a, gE (image (gD a)) = gE (image a)

def MutualSliceAdjunction {A : Type u} [Category.{v} A] {B : Type u'} [Category.{v'} B]
    (post : A ⥤ B) (pull : B ⥤ A) := (post ⊣ pull) × (pull ⊣ post)

def HomBijection {H : Type u} {K : Type v} (extend : H → K) (restrict : K → H) : Prop :=
  Function.LeftInverse restrict extend ∧ Function.RightInverse restrict extend

def SliceCorrespondence {S : Type u} {W : Type v} (s : Domains S) (w : Domains W)
    (ns : S → S) (nw : W → W) (cs : S → Prop) (cw : W → Prop) (B : S → W) : Prop :=
  ∀ t, cs t → s.meet t (ns t) = s.zero → (s.Essential ns cs t ↔ w.Essential nw cw (B t))

def PartialBooleanCriterion {S : Type u} {P : Type v} (s : Domains S) (nw : S → S)
    (constantDelta : S → P) (total hasTotalExtension : P → Prop) : Prop :=
  ∀ t, s.meet t (nw t) = s.zero →
    ((s.join t (nw t) ≠ s.top ↔ ¬ total (constantDelta t)) ∧
      (s.Inseparable t (nw t) ↔ ¬ hasTotalExtension (constantDelta t)))

def BinaryInitial {C : Type u} [Category.{v} C] (F : C ⥤ C) (T : C) (ι : F.obj T ⟶ T) :
    Prop := ∀ (A : C) (a : F.obj A ⟶ A), ∃! f : T ⟶ A, ι ≫ f = F.map f ≫ a

def RuleImageClosed {D : Type u} (d : Domains D) (closed : D → Prop) (image : D) : Prop :=
  closed image ∧ ∀ t, closed t → d.le image t

def TermEvaluationSubstitution {Tm : Type u} {K : Type v}
    (eval : Tm → (ℕ → K) → K) (sub : Tm → ℕ → Tm → Tm) : Prop :=
  ∀ r x t σ, eval (sub r x t) σ = eval r (Function.update σ x (eval t σ))

def FormulaEvaluationSubstitution {Fm : Type u} {Tm : Type v} {K : Type w}
    (val : Tm → (ℕ → K) → K) (sat : Fm → (ℕ → K) → Prop)
    (subst : Fm → ℕ → Tm → Option Fm) : Prop :=
  ∀ φ x t ψ σ, subst φ x t = some ψ → (sat ψ σ ↔ sat φ (Function.update σ x (val t σ)))

def SoundFactorization {P : Type u} {S : Type v} {V : Type w}
    (conc : P → S) (valid : V → S) (neg : S → S) : Prop :=
  (∃! e : P → V, valid ∘ e = conc) ∧
  DisjointPred (Set.range valid) (fun s => neg s ∈ Set.range valid)

def GraphQuotientEquality (provablyEquivalent : ℕ → ℕ → Prop)
    (categoryEqual : ℕ → ℕ → Prop) : Prop :=
  ∀ e f, categoryEqual e f ↔ provablyEquivalent e f

def GraphSearch (R : ℕ → ℕ → Prop) (graph : ℕ → ℕ → ℕ → Prop)
    (paProves : Prop → Prop) : Prop :=
  ∃ e, paProves (∀ x y, graph e x y → R x y) ∧
      paProves (∀ x, (∃ y, graph e x y) ↔ ∃ y, R x y)

/- Here 'paProves' in GraphSearch is a schema for the universal closure
   of a coded arithmetic formula. The phase-two test must expand the
   Hilbert judgment, not take the truth of the displayed metaproposition
   as evidence of an arithmetic proof. -/
def CodedPAGraphSearch {Closed : Type u}
    (sigmaOneFormula : Type v) (impl domEq : sigmaOneFormula → ℕ → Closed)
    (proves : Closed → Prop) : Prop :=
  ∀ Γ, ∃ e, proves (impl Γ e) ∧ proves (domEq Γ e)

def ArithmeticUniform {Hom : Type u} (interpret : Hom → ℕ → ℕ)
    (consistent : ℕ → Prop) (isSentence : ℕ → Prop)
    (provable : ℕ → ℕ → Prop) (neg : ℕ → ℕ) : Prop :=
  ∃ q, ∀ e, isSentence (interpret q e) ∧
    (consistent e → ¬ provable e (interpret q e) ∧ ¬ provable e (neg (interpret q e)))

def EffectiveProofBijection {P : Type u} {Q : Type v} {S : Type w} (p : P → S) (q : Q → S)
    (computableTo : (P → Q) → Prop) (computableFrom : (Q → P) → Prop) : Prop :=
  ∃ b : P ≃ Q, computableTo b ∧ computableFrom b.symm ∧ ∀ x, q (b x) = p x

abbrev BitOracle := ℕ → Bool
abbrev RealSequence := ℕ → ℝ
abbrev OracleOutput := ℕ → BitOracle → ℕ → ℕ → Prop

def MillerProperty (binary : BitOracle → RealSequence) (run : OracleOutput) (rat : ℕ → ℚ)
    (a : RealSequence) : Prop :=
  (∀ n, a n ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ d (r : ℝ), r ∈ Set.Icc 0 1 →
    (∀ p, binary p = a → ∀ k : ℕ, ∃ j, run d p k j ∧ |(rat j : ℝ) - r| < (2 : ℝ) ^ (-(k : ℤ))) →
      a d = r

def MillerExistence (binary : BitOracle → RealSequence) (run : OracleOutput) (rat : ℕ → ℚ) :
    Prop := ∃ a, MillerProperty binary run rat a

def Unanimity (binary : BitOracle → RealSequence) (run : OracleOutput) (pair : ℕ → ℕ → ℕ) :
    Prop := ∃ u, ∀ p e n m, run u p (pair e n) m ↔ ∀ q, binary q = binary p → run e q n m

def UniformSemidecider (binary : BitOracle → RealSequence) (run : OracleOutput)
    (a : RealSequence) (A : Pred ℕ) : Prop :=
  ∃ e, ∀ p, binary p = a → ∀ n, (∃ y, run e p n y) ↔ A n

def NumericInseparable {X : Type u} (decides : Pred X → Prop) (a b : Pred X) : Prop :=
  DisjointPred a b ∧ ¬ ∃ c, decides c ∧ Contained a c ∧ DisjointPred b c

def EndpointConsequence {V : Type u} {S : Type v} (atom : V → S) (neg : S → S)
    (base : Pred S) (ce : Pred S → Prop) (gen : Pred S → Pred S) : Prop :=
  DisjointPred base (fun s => base (neg s)) ∧
  ∀ A, ce A → Contained base (gen A) → DisjointPred (gen A) (fun s => gen A (neg s)) →
    ∃ x, ¬ gen A (atom x) ∧ ¬ gen A (neg (atom x))

def ConservativeFragment {PropForm : Type u} {Sent : Type v}
    (incl : PropForm → Sent) (p : Pred PropForm) (f : Pred Sent) : Prop :=
  ∀ h, p h ↔ f (incl h)

def NumericalPrecomplete (graph : ℕ → ℕ → ℕ → Prop) (R : ℕ → ℕ → Prop)
    (comp : (ℕ → ℕ) → Prop) : Prop :=
  ∀ e, ∃ g, comp g ∧ ∀ x y, graph e x y → R y (g x)

def NumericalClassClaim (R : ℕ → ℕ → Prop) (decides : Pred ℕ → Prop) : Prop :=
  ∀ a b, ¬ R a b → NumericInseparable decides (R a) (R b)

def PrecompleteClassUnions (R : ℕ → ℕ → Prop) (decides : Pred ℕ → Prop) : Prop :=
  ∀ a b : Pred ℕ, (∃ x, a x) → (∃ y, b y) → DisjointPred a b →
     (∀ x y, R x y → a x → a y) → (∀ x y, R x y → b x → b y) →
     NumericInseparable decides a b

def DistinctSubterminals {T : Type u} (count : T → ℕ) (fork numerical : T) : Prop :=
  count fork = 5 ∧ count numerical = 2

def MissingConditional (A : Pred ℕ) (belongs : (ℕ → ℕ ⊕ ℕ) → Prop) : Prop :=
  ¬ ∃ ℓ, belongs ℓ ∧ ∀ n, A n ↔ ∃ x, ℓ n = Sum.inr x

def FamilyFaithfulness {Q : Type u} {Model : Type v} {Carrier : Model → Type w}
    (int : (M : Model) → Q → Carrier M) : Prop :=
  ∀ e f, (∀ M, int M e = int M f) → e = f

def FullLiteratureExistence {A : Type u} {B : Type v}
    (sourceHypotheses : A → Prop) (conclusion : A → B → Prop) : Prop :=
  ∀ a, sourceHypotheses a → ∃ b, conclusion a b

end SecondReading
