module

/- Independently written specifications for comparison with the checked declarations.
   Arguments naming a construction in the manuscript must ultimately be instantiated by that construction.
   The definitions specify statements and supply no proof of existence. -/
namespace SecondReading

universe u v

def Preimage {X : Type u} {Y : Type v} (f : X → Y) (p : Y → Prop) : X → Prop :=
  fun x => p (f x)

def Included {X : Type u} (A B : X → Prop) : Prop := ∀ x, A x → B x

def Complementary {X : Type u} (A B : X → Prop) : Prop :=
  (∀ x, ¬ (A x ∧ B x)) ∧ ∀ x, A x ∨ B x

def Separated {X : Type u} (Admissible : (X → Prop) → Prop) (A B : X → Prop) : Prop :=
  ∃ C D, Admissible C ∧ Admissible D ∧ Complementary C D ∧ Included A C ∧ Included B D

def EntireTheoryCriterion {α β : Type u} [LE α] [LE β]
    (isComplementα : α → α → Prop) (cons complete closed : β → Prop)
    (generateSigned : α → α → β) (disjoint : α → α → Prop) : Prop :=
  ∀ a b, disjoint a b → cons (generateSigned a b) →
    ((∀ U, generateSigned a b ≤ U → cons U → closed U → ¬ complete U) ↔
      ¬ ∃ c d, isComplementα c d ∧ a ≤ c ∧ b ≤ d)

def GeneratedAdjunction {A B : Type u}
    (Hom₁ : A → A → Type v) (Hom₂ : B → B → Type v)
    (generate : A → B) (observe : B → A)
    (extend : ∀ x y, Hom₁ x (observe y) → Hom₂ (generate x) y)
    (restrict : ∀ x y, Hom₂ (generate x) y → Hom₁ x (observe y)) : Prop :=
  (∀ x y k, extend x y (restrict x y k) = k) ∧
    (∀ x y f, restrict x y (extend x y f) = f)

def IsUniformSentenceMorph {Mor : Type u} (evaluate : Mor → Nat → Nat)
    (consistent : Nat → Prop) (provable : Nat → Nat → Prop)
    (negation : Nat → Nat) : Prop :=
  ∃ q : Mor, ∀ e, consistent e →
    ¬ provable e (evaluate q e) ∧ ¬ provable e (negation (evaluate q e))

def ActualNumeralMorphism {Mor : Type u} (eval : Mor → Nat → Nat)
    (closedInstance : Nat → Nat) : Prop := ∃ θ : Mor, ∀ n, eval θ n = closedInstance n

def FiniteProofBijection {P Q : Type u} {S : Type v} (c : P → S) (d : Q → S)
    (computable : (P → Q) → Prop) (computable' : (Q → P) → Prop) : Prop :=
  ∃ f : P → Q, ∃ g : Q → P, computable f ∧ computable' g ∧
    (∀ p, g (f p) = p) ∧ (∀ q, f (g q) = q) ∧ ∀ p, d (f p) = c p

def AllNumeralFibers (Enumerated : Nat → Nat → Prop) (isSigmaOne : (Nat → Nat → Prop) → Prop)
    (PaProvesIff : (Nat → Prop) → (Nat → Prop) → Prop) : Prop :=
  ∃ Family : Nat → Nat → Prop, isSigmaOne Family ∧ ∀ e, PaProvesIff (Family e) (Enumerated e)

def ModelSoundness {M : Type u} 
    (ProofAt : M → Type v) (SentenceAt : M → Type v) (ValidAt : M → Type v)
    (concl : ∀ m, ProofAt m → SentenceAt m) (valid : ∀ m, ValidAt m → SentenceAt m)
    (neg : ∀ m, SentenceAt m → SentenceAt m) : Prop :=
  ∀ m, ∃ k : ProofAt m → ValidAt m,
    (∀ p, valid m (k p) = concl m p) ∧
    (∀ a b : ValidAt m, valid m a ≠ neg m (valid m b)) ∧
    ∀ k' : ProofAt m → ValidAt m, (∀ p, valid m (k' p) = concl m p) → k' = k

def IsMiller {Point Real Name : Type u} (entry : Point → Nat → Real)
    (names : Point → Name → Prop) (validReal : Real → Prop)
    (codeApprox : Nat → Name → Nat → Real → Prop) (a : Point) : Prop :=
  ∀ d r, validReal r → (∀ p, names a p → ∀ k, codeApprox d p k r) → entry a d = r

def MillerWitness {Point Real Name : Type u} (entry : Point → Nat → Real)
    (names : Point → Name → Prop) (validReal : Real → Prop)
    (codeApprox : Nat → Name → Nat → Real → Prop) : Prop :=
  ∃ a : Point, IsMiller entry names validReal codeApprox a

def UnanimousEvaluator {Point Name : Type u} (names : Point → Name → Prop)
    (runs : Nat → Name → Nat → Nat → Prop) (pair : Nat → Nat → Nat) : Prop :=
  ∃ D, ∀ a p, names a p → ∀ e n m,
    (runs D p (pair e n) m ↔ ∀ q, names a q → runs e q n m)

def TotalReduction (A B L R : Nat → Prop) (isRecursive : (Nat → Nat) → Prop) : Prop :=
  ∃ h : Nat → Nat, isRecursive h ∧ (∀ n, A n ↔ L (h n)) ∧ ∀ n, B n ↔ R (h n)

def FamilyIndependentCut {Name : Type u} (isName : Name → Prop)
    (decides : Nat → Name → (Nat → Prop) → Prop) (L R : Nat → Prop) : Prop :=
  (∀ p, isName p → ∃ C d, decides d p C ∧ Included L C ∧ ∀ n, R n → ¬ C n) ∧
    ¬ ∃ C d, Included L C ∧ (∀ n, R n → ¬ C n) ∧ ∀ p, isName p → decides d p C

def BoolValuationMorphism {Mor Form Label : Type u} (on : Mor → List Label → Form → Bool)
    (atom : Label → Form) (member : Label → List Label → Bool) : Prop :=
  ∃ v : Mor, ∀ l x, on v l (atom x) = member x l

def ActualRangeProvability {Mono Word : Type u} (closed : Word → Prop)
    (conclImage finiteHilbert : Mono → Word → Prop) : Prop :=
  ∀ (m : Mono) w, closed w → (conclImage m w ↔ finiteHilbert m w)

def SameConclusionOver {M N : Type u} {S : Type v} (sentence₁ : M → S) (sentence₂ : N → S) : Prop :=
  ∃ e : M → N, ∃ r : N → M,
    (∀ m, r (e m) = m) ∧ (∀ n, e (r n) = n) ∧ ∀ m, sentence₂ (e m) = sentence₁ m

def SourceConditional {X : Type u} {Y : Type v} (carrier : X → Prop) (ι : Bool → X → Y)
    (isSource : (X → Y) → Prop) : Prop :=
  ∃ s : X → Y, isSource s ∧ ∀ x, (carrier x → s x = ι true x) ∧ (¬ carrier x → s x = ι false x)

end SecondReading

namespace SecondReading

universe u v

theorem reduction_of_separation {X : Type u} {Y : Type v}
    {AdX : (X → Prop) → Prop} {AdY : (Y → Prop) → Prop}
    {a b : X → Prop} {t n : Y → Prop} (θ : X → Y)
    (stable : ∀ c, AdY c → AdX (Preimage θ c))
    (lower : Included a (Preimage θ t)) (upper : Included b (Preimage θ n))
    (separator : Separated AdY t n) : Separated AdX a b := by
  obtain ⟨c,d,hc,hd,⟨dis,cover⟩,ht,hn⟩ := separator
  exact ⟨Preimage θ c, Preimage θ d, stable c hc, stable d hd,
    ⟨fun x => dis (θ x), fun x => cover (θ x)⟩,
    fun x h => ht (θ x) (lower x h), fun x h => hn (θ x) (upper x h)⟩

theorem diagonal_avoidance {X : Type u} (P N : X → Prop) (g : X → X)
    (disjoint : ∀ x, P x → ¬N x)
    (odd : ∀ x, P (g x) → N (g x))
    (even : ∀ x, N (g x) → P (g x)) : ∀ x, ¬ P (g x) ∧ ¬ N (g x) := by
  intro x
  exact ⟨fun h => disjoint _ h (odd x h), fun h => disjoint _ (even x h) h⟩

theorem global_points_miss_properness {X : Type u} {S : X → Prop} (x : X)
    (out : ¬ S x) : ¬ ∀ y, S y :=
  fun all => out (all x)

def IndexedProofAlgebra
    {F P Rule Proof : Type u}
    (parameter : Proof → P) (conclusion : Proof → F)
    (ruleArity : Rule → Nat) (ruleConclusion : Rule → F)
    (valid : P → Proof → Prop) (infer : Rule → List Proof → Proof)
    (allowed : P → Rule → Prop) : Prop :=
  ∀ p : P, ∀ r : Rule, ∀ inputs : List Proof,
    allowed p r → inputs.length = ruleArity r →
    (∀ d, d ∈ inputs → valid p d) →
    valid p (infer r inputs) ∧ parameter (infer r inputs) = p ∧ conclusion (infer r inputs) = ruleConclusion r

def InitialInSlice
    {Object : Type u} (Hom : Object → Object → Type v)
    (Base : Object) (H : Object → Object)
    (Over : ∀ {X Y}, Hom X Y → Hom X Base → Hom Y Base → Prop)
    (Alg : ∀ Q, Hom Q Base → Hom (H Q) Q → Prop)
    (Commutes : ∀ {D Q}, Hom D Q → Hom (H D) D → Hom (H Q) Q → Prop) : Prop :=
  ∃ D, ∃ c : Hom D Base, ∃ δ : Hom (H D) D, Alg D c δ ∧
    ∀ Q q β, Alg Q q β → ∃ h : Hom D Q, Over h c q ∧ Commutes h δ β ∧
      ∀ h' : Hom D Q, Over h' c q → Commutes h' δ β → h' = h

def UniformArithmeticCompiler
    {Sentence : Type u} (provPA : Sentence → Prop) (primitiveRecursive : (Nat → Nat → Nat) → Prop)
    (universal : Nat → Sentence) (specialization composes : (Nat → Nat → Nat) → Sentence)
    (functional : Sentence) : Prop :=
  ∃ u, ∃ s c, primitiveRecursive s ∧ primitiveRecursive c ∧ provPA functional ∧
    provPA (universal u) ∧ provPA (specialization s) ∧ provPA (composes c)

def PARefutationOfTwoSignedDerivations {Sentence : Type u}
    (ProvablePA : Sentence → Prop) (formalContradictionExcluded : Sentence) : Prop :=
  ProvablePA formalContradictionExcluded

def FunctorAtCopiedTheory {ObjC ObjD : Type u} (MorC : ObjC → ObjC → Type v)
    (MorD : ObjD → ObjD → Type v) (mapObj : ObjC → ObjD)
    (map : ∀ {a b}, MorC a b → MorD (mapObj a) (mapObj b)) : Prop :=
  ∀ A B, ∀ f : MorD (mapObj A) (mapObj B), ∃ g : MorC A B, map g = f ∧
    ∀ h : MorC A B, map h = f → h = g

end SecondReading
