import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Subobject.Basic

/-!
Original-type comparison schemas from the publications cited in v81. The named
primitives are instantiated by the historical authors' definitions described in
primary-reading.md. These are propositions to check. No proof of the conclusions
occurring in them is a parameter. A realization in a particular category, a
new representation of proof codes, and both directions of an equivalence
require separate identifications before their proofs can be used.
-/

namespace SecondReading.Literature

open CategoryTheory

universe u v w

structure IterationVocabulary where
  iterationCategory : Type u
  totalBSharpSubcategory : iterationCategory → Type v
  locallyConnected : iterationCategory → Prop
  separated : iterationCategory → Prop
  faithfulIterationFunctor : iterationCategory → iterationCategory → Type w
  isotypical : {C : iterationCategory} → totalBSharpSubcategory C → Prop
  uniformlyGenerated : {C : iterationCategory} → totalBSharpSubcategory C → Prop
  recursionCategoryOfTuringDevelopments : {C : iterationCategory} → totalBSharpSubcategory C → Prop

def Heller9_2 (I : IterationVocabulary) : Prop :=
  ∀ C, I.locallyConnected C → ∀ B : I.totalBSharpSubcategory C,
    I.isotypical B → I.uniformlyGenerated B → I.recursionCategoryOfTuringDevelopments B

def Lengyel21 (I : IterationVocabulary) : Prop :=
  ∀ C, I.separated C → ∀ B : I.totalBSharpSubcategory C,
    I.isotypical B → I.uniformlyGenerated B → I.recursionCategoryOfTuringDevelopments B

def Lengyel26WithCorrections (I : IterationVocabulary) : Prop :=
  ∀ C D, I.separated D → Nonempty (I.faithfulIterationFunctor C D) →
    ∀ B : I.totalBSharpSubcategory C,
      I.isotypical B → I.uniformlyGenerated B → I.recursionCategoryOfTuringDevelopments B

def Ch4_9_forward (internalPCA : Type u) (computableMapCategoryIsTuringOn :
    (A : internalPCA) → Prop) : Prop := ∀ A, computableMapCategoryIsTuringOn A

def Ch4_9_reverse (D : Type u) [Category.{v} D] (turingObject : D → Prop)
    (internalPCAOn : D → Type w)
    (computableMaps : (A : D) → internalPCAOn A → Cat.{v, u})
    (splitComputableMaps : ∀ A p,
      (∀ X : computableMaps A p, (X ⟶ X) → Prop) → Cat.{v, u}) : Prop :=
  ∀ A, turingObject A → ∃ p : internalPCAOn A,
    ∃ E : ∀ X : computableMaps A p, (X ⟶ X) → Prop,
      (∀ X e, E X e → e ≫ e = e) ∧ Nonempty (D ≌ splitComputableMaps A p E)

def Joyal5_19 (AUObjectInUrec : Type u) (syntacticallyComplete trivial : AUObjectInUrec → Prop) :
    Prop := ∀ U, syntacticallyComplete U → trivial U

def Joyal5_20 (U₀ : Type u) [Category.{v} U₀] (one : U₀) (consistent : Prop)
    (internalTruthEqualsFalsity minimal : Subobject one) : Prop :=
  consistent → internalTruthEqualsFalsity ≠ minimal

def BauerHanson6_4 (Tμ : Type u) [Category.{v} Tμ] (naturalNumbers dedekindReals : Tμ) :
    Prop := ∃ e : naturalNumbers ⟶ dedekindReals, Epi e

structure RestrictionVocabulary (C : Type u) [Category.{v} C] where
  prod : C → C → C
  sum : C → C → C
  zero : (X Y : C) → (X ⟶ Y)
  total : {X Y : C} → (X ⟶ Y) → Prop
  domain : {X Y : C} → (X ⟶ Y) → (X ⟶ X)
  diagonal : (X : C) → (X ⟶ prod X X)
  sumLeftDomain : (X Y : C) → (sum X Y ⟶ sum X Y)
  sumRightDomain : (X Y : C) → (sum X Y ⟶ sum X Y)
  restrictionDomain : {X : C} → (X ⟶ X) → Prop
  inseparable : {X : C} → (X ⟶ X) → (X ⟶ X) → Prop

def DiPaolaHeller8_15 (C : Type u) [Category.{v} C] (R : RestrictionVocabulary C)
    (cPlusDominical : Prop)
    (turing : (X : C) → (R.prod X X ⟶ R.sum X X) → Prop) : Prop :=
  cPlusDominical → ∀ X τ, turing X τ →
    R.inseparable (R.domain (R.diagonal X ≫ τ ≫ R.sumLeftDomain X X))
      (R.domain (R.diagonal X ≫ τ ≫ R.sumRightDomain X X))

def Cockett7_8 (C : Type u) [Category.{v} C] (R : RestrictionVocabulary C)
    (nontrivial discreteTuring stableFiniteCompatibleJoins : Prop) : Prop :=
  nontrivial → discreteTuring → stableFiniteCompatibleJoins →
    ∃ (X : C) (a b : X ⟶ X), R.restrictionDomain a ∧ R.restrictionDomain b ∧ R.inseparable a b

def Cockett7_14 (C : Type u) [Category.{v} C] (R : RestrictionVocabulary C)
    (terminal : C) (nontrivial turing restrictionZero provabilityPredicateForOrder : Prop) : Prop :=
  nontrivial → turing → restrictionZero → provabilityPredicateForOrder →
    ∃ e : terminal ⟶ terminal, R.restrictionDomain e ∧ e ≠ R.zero terminal terminal ∧ e ≠ 𝟙 terminal

def Montagna3_1 (S : Type u) [Category.{v} S] (R : RestrictionVocabulary S) (X : S)
    (indices : Type w) (indexedDomain : indices → (X ⟶ X))
    (le disjoint : (X ⟶ X) → (X ⟶ X) → Prop)
    (productiveOutside : (R.prod X X ⟶ X) → indices → indices → Prop) : Prop :=
  ∃ a b : X ⟶ X, R.restrictionDomain a ∧ R.restrictionDomain b ∧ disjoint a b ∧
    ∃ g : R.prod X X ⟶ X, R.total g ∧ ∀ i j,
      le a (indexedDomain i) → le b (indexedDomain j) →
      disjoint (indexedDomain i) (indexedDomain j) → productiveOutside g i j

def BernardiNumerical (graph : ℕ → ℕ → ℕ → Prop) (computable : (ℕ → ℕ) → Prop)
    (R : ℕ → ℕ → Prop) : Prop :=
  _root_.Equivalence R →
  (∀ e, ∃ g, computable g ∧ ∀ n m, graph e n m → R m (g n)) →
  (∀ f : ℕ → ℕ, computable f → ∃ n, R n (f n)) ∧
  (∀ a b, ¬ R a b → ¬ ∃ c : ℕ → ℕ, computable c ∧
      (∀ n, R a n → c n = 0) ∧ (∀ n, R b n → c n ≠ 0))

def Bernardi3_1 (C : Type u) [Category.{v} C] (R : RestrictionVocabulary C) (X : C)
    (η : R.prod X X ⟶ R.prod X X) (recursionCategory precomplete : Prop)
    (pair : (X ⟶ X) → (X ⟶ X) → (X ⟶ R.prod X X)) : Prop :=
  recursionCategory → precomplete → ∀ φ : X ⟶ X, ∃ g : X ⟶ X, R.total g ∧
    R.domain (g ≫ pair φ (𝟙 X) ≫ η) = R.domain (g ≫ φ)

def Bernardi3_2 (C : Type u) [Category.{v} C] (R : RestrictionVocabulary C) (X : C)
    (recursionCategory cPlusDominical precomplete : Prop) (unionOfClasses : (X ⟶ X) → Prop)
    (disjoint : (X ⟶ X) → (X ⟶ X) → Prop) : Prop :=
  recursionCategory → cPlusDominical → precomplete → ∀ a b : X ⟶ X, unionOfClasses a → unionOfClasses b →
    a ≠ R.zero X X → b ≠ R.zero X X → disjoint a b → R.inseparable a b

def DiPaolaMontagna4_4 (Theory : Type u) (consistent ce extendsPA
    unprimedSyntacticCategoryLocallyConnected : Theory → Prop) : Prop :=
  ∀ T, consistent T → ce T → extendsPA T → ¬ unprimedSyntacticCategoryLocallyConnected T

def DisjointCEAntecedent (Theory : Type u) (equivalenceRelationTheory : Set ℕ → Set ℕ → Theory)
    (ce : Set ℕ → Prop) (recursivelyInseparable : Set ℕ → Set ℕ → Prop)
    (essentiallyUndecidable : Theory → Prop) : Prop :=
  ∀ X Y, ce X → ce Y → Disjoint X Y →
    (essentiallyUndecidable (equivalenceRelationTheory X Y) ↔ recursivelyInseparable X Y)

def Visser23 (Theory : Type u) (consistent ce essentiallyUndecidable : Theory → Prop)
    (theoremCodes refutationCodes : Theory → Set ℕ)
    (computable : (ℕ → ℕ) → Prop) (inseparable : Set ℕ → Set ℕ → Prop) : Prop :=
  ∀ T, consistent T → ce T → ∀ A B, inseparable A B → ∀ f : ℕ → ℕ,
    computable f → A ⊆ f ⁻¹' theoremCodes T → B ⊆ f ⁻¹' refutationCodes T → essentiallyUndecidable T

def KirstPeters20 (FormalSystem : Type u) (sentence : FormalSystem → Type v)
    (stronglySeparatesDiagonalFork : FormalSystem → Prop)
    (consistentSemidecidableExtension : FormalSystem → FormalSystem → Prop)
    (proves refutes : (S : FormalSystem) → sentence S → Prop) : Prop :=
  ∀ S, stronglySeparatesDiagonalFork S → ∀ T, consistentSemidecidableExtension S T →
    ∃ σ : sentence T, ¬ proves T σ ∧ ¬ refutes T σ

def Voutsadakis7 (HSet Sign : Type u) [Category.{v} HSet] [Category.{v} Sign]
    (freeSignature : HSet ⥤ Sign) (formulaUnderlying : Sign ⥤ HSet) :=
  freeSignature ⊣ formulaUnderlying

end SecondReading.Literature
