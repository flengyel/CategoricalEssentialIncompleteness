import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentFamilies
import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentTuples

/-! Absence invariants for every finite function or relation arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.AbsentConstructors
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {P : D} (A : Over P × Over P)
attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

abbrev family (p : SyntaxPolynomial D) : Over P := (p.withParameters P).eval.obj A

def comparison {T Z : D} (f : A ⟶ (constantFamily P T,constantFamily P Z))
    (p : SyntaxPolynomial D) : family A p ⟶ constantFamily P (p.eval.obj (T,Z)) :=
  (p.withParameters P).eval.map f ≫ SyntaxPolynomial.parameterComparison P (T,Z) p

def value {T Z : D} (f : A ⟶ (constantFamily P T,constantFamily P Z))
    (p : SyntaxPolynomial D) : (family A p).left ⟶ p.eval.obj (T,Z) :=
  (comparison A f p).left ≫ prod.snd

@[simp] theorem value_coefficient {T Z K : D}
    (f : A ⟶ (constantFamily P T,constantFamily P Z)) :
    value A f (.coefficient K) = prod.snd := by
  change ((𝟙 (P ⨯ K) ≫ 𝟙 (P ⨯ K)) ≫ prod.snd) = prod.snd
  simp only [Category.id_comp]

@[simp] theorem value_power {T Z : D}
    (f : A ⟶ (constantFamily P T,constantFamily P Z)) (n : ℕ) :
    value A f (SyntaxPolynomial.power .term n) =
      AbsentTuples.tupleMap A (Z := Z) (f.1.left ≫ prod.snd) n :=
  AbsentTuples.tupleMap_comparison A f n

theorem value_product {T Z : D}
    (f : A ⟶ (constantFamily P T,constantFamily P Z)) (p q : SyntaxPolynomial D) :
    value A f (.product p q) =
      prod.lift ((prod.fst : family A p ⨯ family A q ⟶ family A p).left ≫ value A f p)
        ((prod.snd : family A p ⨯ family A q ⟶ family A q).left ≫ value A f q) := by
  unfold value comparison
  change (prod.map _ _ ≫ (prod.map _ _ ≫ constantProductComparison P _ _)).left ≫
    prod.snd = _
  rw [← Category.assoc, prod.map_map, AbsentTuples.product_comparison_value]

@[simp, reassoc] theorem comparison_inl {T Z : D}
    (f : A ⟶ (constantFamily P T,constantFamily P Z)) (p q : SyntaxPolynomial D) :
    (coprod.inl : family A p ⟶ family A (.sum p q)) ≫ comparison A f (.sum p q) =
      comparison A f p ≫ (constantFamilyFunctor P).map coprod.inl := by
  unfold comparison
  change coprod.inl ≫ (coprod.map _ _ ≫ _) = _
  rw [coprod.inl_map_assoc]
  have hn := SyntaxPolynomial.parameterComparison_inl P (T,Z) p q
  simpa only [Category.assoc] using
    congrArg (fun k => (p.withParameters P).eval.map f ≫ k) hn

@[simp, reassoc] theorem comparison_inr {T Z : D}
    (f : A ⟶ (constantFamily P T,constantFamily P Z)) (p q : SyntaxPolynomial D) :
    (coprod.inr : family A q ⟶ family A (.sum p q)) ≫ comparison A f (.sum p q) =
      comparison A f q ≫ (constantFamilyFunctor P).map coprod.inr := by
  unfold comparison
  change coprod.inr ≫ (coprod.map _ _ ≫ _) = _
  rw [coprod.inr_map_assoc]
  have hn := SyntaxPolynomial.parameterComparison_inr P (T,Z) p q
  simpa only [Category.assoc] using
    congrArg (fun k => (q.withParameters P).eval.map f ≫ k) hn

theorem comparison_comp {B C : D × D}
    (m : A ⟶ (constantFamily P B.1,constantFamily P B.2)) (f : B ⟶ C)
    (p : SyntaxPolynomial D) :
    comparison A (m ≫ ((constantFamilyFunctor P).map f.1,
      (constantFamilyFunctor P).map f.2)) p =
      (p.withParameters P).eval.map m ≫ SyntaxPolynomial.parameterComparison P B p ≫
        (constantFamilyFunctor P).map (p.eval.map f) := by
  unfold comparison
  rw [(p.withParameters P).eval.map_comp, Category.assoc,
    SyntaxPolynomial.parameterComparison_natural]

/-- Pair the original and computed applications of one constructor. -/
def pairConstructor {T Z U Y : D}
    (f g : A ⟶ (constantFamily P T,constantFamily P Z))
    (p : SyntaxPolynomial D) (h : p.eval.obj (T,Z) ⟶ U) (embed : U ⟶ Y) :
    family A p ⟶ constantFamily P (U ⨯ Y) :=
  AbsentFamilies.pairFamily
    (comparison A f p ≫ (constantFamilyFunctor P).map h)
    (comparison A g p ≫ (constantFamilyFunctor P).map (h ≫ embed))

@[simp, reassoc] theorem pairConstructor_original {T Z U Y : D}
    (f g : A ⟶ (constantFamily P T,constantFamily P Z))
    (p : SyntaxPolynomial D) (h : p.eval.obj (T,Z) ⟶ U) (embed : U ⟶ Y) :
    (pairConstructor A f g p h embed).left ≫ prod.snd ≫ prod.fst =
      value A f p ≫ h := by
  simp [pairConstructor, AbsentFamilies.pairFamily, value, constantFamilyFunctor,
    Over.comp_left, Category.assoc]

@[simp, reassoc] theorem pairConstructor_result {T Z U Y : D}
    (f g : A ⟶ (constantFamily P T,constantFamily P Z))
    (p : SyntaxPolynomial D) (h : p.eval.obj (T,Z) ⟶ U) (embed : U ⟶ Y) :
    (pairConstructor A f g p h embed).left ≫ prod.snd ≫ prod.snd =
      value A g p ≫ h ≫ embed := by
  simp [pairConstructor, AbsentFamilies.pairFamily, value, constantFamilyFunctor,
    Over.comp_left, Category.assoc]

@[simp, reassoc] theorem pairConstructor_inl {T Z U Y : D}
    (f g : A ⟶ (constantFamily P T,constantFamily P Z))
    (p q : SyntaxPolynomial D) (h : (SyntaxPolynomial.sum p q).eval.obj (T,Z) ⟶ U) (embed : U ⟶ Y) :
    (coprod.inl : family A p ⟶ family A (.sum p q)) ≫
        pairConstructor A f g (.sum p q) h embed =
      pairConstructor A f g p (coprod.inl ≫ h) embed := by
  unfold pairConstructor
  rw [AbsentFamilies.pairFamily_natural]
  simp only [Category.assoc, comparison_inl_assoc,
    ← (constantFamilyFunctor P).map_comp]

@[simp, reassoc] theorem pairConstructor_inr {T Z U Y : D}
    (f g : A ⟶ (constantFamily P T,constantFamily P Z))
    (p q : SyntaxPolynomial D) (h : (SyntaxPolynomial.sum p q).eval.obj (T,Z) ⟶ U) (embed : U ⟶ Y) :
    (coprod.inr : family A q ⟶ family A (.sum p q)) ≫
        pairConstructor A f g (.sum p q) h embed =
      pairConstructor A f g q (coprod.inr ≫ h) embed := by
  unfold pairConstructor
  rw [AbsentFamilies.pairFamily_natural]
  simp only [Category.assoc, comparison_inr_assoc,
    ← (constantFamilyFunctor P).map_comp]

/-- Computing and then pairing the original/result projections is exactly
pairing the two polynomial constructor applications in parameter families. -/
theorem paired_step {B C : D × D} {U Y : D}
    (m : A ⟶ (constantFamily P B.1,constantFamily P B.2))
    (original result : B ⟶ C) (p : SyntaxPolynomial D)
    (h : p.eval.obj C ⟶ U) (embed : U ⟶ Y) :
    (p.withParameters P).eval.map m ≫ SyntaxPolynomial.parameterComparison P B p ≫
      (constantFamilyFunctor P).map
        (prod.lift (p.eval.map original ≫ h) (p.eval.map result ≫ h ≫ embed)) =
    pairConstructor A
      (m ≫ ((constantFamilyFunctor P).map original.1,
        (constantFamilyFunctor P).map original.2))
      (m ≫ ((constantFamilyFunctor P).map result.1,
        (constantFamilyFunctor P).map result.2)) p h embed := by
  apply AbsentFamilies.product_hom_ext
  · unfold pairConstructor
    rw [AbsentFamilies.pairFamily_original, comparison_comp]
    simp only [Category.assoc, ← (constantFamilyFunctor P).map_comp, prod.lift_fst]
  · unfold pairConstructor
    rw [AbsentFamilies.pairFamily_result, comparison_comp]
    simp only [Category.assoc, ← (constantFamilyFunctor P).map_comp, prod.lift_snd]

variable {V T Z U Y : D} (L : StableListAlgebra V) (E : DecidableVariables V)
variable (name : P ⟶ V) (FVargs : (T,Z) ⟶ (L.algebra.carrier,L.algebra.carrier))
variable (FVout : U ⟶ L.algebra.carrier) (embed : U ⟶ Y)
variable (f g : A ⟶ (constantFamily P T,constantFamily P Z))
variable (good : ∀ {X : D} (k : X ⟶ A.1.left),
  prod.lift (k ≫ A.1.hom ≫ name) (k ≫ f.1.left ≫ prod.snd ≫ FVargs.1) ≫ L.membership E =
    Two.constant X false → k ≫ g.1.left ≫ prod.snd = k ≫ f.1.left ≫ prod.snd)

include good in
theorem arity_invariant (K : D) (n : ℕ)
    (h : (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)).eval.obj (T,Z) ⟶ U)
    (hFV : h ≫ FVout =
      (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)).eval.map FVargs ≫
        prod.snd ≫ L.tupleAppend n) :
    pairConstructor A f g (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)) h embed ≫
        AbsentFamilies.mask L E name FVout embed =
      pairConstructor A f g (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)) h embed ≫
        AbsentFamilies.result := by
  apply AbsentFamilies.equation_of_fixed L E name FVout embed
  intro X k hk
  let kt := k ≫ (prod.snd : constantFamily P K ⨯ AbsentTuples.family A n ⟶
    AbsentTuples.family A n).left
  have hb : kt ≫ (AbsentTuples.family A n).hom ≫ name =
      k ≫ (family A (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n))).hom ≫ name := by
    have hp := Over.w (prod.snd : constantFamily P K ⨯ AbsentTuples.family A n ⟶
      AbsentTuples.family A n)
    simpa only [kt, family, AbsentTuples.family, SyntaxPolynomial.withParameters,
      SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor, CategoryTheory.Functor.const,
      Category.assoc] using congrArg (fun p => k ≫ p ≫ name) hp
  have hocc : k ≫ value A f (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)) ≫
      h ≫ FVout = kt ≫ AbsentTuples.tupleMap A (Z := L.algebra.carrier)
        (f.1.left ≫ prod.snd ≫ FVargs.1) n ≫ L.tupleAppend n := by
    rw [hFV, value_product, value_coefficient, value_power]
    change k ≫ prod.lift _ _ ≫ prod.map (𝟙 K)
      ((SyntaxPolynomial.power .term n).eval.map FVargs) ≫ prod.snd ≫ L.tupleAppend n = _
    simp only [prod.lift_map_assoc, prod.lift_snd_assoc, Category.assoc,
      AbsentTuples.tupleMap_natural, kt, family, AbsentTuples.family,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
      CategoryTheory.Functor.const]
  have habsent : prod.lift (kt ≫ (AbsentTuples.family A n).hom ≫ name)
      (kt ≫ AbsentTuples.tupleMap A (Z := L.algebra.carrier)
        (f.1.left ≫ prod.snd ≫ FVargs.1) n ≫ L.tupleAppend n) ≫ L.membership E =
          Two.constant X false := by
    rw [hb]
    simpa only [pairConstructor_original_assoc, Category.assoc, hocc] using hk
  have ht := AbsentTuples.tuple_absence (Z := Z) A L E name FVargs.1
    (f.1.left ≫ prod.snd) (g.1.left ≫ prod.snd)
    (fun k hk => by
      simpa only [Category.assoc] using good k (by simpa only [Category.assoc] using hk))
    n kt (by simpa only [Category.assoc] using habsent)
  have hargs : k ≫ value A g (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)) =
      k ≫ value A f (SyntaxPolynomial.product (.coefficient K) (SyntaxPolynomial.power .term n)) := by
    rw [value_product, value_product, value_coefficient, value_coefficient,
      value_power, value_power, prod.comp_lift, prod.comp_lift]
    change (prod.lift _ _ : X ⟶ K ⨯ AbsentTuples.value T Z n) = prod.lift _ _
    simpa only [kt, family, AbsentTuples.family, AbsentTuples.value,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval, SyntaxPolynomial.productFunctor,
      CategoryTheory.Functor.const, Category.assoc] using congrArg
      (fun t => prod.lift
        (k ≫ (prod.fst : constantFamily P K ⨯ AbsentTuples.family A n ⟶
          constantFamily P K).left ≫ prod.snd) t) ht
  simpa only [pairConstructor_original_assoc, pairConstructor_result, Category.assoc] using
    congrArg (fun v => v ≫ h ≫ embed) hargs

include good in
theorem constructors_invariant (σ : ℕ → D) (n : ℕ)
    (h : (SyntaxPolynomial.constructors σ n).eval.obj (T,Z) ⟶ U)
    (hFV : h ≫ FVout = (SyntaxPolynomial.constructors σ n).eval.map FVargs ≫
      L.constructorOccurrences σ n) :
    pairConstructor A f g (SyntaxPolynomial.constructors σ n) h embed ≫
        AbsentFamilies.mask L E name FVout embed =
      pairConstructor A f g (SyntaxPolynomial.constructors σ n) h embed ≫
        AbsentFamilies.result := by
  induction n with
  | zero =>
    exact arity_invariant A L E name FVargs FVout embed f g good (σ 0) 0 h hFV
  | succ n ih =>
    have hleft : (coprod.inl ≫ h) ≫ FVout =
        (SyntaxPolynomial.constructors σ n).eval.map FVargs ≫ L.constructorOccurrences σ n := by
      simpa [SyntaxPolynomial.constructors, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
        StableListAlgebra.constructorOccurrences, Category.assoc] using
          congrArg (fun t => coprod.inl ≫ t) hFV
    have hright : (coprod.inr ≫ h) ≫ FVout =
        (SyntaxPolynomial.product (.coefficient (σ (n+1))) (SyntaxPolynomial.power .term (n+1))).eval.map FVargs ≫
          prod.snd ≫ L.tupleAppend (n+1) := by
      simpa [SyntaxPolynomial.constructors, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
        StableListAlgebra.constructorOccurrences, Category.assoc] using
          congrArg (fun t => coprod.inr ≫ t) hFV
    apply coprod.hom_ext
    · simpa only [SyntaxPolynomial.constructors, pairConstructor_inl_assoc,
        Category.assoc] using ih (coprod.inl ≫ h) hleft
    · simpa only [SyntaxPolynomial.constructors, pairConstructor_inr_assoc,
        Category.assoc] using arity_invariant A L E name FVargs FVout embed f g good
          (σ (n+1)) (n+1) (coprod.inr ≫ h) hright

end CategoricalEssentialIncompleteness.V46.AbsentConstructors
