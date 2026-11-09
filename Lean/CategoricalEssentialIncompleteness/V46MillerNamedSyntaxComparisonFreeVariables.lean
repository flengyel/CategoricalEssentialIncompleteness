import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonNormalization
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransportDeletion
import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables

/-! # The concrete occurrence fold under the uniform named-word chart

The target occurrence algebra is the intrinsic one. Every list operation
comparison is supplied by its constructed parameter-fold proof, rather
than an extra hypothesis of this endpoint.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family)
local notation "F" => Syntax.predicateFunctor P
local notation "FP" => Functor.prod (Syntax.predicateFunctor P) (Syntax.predicateFunctor P)

private def imageSum {A B : PredicateCategory 𝗣𝗔} {X Y : Total.TotalCategory P}
    (a : (F).obj A ≅ X) (b : (F).obj B ≅ Y) : (F).obj (A ⨿ B) ≅ X ⨿ Y :=
  (asIso (coprodComparison (F) A B)).symm ≪≫ coprod.mapIso a b

private theorem imageSum_inl {A B : PredicateCategory 𝗣𝗔} {X Y : Total.TotalCategory P}
    (a : (F).obj A ≅ X) (b : (F).obj B ≅ Y) :
    (F).map (coprod.inl : A ⟶ A ⨿ B) ≫ (imageSum P a b).hom=a.hom ≫ coprod.inl := by
  simp only [imageSum,Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    ← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]

private theorem imageSum_inr {A B : PredicateCategory 𝗣𝗔} {X Y : Total.TotalCategory P}
    (a : (F).obj A ≅ X) (b : (F).obj B ≅ Y) :
    (F).map (coprod.inr : B ⟶ A ⨿ B) ≫ (imageSum P a b).hom=b.hom ≫ coprod.inr := by
  simp only [imageSum,Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
    ← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]

private theorem mapped_coprod_ext {A B : PredicateCategory 𝗣𝗔} {Z : Total.TotalCategory P}
    {f g : (F).obj (A ⨿ B) ⟶ Z}
    (h0 : (F).map coprod.inl ≫ f=(F).map coprod.inl ≫ g)
    (h1 : (F).map coprod.inr ≫ f=(F).map coprod.inr ≫ g) : f=g :=
  BinaryCofan.IsColimit.hom_ext
    (isColimitOfHasBinaryCoproductOfPreservesColimit (F) A B) h0 h1

private theorem image_copair {A B X : PredicateCategory 𝗣𝗔} {A' B' : Total.TotalCategory P}
    (a : (F).obj A ≅ A') (b : (F).obj B ≅ B')
    (f0 : A ⟶ X) (g0 : B ⟶ X) (f1 : A' ⟶ (F).obj X) (g1 : B' ⟶ (F).obj X)
    (hf : (F).map f0=a.hom ≫ f1) (hg : (F).map g0=b.hom ≫ g1) :
    (F).map (coprod.desc f0 g0)=(imageSum P a b).hom ≫ coprod.desc f1 g1 := by
  apply mapped_coprod_ext P
  · rw [← Functor.map_comp,coprod.inl_desc,hf,← Category.assoc,imageSum_inl,Category.assoc,coprod.inl_desc]
  · rw [← Functor.map_comp,coprod.inr_desc,hg,← Category.assoc,imageSum_inr,Category.assoc,coprod.inr_desc]

private theorem compared_copair {A B X : PredicateCategory 𝗣𝗔} {A' B' : Total.TotalCategory P}
    (h : (F).obj (A ⨿ B) ⟶ A' ⨿ B') (a : (F).obj A ⟶ A') (b : (F).obj B ⟶ B')
    (hin : (F).map (coprod.inl : A ⟶ A ⨿ B) ≫ h = a ≫ coprod.inl)
    (hir : (F).map (coprod.inr : B ⟶ A ⨿ B) ≫ h = b ≫ coprod.inr)
    (f0 : A ⟶ X) (g0 : B ⟶ X) (f1 : A' ⟶ (F).obj X) (g1 : B' ⟶ (F).obj X)
    (hf : (F).map f0 = a ≫ f1) (hg : (F).map g0 = b ≫ g1) :
    (F).map (coprod.desc f0 g0) = h ≫ coprod.desc f1 g1 := by
  apply mapped_coprod_ext P
  · calc
      _ = (F).map f0 := by rw [← (F).map_comp,coprod.inl_desc]
      _ = a ≫ f1 := hf
      _ = (a ≫ coprod.inl) ≫ coprod.desc f1 g1 := by rw [Category.assoc,coprod.inl_desc]
      _ = ((F).map coprod.inl ≫ h) ≫ coprod.desc f1 g1 :=
        congrArg (fun f => f ≫ coprod.desc f1 g1) hin.symm
      _ = _ := Category.assoc _ _ _
  · calc
      _ = (F).map g0 := by rw [← (F).map_comp,coprod.inr_desc]
      _ = b ≫ g1 := hg
      _ = (b ≫ coprod.inr) ≫ coprod.desc f1 g1 := by rw [Category.assoc,coprod.inr_desc]
      _ = ((F).map coprod.inr ≫ h) ≫ coprod.desc f1 g1 :=
        congrArg (fun f => f ≫ coprod.desc f1 g1) hir.symm
      _ = _ := Category.assoc _ _ _

private theorem normalized_coefficient (C : PredicateCategory 𝗣𝗔)
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    normalizedComponent P (.coefficient C) (.coefficient ((F).obj C)) rfl X = Iso.refl _ := by
  apply Iso.ext
  change (𝟙 ((F).obj C)) ≫ 𝟙 _ = 𝟙 _
  exact Category.comp_id _

private theorem normalized_term (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    normalizedComponent P .term .term rfl X = Iso.refl _ := by
  apply Iso.ext
  change (𝟙 ((F).obj X.1)) ≫ 𝟙 _ = 𝟙 _
  exact Category.comp_id _

private theorem normalized_formula (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    normalizedComponent P .formula .formula rfl X = Iso.refl _ := by
  apply Iso.ext
  change (𝟙 ((F).obj X.2)) ≫ 𝟙 _ = 𝟙 _
  exact Category.comp_id _

private theorem product_reflexive {D : Type*} [Category D] (X Y : D) [HasBinaryProduct X Y] :
    prod.mapIso (Iso.refl X) (Iso.refl Y) = Iso.refl (X ⨯ Y) := by
  apply Iso.ext
  simp only [prod.mapIso_hom,Iso.refl_hom,prod.map_id_id]

private def algebraIso_from_diagram {C : Type*} [Category C] (G : C ⥤ C)
    (A B : Endofunctor.Algebra G) (i : A.a ≅ B.a) {X : C} (j : X ≅ G.obj B.a)
    (h : j.hom ≫ G.map i.inv ≫ A.str ≫ i.hom = j.hom ≫ B.str) : A ≅ B := by
  refine Endofunctor.Algebra.isoMk i ?_
  apply (cancel_epi (j.hom ≫ G.map i.inv)).mp
  calc
    _ = j.hom ≫ (G.map i.inv ≫ G.map i.hom) ≫ B.str := by simp only [Category.assoc]
    _ = j.hom ≫ G.map (i.inv ≫ i.hom) ≫ B.str := by rw [G.map_comp]
    _ = j.hom ≫ B.str := by rw [i.inv_hom_id,G.map_id,Category.id_comp]
    _ = _ := by simpa only [Category.assoc] using h.symm

private def normalizedAlgebraIso
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p q : SyntaxPolynomial (Total.TotalCategory P))
    (hp : Syntax.Polynomial.mapped P a = p) (hq : Syntax.Polynomial.mapped P b = q)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (s : (SyntaxPolynomial.jointFunctor p q).obj ((FP).obj A.a) ⟶ (FP).obj A.a)
    (hs : (FP).map A.str = (normalizedJointIso P a b p q hp hq).hom.app A.a ≫ s) :
    castAlgebra hp hq (Syntax.Polynomial.mappedAlgebra P a b A) ≅
      (⟨(FP).obj A.a, s⟩ : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) := by
  cases hp
  cases hq
  refine Endofunctor.Algebra.isoMk (Iso.refl _) ?_
  change (SyntaxPolynomial.jointFunctor (Syntax.Polynomial.mapped P a)
    (Syntax.Polynomial.mapped P b)).map (𝟙 ((FP).obj A.a)) ≫ s =
      (Syntax.Polynomial.mappedAlgebra P a b A).str ≫ 𝟙 _
  erw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]
  apply (cancel_epi ((Syntax.Polynomial.jointIso P a b).hom.app A.a)).mp
  have h : (FP).map A.str = (Syntax.Polynomial.jointIso P a b).hom.app A.a ≫ s := by
    simpa only [normalizedJointIso,eqToIso_refl,Iso.trans_refl] using hs
  exact h.symm.trans (mapped_structure P a b A).symm

private theorem normalizedAlgebraIso_hom
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p q : SyntaxPolynomial (Total.TotalCategory P))
    (hp : Syntax.Polynomial.mapped P a = p) (hq : Syntax.Polynomial.mapped P b = q)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (s : (SyntaxPolynomial.jointFunctor p q).obj ((FP).obj A.a) ⟶ (FP).obj A.a)
    (hs : (FP).map A.str = (normalizedJointIso P a b p q hp hq).hom.app A.a ≫ s) :
    (normalizedAlgebraIso P a b p q hp hq A s hs).hom.f =
      eqToHom (castAlgebra_carrier hp hq (Syntax.Polynomial.mappedAlgebra P a b A)) := by
  cases hp
  cases hq
  rfl

private theorem algebra_eqToIso_hom_f {C : Type*} [Category C] {G : C ⥤ C}
    {A B : Endofunctor.Algebra G} (h : A = B) :
    (eqToIso h).hom.f = eqToHom (congrArg (fun K : Endofunctor.Algebra G => K.a) h) := by
  cases h
  rfl

private theorem normalizedFold_comparison
    (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p q : SyntaxPolynomial (Total.TotalCategory P))
    (hp : Syntax.Polynomial.mapped P a = p) (hq : Syntax.Polynomial.mapped P b = q)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (hA : IsInitial A) (hB : IsInitial B)
    (j : B ≅ castAlgebra hp hq (Syntax.Polynomial.mappedAlgebra P a b A))
    (R : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b))
    (s : (SyntaxPolynomial.jointFunctor p q).obj ((FP).obj R.a) ⟶ (FP).obj R.a)
    (hs : (FP).map R.str = (normalizedJointIso P a b p q hp hq).hom.app R.a ≫ s) :
    (castedCarrierIso P a b p q hp hq A B j).hom ≫ (FP).map (hA.to R).f =
      (hB.to (⟨(FP).obj R.a,s⟩ : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))).f := by
  let R' : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q) := ⟨(FP).obj R.a,s⟩
  let m : B ⟶ R' := j.hom ≫ castHom P hp hq (mappedHom P a b (hA.to R)) ≫
    (normalizedAlgebraIso P a b p q hp hq R s hs).hom
  have he := congrArg Endofunctor.Algebra.Hom.f (hB.hom_ext m (hB.to R'))
  change j.hom.f ≫ (castHom P hp hq (mappedHom P a b (hA.to R))).f ≫
    (normalizedAlgebraIso P a b p q hp hq R s hs).hom.f = _ at he
  erw [normalizedAlgebraIso_hom] at he
  erw [castHom_carrier] at he
  change j.hom.f ≫ eqToHom (castAlgebra_carrier hp hq
    (Syntax.Polynomial.mappedAlgebra P a b A)) ≫ (FP).map (hA.to R).f = _ at he
  change (j.hom.f ≫ eqToHom (castAlgebra_carrier hp hq
    (Syntax.Polynomial.mappedAlgebra P a b A))) ≫ (FP).map (hA.to R).f = _
  exact (Category.assoc _ _ _).trans he

variable (V : PredicateCategory 𝗣𝗔)
local notation "L₀" => SyntacticLists.stableListAlgebra 𝗣𝗔 V
local notation "L₁" => mappedListStable P V

private theorem nil_image : (F).map (L₀).algebra.nil=terminalComparison (F) ≫ (L₁).algebra.nil :=
  ListTransport.map_nil P V

theorem tupleAppend_image (n : ℕ) : (F).map ((L₀).tupleAppend n)=
    (powerComponent P (L₀).algebra.carrier n).hom ≫ (L₁).tupleAppend n := by
  induction n with
  | zero => simpa only [StableListAlgebra.tupleAppend,powerComponent_zero] using nil_image P V
  | succ n ih =>
    cases n with
    | zero =>
      change (F).map (𝟙 (L₀).algebra.carrier) =
        (powerComponent P (L₀).algebra.carrier 1).hom ≫ 𝟙 (L₁).algebra.carrier
      erw [powerComponent_one,Category.id_comp]
      exact (F).map_id (L₀).algebra.carrier
    | succ n =>
      change (F).map (prod.map ((L₀).tupleAppend (n+1)) (𝟙 _) ≫ (L₀).append)=_
      rw [Functor.map_comp,ListTransport.map_append,← Category.assoc,prodComparison_natural]
      let X : PredicateCategory 𝗣𝗔 :=
        (SyntaxPolynomial.power .term (n+1)).eval.obj ((L₀).algebra.carrier,(L₀).algebra.carrier)
      have hi := congrArg
        (fun f => prodComparison (F) X (L₀).algebra.carrier ≫
          prod.map ((F).map ((L₀).tupleAppend (n+1))) f ≫ (L₁).append)
        ((F).map_id (L₀).algebra.carrier)
      refine (Category.assoc _ _ _).trans (hi.trans ?_)
      rw [ih,powerComponent_succ]
      refine Eq.trans ?_ (Category.assoc
        (prodComparison (F) X (L₀).algebra.carrier)
        (prod.map (powerComponent P (L₀).algebra.carrier (n+1)).hom
          (𝟙 ((F).obj (L₀).algebra.carrier))) ((L₁).tupleAppend (n+1+1))).symm
      change _ = prodComparison (F)
        ((SyntaxPolynomial.power .term (n+1)).eval.obj ((L₀).algebra.carrier,(L₀).algebra.carrier))
        (L₀).algebra.carrier ≫
        prod.map (powerComponent P (L₀).algebra.carrier (n+1)).hom (𝟙 ((F).obj (L₀).algebra.carrier)) ≫
        prod.map ((L₁).tupleAppend (n+1)) (𝟙 ((F).obj (L₀).algebra.carrier)) ≫ (L₁).append
      simp only [prod.map_map_assoc,Category.id_comp]
      rfl

private theorem symbolOccurrences_image (C : PredicateCategory 𝗣𝗔) (n : ℕ) :
    (F).map ((prod.snd : C ⨯ (SyntaxPolynomial.power .term n).eval.obj
      ((L₀).algebra.carrier,(L₀).algebra.carrier) ⟶ _) ≫ (L₀).tupleAppend n)=
      (symbolComponent P C (L₀).algebra.carrier n).hom ≫ prod.snd ≫ (L₁).tupleAppend n := by
  rw [Functor.map_comp,tupleAppend_image]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (L₁).tupleAppend n)
      (symbolComponent_snd P C (L₀).algebra.carrier n).symm).trans (Category.assoc _ _ _))

theorem constructorOccurrences_image (σ : ℕ → PredicateCategory 𝗣𝗔) (n : ℕ) :
    (F).map ((L₀).constructorOccurrences σ n)=
      (constructorComponent P σ (L₀).algebra.carrier n).hom ≫
        (L₁).constructorOccurrences (fun i => (F).obj (σ i)) n := by
  induction n with
  | zero =>
    change (F).map ((prod.snd : σ 0 ⨯ _ ⟶ _) ≫ (L₀).tupleAppend 0) =
      (symbolComponent P (σ 0) (L₀).algebra.carrier 0).hom ≫ prod.snd ≫ (L₁).tupleAppend 0
    exact symbolOccurrences_image P V (σ 0) 0
  | succ n ih =>
    change (F).map (coprod.desc ((L₀).constructorOccurrences σ n)
      ((prod.snd : σ (n+1) ⨯ _ ⟶ _) ≫ (L₀).tupleAppend (n+1))) =
      (constructorComponent P σ (L₀).algebra.carrier (n+1)).hom ≫
        coprod.desc ((L₁).constructorOccurrences (fun i => (F).obj (σ i)) n)
          ((prod.snd : (F).obj (σ (n+1)) ⨯ _ ⟶ _) ≫ (L₁).tupleAppend (n+1))
    exact compared_copair P
      (A := (SyntaxPolynomial.constructors σ n).eval.obj ((L₀).algebra.carrier,(L₀).algebra.carrier))
      (B := σ (n+1) ⨯ (SyntaxPolynomial.power .term (n+1)).eval.obj
        ((L₀).algebra.carrier,(L₀).algebra.carrier)) (X := (L₀).algebra.carrier)
      (A' := (SyntaxPolynomial.constructors (fun i => (F).obj (σ i)) n).eval.obj
        ((FP).obj ((L₀).algebra.carrier,(L₀).algebra.carrier)))
      (B' := (F).obj (σ (n+1)) ⨯ (SyntaxPolynomial.power .term (n+1)).eval.obj
        ((FP).obj ((L₀).algebra.carrier,(L₀).algebra.carrier)))
      (constructorComponent P σ (L₀).algebra.carrier (n+1)).hom
      (constructorComponent P σ (L₀).algebra.carrier n).hom
      (symbolComponent P (σ (n+1)) (L₀).algebra.carrier (n+1)).hom
      (constructorComponent_inl P σ (L₀).algebra.carrier n)
      (constructorComponent_inr P σ (L₀).algebra.carrier n)
      _ _ _ _ ih (symbolOccurrences_image P V (σ (n+1)) (n+1))

variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "S₀" => sourceSyntax V σ π d
local notation "S₁" => presentedSyntax P V σ π d
local notation "a" => SyntaxPolynomial.termExpression V σ d
local notation "b" => SyntaxPolynomial.formulaExpression V π d
local notation "p" => SyntaxPolynomial.termExpression (Functor.obj (Syntax.predicateFunctor P) V) (fun i => Functor.obj (Syntax.predicateFunctor P) (σ i)) d
local notation "q" => SyntaxPolynomial.formulaExpression (Functor.obj (Syntax.predicateFunctor P) V) (fun i => Functor.obj (Syntax.predicateFunctor P) (π i)) d

/-- The occurrence algebra uses only the independently constructed
mapped lists and mapped variable equality, with an explicit carrier. -/
def explicitOccurrenceAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q) where
  «a» := ((F).obj (L₀).algebra.carrier, (F).obj (L₀).algebra.carrier)
  str :=
    (coprod.desc (L₁).singleton ((L₁).constructorOccurrences (fun n => (F).obj (σ n)) d),
      coprod.desc
        (coprod.desc
          (coprod.desc (coprod.desc (L₁).append
            ((L₁).constructorOccurrences (fun n => (F).obj (π n)) d))
            (𝟙 ((F).obj (L₀).algebra.carrier)))
          (L₁).append)
        ((L₁).deletion (Derivation.mappedEquality (F)
          (SyntacticDecidableVariables.decidableVariables 𝗣𝗔 V))))

/-- Both actual constructors, the lists, and the variable classifier agree
with the chosen syntax record. No initiality comparison is assumed. -/
theorem explicitOccurrenceAlgebra_eq :
    explicitOccurrenceAlgebra P V σ π d = (S₁).occurrenceAlgebra := by
  rfl

private theorem termOccurrence_component :
    (normalizedComponent P a p (termExpression_mapped P V σ d)
      ((L₀).algebra.carrier,(L₀).algebra.carrier)).hom=
      (imageSum P (Iso.refl ((F).obj V)) (constructorComponent P σ (L₀).algebra.carrier d)).hom := by
  erw [normalizedComponent_sum P (.coefficient V) (SyntaxPolynomial.constructors σ d)
    (.coefficient ((F).obj V)) (SyntaxPolynomial.constructors (fun i => (F).obj (σ i)) d)
    rfl (SyntaxOperationsTransport.mapCoefficients_constructors (F).obj σ d)
    ((L₀).algebra.carrier,(L₀).algebra.carrier)]
  simp only [normalized_coefficient,imageSum,constructorComponent,SyntaxPolynomial.eval,Functor.const_obj_obj]

private theorem formulaOccurrence_component :
    (normalizedComponent P b q (formulaExpression_mapped P V π d)
      ((L₀).algebra.carrier,(L₀).algebra.carrier)).hom=
      (imageSum P
        (imageSum P
          (imageSum P
            (imageSum P (asIso (prodComparison (F) (L₀).algebra.carrier (L₀).algebra.carrier))
              (constructorComponent P π (L₀).algebra.carrier d)) (Iso.refl _))
          (asIso (prodComparison (F) (L₀).algebra.carrier (L₀).algebra.carrier)))
        (asIso (prodComparison (F) V (L₀).algebra.carrier))).hom := by
  let X := ((L₀).algebra.carrier,(L₀).algebra.carrier)
  let T : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.power .term 2
  let T' : SyntaxPolynomial (Total.TotalCategory P) := SyntaxPolynomial.power .term 2
  let C : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.constructors π d
  let C' : SyntaxPolynomial (Total.TotalCategory P) := SyntaxPolynomial.constructors (fun i => (F).obj (π i)) d
  let W : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.power .formula 2
  let W' : SyntaxPolynomial (Total.TotalCategory P) := SyntaxPolynomial.power .formula 2
  have ht : Syntax.Polynomial.mapped P T = T' := SyntaxOperationsTransport.mapCoefficients_power (F).obj .term 2
  have hc : Syntax.Polynomial.mapped P C = C' := SyntaxOperationsTransport.mapCoefficients_constructors (F).obj π d
  have hw : Syntax.Polynomial.mapped P W = W' := SyntaxOperationsTransport.mapCoefficients_power (F).obj .formula 2
  have hf : Syntax.Polynomial.mapped P .formula = .formula := rfl
  have hv : Syntax.Polynomial.mapped P (.coefficient V) = .coefficient ((F).obj V) := rfl
  have hs₀ := congrArg₂ SyntaxPolynomial.sum ht hc
  have hs₁ := congrArg₂ SyntaxPolynomial.sum hs₀ hf
  have hs₂ := congrArg₂ SyntaxPolynomial.sum hs₁ hw
  have hp := congrArg₂ SyntaxPolynomial.product hv hf
  erw [normalizedComponent_sum P (.sum (.sum (.sum T C) .formula) W)
    (.product (.coefficient V) .formula) (.sum (.sum (.sum T' C') .formula) W')
    (.product (.coefficient ((F).obj V)) .formula) hs₂ hp X,
    normalizedComponent_sum P (.sum (.sum T C) .formula) W (.sum (.sum T' C') .formula) W' hs₁ hw X,
    normalizedComponent_sum P (.sum T C) .formula (.sum T' C') .formula hs₀ hf X,
    normalizedComponent_sum P T C T' C' ht hc X,
    normalizedComponent_product P .term .term .term .term rfl rfl X,
    normalizedComponent_product P (.coefficient V) .formula (.coefficient ((F).obj V)) .formula hv hf X]
  simp only [normalized_term,normalized_formula,normalized_coefficient,
    product_reflexive,Iso.trans_refl,imageSum,constructorComponent]
  dsimp only [T,T',W,W',C,C',X,SyntaxPolynomial.power,SyntaxPolynomial.eval,
    SyntaxPolynomial.productFunctor,SyntaxPolynomial.sumFunctor,
    CategoryTheory.Prod.fst,CategoryTheory.Prod.snd,Functor.const_obj_obj]

private theorem termOccurrence_explicit_structure :
    (F).map (S₀).occurrenceAlgebra.str.1=
      (normalizedComponent P a p (termExpression_mapped P V σ d) (S₀).occurrenceAlgebra.a).hom ≫
        (explicitOccurrenceAlgebra P V σ π d).str.1 := by
  erw [termOccurrence_component]
  change (F).map (coprod.desc (L₀).singleton ((L₀).constructorOccurrences σ d))=_
  apply image_copair P
  · change (F).map (L₀).singleton = (𝟙 _) ≫ (L₁).singleton
    exact (ListTransport.map_singleton P V).trans (Category.id_comp _).symm
  · exact constructorOccurrences_image P V σ d

private theorem formulaOccurrence_explicit_structure :
    (F).map (S₀).occurrenceAlgebra.str.2=
      (normalizedComponent P b q (formulaExpression_mapped P V π d) (S₀).occurrenceAlgebra.a).hom ≫
        (explicitOccurrenceAlgebra P V σ π d).str.2 := by
  erw [formulaOccurrence_component]
  change (F).map (coprod.desc (coprod.desc (coprod.desc
    (coprod.desc (L₀).append ((L₀).constructorOccurrences π d)) (𝟙 _)) (L₀).append)
      ((L₀).deletion (S₀).decidableVariables))=_
  apply image_copair P
  · apply image_copair P
    · apply image_copair P
      · apply image_copair P
        · exact ListTransport.map_append P V
        · exact constructorOccurrences_image P V π d
      · change (F).map (𝟙 (L₀).algebra.carrier) = (𝟙 ((F).obj (L₀).algebra.carrier)) ≫ 𝟙 _
        exact ((F).map_id (L₀).algebra.carrier).trans (Category.id_comp _).symm
    · exact ListTransport.map_append P V
  · exact ListTransport.map_deletion P V (S₀).decidableVariables
theorem termOccurrence_structure :
    (F).map (S₀).occurrenceAlgebra.str.1=
      (normalizedComponent P a p (termExpression_mapped P V σ d) (S₀).occurrenceAlgebra.a).hom ≫
        (S₁).occurrenceAlgebra.str.1 := by
  exact termOccurrence_explicit_structure P V σ π d

theorem formulaOccurrence_structure :
    (F).map (S₀).occurrenceAlgebra.str.2=
      (normalizedComponent P b q (formulaExpression_mapped P V π d) (S₀).occurrenceAlgebra.a).hom ≫
        (S₁).occurrenceAlgebra.str.2 := by
  exact formulaOccurrence_explicit_structure P V σ π d

private theorem explicit_occurrence_structure_comparison : (FP).map (S₀).occurrenceAlgebra.str =
      (normalizedJointIso P a b p q (termExpression_mapped P V σ d)
        (formulaExpression_mapped P V π d)).hom.app (S₀).occurrenceAlgebra.a ≫
          (explicitOccurrenceAlgebra P V σ π d).str := by
  apply Prod.ext
  · change (F).map (S₀).occurrenceAlgebra.str.1 = _
    exact (termOccurrence_explicit_structure P V σ π d).trans
      (congrArg (fun f => f ≫ (explicitOccurrenceAlgebra P V σ π d).str.1)
        (normalizedJointIso_first P a b p q (termExpression_mapped P V σ d)
          (formulaExpression_mapped P V π d) (S₀).occurrenceAlgebra.a).symm)
  · change (F).map (S₀).occurrenceAlgebra.str.2 = _
    exact (formulaOccurrence_explicit_structure P V σ π d).trans
      (congrArg (fun f => f ≫ (explicitOccurrenceAlgebra P V σ π d).str.2)
        (normalizedJointIso_second P a b p q (termExpression_mapped P V σ d)
          (formulaExpression_mapped P V π d) (S₀).occurrenceAlgebra.a).symm)

def explicitOccurrenceAlgebraIso :
    castAlgebra (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)
      (Syntax.Polynomial.mappedAlgebra P a b (S₀).occurrenceAlgebra) ≅ (explicitOccurrenceAlgebra P V σ π d) :=
  normalizedAlgebraIso P a b p q (termExpression_mapped P V σ d)
    (formulaExpression_mapped P V π d) (S₀).occurrenceAlgebra
    (explicitOccurrenceAlgebra P V σ π d).str
    (explicit_occurrence_structure_comparison P V σ π d)

private theorem explicitOccurrenceAlgebraIso_hom :
    (explicitOccurrenceAlgebraIso P V σ π d).hom.f =
      eqToHom (castAlgebra_carrier (termExpression_mapped P V σ d)
        (formulaExpression_mapped P V π d)
        (Syntax.Polynomial.mappedAlgebra P a b (S₀).occurrenceAlgebra)) := by
  exact normalizedAlgebraIso_hom P a b p q (termExpression_mapped P V σ d)
    (formulaExpression_mapped P V π d) (S₀).occurrenceAlgebra
    (explicitOccurrenceAlgebra P V σ π d).str
    (explicit_occurrence_structure_comparison P V σ π d)

/-- Restore the actual target algebra through the proved record equality. -/
def occurrenceAlgebraIso :
    castAlgebra (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)
      (Syntax.Polynomial.mappedAlgebra P a b (S₀).occurrenceAlgebra) ≅ (S₁).occurrenceAlgebra :=
  explicitOccurrenceAlgebraIso P V σ π d

theorem occurrenceAlgebraIso_hom :
    (occurrenceAlgebraIso P V σ π d).hom.f =
      eqToHom (castAlgebra_carrier (termExpression_mapped P V σ d)
        (formulaExpression_mapped P V π d)
        (Syntax.Polynomial.mappedAlgebra P a b (S₀).occurrenceAlgebra)) := by
  exact explicitOccurrenceAlgebraIso_hom P V σ π d

def sourcePairIso : (S₁).algebra.a ≅ (FP).obj (S₀).algebra.a :=
  ((Endofunctor.Algebra.forget _).mapIso (sourceAlgebraIso P V σ π d)) ≪≫
    eqToIso (castAlgebra_carrier _ _ (Syntax.Polynomial.mappedAlgebra P a b (S₀).algebra))

theorem sourcePairIso_eq_normalized : sourcePairIso P V σ π d=
    normalizedWordPairIso P a b p q (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d) :=
  normalizedWordAlgebraIso_carrier P a b p q (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)

theorem sourcePairIso_term_graph (word output : ℕ) :
    output∈Total.val ((sourcePairIso P V σ π d).hom.1).hom word ↔
      word∈(Syntax.Raw.uniformWords false p q).support ∧ output=word := by
  rw [sourcePairIso_eq_normalized]
  exact normalizedWordPairIso_term_graph P a b p q _ _ word output

theorem sourcePairIso_formula_graph (word output : ℕ) :
    output∈Total.val ((sourcePairIso P V σ π d).hom.2).hom word ↔
      word∈(Syntax.Raw.uniformWords true p q).support ∧ output=word := by
  rw [sourcePairIso_eq_normalized]
  exact normalizedWordPairIso_formula_graph P a b p q _ _ word output

def termIso : (S₁).algebra.a.1 ≅ (F).obj (S₀).algebra.a.1 where
  hom := (sourcePairIso P V σ π d).hom.1
  inv := (sourcePairIso P V σ π d).inv.1
  hom_inv_id := congrArg Prod.fst (sourcePairIso P V σ π d).hom_inv_id
  inv_hom_id := congrArg Prod.fst (sourcePairIso P V σ π d).inv_hom_id

def formulaIso : (S₁).algebra.a.2 ≅ (F).obj (S₀).algebra.a.2 where
  hom := (sourcePairIso P V σ π d).hom.2
  inv := (sourcePairIso P V σ π d).inv.2
  hom_inv_id := congrArg Prod.snd (sourcePairIso P V σ π d).hom_inv_id
  inv_hom_id := congrArg Prod.snd (sourcePairIso P V σ π d).inv_hom_id

theorem occurrence_fold_comparison :
    (sourcePairIso P V σ π d).hom ≫ (FP).map ((S₀).fold (S₀).occurrenceAlgebra)=
      (S₁).fold (S₁).occurrenceAlgebra := by
  exact normalizedFold_comparison P a b p q (termExpression_mapped P V σ d)
    (formulaExpression_mapped P V π d) (S₀).algebra (S₁).algebra (S₀).initial (S₁).initial
    (sourceAlgebraIso P V σ π d) (S₀).occurrenceAlgebra
    (explicitOccurrenceAlgebra P V σ π d).str
    (explicit_occurrence_structure_comparison P V σ π d)

theorem termOccurrences_comparison :
    (sourcePairIso P V σ π d).hom.1 ≫ (F).map (S₀).termOccurrences=(S₁).termOccurrences :=
  congrArg Prod.fst (occurrence_fold_comparison P V σ π d)

theorem formulaOccurrences_comparison :
    (sourcePairIso P V σ π d).hom.2 ≫ (F).map (S₀).formulaOccurrences=(S₁).formulaOccurrences :=
  congrArg Prod.snd (occurrence_fold_comparison P V σ π d)

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
