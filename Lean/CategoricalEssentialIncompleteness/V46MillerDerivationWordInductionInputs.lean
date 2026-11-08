import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionCharts

/-! # Ordered branch charts for actual uniform inference inputs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
open SyntacticDerivation SyntacticSyntax
variable {P : Uniform.Family}
local notation "U" => (Total.underlying (P := P))

theorem rawProduct_inverse_fst (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (z : (U).obj ((SyntaxPolynomial.product a b).eval.obj (X,Y))) :
    (Nat.unpair ((U).map (Syntax.Raw.baseComparison X Y (.product a b)).inv z).val).1=
      ((U).map (Syntax.Raw.baseComparison X Y a).inv ((U).map prod.fst z)).val := by
  let u := (U).map (Syntax.Raw.baseComparison X Y (.product a b)).inv z
  have h := rawProduct_fst X Y a b u
  have he : (U).map (Syntax.Raw.baseComparison X Y (.product a b)).hom u=z := by
    dsimp only [u]
    erw [← CategoryTheory.Functor.map_comp_apply,Iso.inv_hom_id,CategoryTheory.Functor.map_id_apply]
  erw [he] at h
  have hh := congrArg (fun q => ((U).map (Syntax.Raw.baseComparison X Y a).inv q).val) h
  have hi : (U).map (Syntax.Raw.baseComparison X Y a).inv
      ((U).map (Syntax.Raw.baseComparison X Y a).hom
        ⟨(Nat.unpair u.val).1,u.property.1⟩)=⟨(Nat.unpair u.val).1,u.property.1⟩ := by
    erw [← CategoryTheory.Functor.map_comp_apply,Iso.hom_inv_id,CategoryTheory.Functor.map_id_apply]
  exact (congrArg Subtype.val hi).symm.trans hh.symm

theorem rawProduct_inverse_snd (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (z : (U).obj ((SyntaxPolynomial.product a b).eval.obj (X,Y))) :
    (Nat.unpair ((U).map (Syntax.Raw.baseComparison X Y (.product a b)).inv z).val).2=
      ((U).map (Syntax.Raw.baseComparison X Y b).inv ((U).map prod.snd z)).val := by
  let u := (U).map (Syntax.Raw.baseComparison X Y (.product a b)).inv z
  have h := rawProduct_snd X Y a b u
  have he : (U).map (Syntax.Raw.baseComparison X Y (.product a b)).hom u=z := by
    dsimp only [u]
    erw [← CategoryTheory.Functor.map_comp_apply,Iso.inv_hom_id,CategoryTheory.Functor.map_id_apply]
  erw [he] at h
  have hh := congrArg (fun q => ((U).map (Syntax.Raw.baseComparison X Y b).inv q).val) h
  have hi : (U).map (Syntax.Raw.baseComparison X Y b).inv
      ((U).map (Syntax.Raw.baseComparison X Y b).hom
        ⟨(Nat.unpair u.val).2,u.property.2⟩)=⟨(Nat.unpair u.val).2,u.property.2⟩ := by
    erw [← CategoryTheory.Functor.map_comp_apply,Iso.hom_inv_id,CategoryTheory.Functor.map_id_apply]
  exact (congrArg Subtype.val hi).symm.trans hh.symm

theorem rawProduct_inverse_value (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (z : (U).obj ((SyntaxPolynomial.product a b).eval.obj (X,Y))) :
    ((U).map (Syntax.Raw.baseComparison X Y (.product a b)).inv z).val=
      Nat.pair (((U).map (Syntax.Raw.baseComparison X Y a).inv ((U).map prod.fst z)).val)
        (((U).map (Syntax.Raw.baseComparison X Y b).inv ((U).map prod.snd z)).val) := by
  rw [← rawProduct_inverse_fst,← rawProduct_inverse_snd,Nat.pair_unpair]

theorem rawSum_inverse_inl (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (z : (U).obj (a.eval.obj (X,Y))) :
    ((U).map (Syntax.Raw.baseComparison X Y (.sum a b)).inv ((U).map coprod.inl z)).val=
      Nat.pair (((U).map (Syntax.Raw.baseComparison X Y a).inv z).val) 0 := by
  erw [← CategoryTheory.Functor.map_comp_apply,Syntax.Raw.baseComparison_sum_inv_inl,CategoryTheory.Functor.map_comp_apply]
  exact Part.mem_unique (Total.totalFunction_mem _ _)
    ((Total.mem_totalFromFunction (fun n => Nat.pair n 0)
      (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
      (Syntax.Raw.taggedInl_supported (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)) _ _).mpr
        ⟨((U).map (Syntax.Raw.baseComparison X Y a).inv z).property,rfl⟩)

theorem rawSum_inverse_inr (X Y : Total.TotalCategory P) (a b : SyntaxPolynomial (Total.TotalCategory P))
    (z : (U).obj (b.eval.obj (X,Y))) :
    ((U).map (Syntax.Raw.baseComparison X Y (.sum a b)).inv ((U).map coprod.inr z)).val=
      Nat.pair (((U).map (Syntax.Raw.baseComparison X Y b).inv z).val) 1 := by
  erw [← CategoryTheory.Functor.map_comp_apply,Syntax.Raw.baseComparison_sum_inv_inr,CategoryTheory.Functor.map_comp_apply]
  exact Part.mem_unique (Total.totalFunction_mem _ _)
    ((Total.mem_totalFromFunction (fun n => Nat.pair n 1)
      (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
      (Syntax.Raw.taggedInr_supported (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)) _ _).mpr
        ⟨((U).map (Syntax.Raw.baseComparison X Y b).inv z).property,rfl⟩)

theorem summand_inverse_value (labels : ℕ → Total.TotalCategory P) (X : Total.TotalCategory P) (n : ℕ)
    (p : (U).obj (labels n ⨯ finitePower X n)) :
    ((U).map (Syntax.Raw.baseComparison X (⊤_ (Total.TotalCategory P))
      (.product (.coefficient (labels n)) (SyntaxPolynomial.power .term n))).inv
        ((U).map (PolynomialComparison.summandIso labels X n).hom p)).val=
      Nat.pair (((U).map prod.fst p).val)
        (((U).map (rawPowerIso X n).hom ((U).map prod.snd p)).val) := by
  erw [rawProduct_inverse_value]
  have hf : (PolynomialComparison.summandIso labels X n).hom ≫ prod.fst=prod.fst := by
    simp only [PolynomialComparison.summandIso,prod.mapIso_hom,Iso.refl_hom,prod.map_fst,Category.comp_id]
  have hs : (PolynomialComparison.summandIso labels X n).hom ≫ prod.snd=
      prod.snd ≫ (PolynomialComparison.powerIso X n).hom := by
    simp only [PolynomialComparison.summandIso,prod.mapIso_hom,Iso.refl_hom,prod.map_snd]
  have hfp := congrArg (fun f : labels n ⨯ finitePower X n ⟶ labels n => (U).map f p) hf
  have hsp := congrArg (fun f : labels n ⨯ finitePower X n ⟶
      (SyntaxPolynomial.power (D := Total.TotalCategory P) .term n).eval.obj
        (X,⊤_ (Total.TotalCategory P)) => (U).map f p) hs
  erw [CategoryTheory.Functor.map_comp_apply] at hfp
  erw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply] at hsp
  simp only [Syntax.Raw.baseComparison,Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id]
  erw [hfp,hsp]
  simp only [rawPowerIso,Iso.trans_hom,Iso.symm_hom,CategoryTheory.Functor.map_comp_apply]
  rfl

theorem injection_inverse_value (labels : ℕ → Total.TotalCategory P) (X : Total.TotalCategory P)
    (n : ℕ) (i : Fin (n+1)) (p : (U).obj (labels i.val ⨯ finitePower X i.val)) :
    ((U).map (Syntax.Raw.baseComparison X (⊤_ (Total.TotalCategory P))
      (SyntaxPolynomial.constructors labels n)).inv
        ((U).map (PolynomialComparison.injection labels X n i) p)).val=
      ruleTag n i (Nat.pair (((U).map prod.fst p).val)
        (((U).map (rawPowerIso X i.val).hom ((U).map prod.snd p)).val)) := by
  induction n with
  | zero =>
    have hi : i=0 := Fin.eq_zero i
    subst i
    have h := summand_inverse_value labels X 0 p
    have hs : (PolynomialComparison.summandIso labels X 0).hom=𝟙 _ := by
      simp only [PolynomialComparison.summandIso,PolynomialComparison.powerIso,
        prod.mapIso_hom,Iso.refl_hom,prod.map_id_id]
    simp only [ruleTag,PolynomialComparison.injection,SyntaxPolynomial.constructors]
    erw [hs] at h
    convert h using 1 <;> rfl
  | succ n ih =>
    revert p
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro p
      simp only [PolynomialComparison.injection,ruleTag,Fin.lastCases_last,
        Fin.val_last,CategoryTheory.Functor.map_comp_apply,SyntaxPolynomial.constructors]
      erw [rawSum_inverse_inr,summand_inverse_value]
    · intro p
      simp only [PolynomialComparison.injection,ruleTag,Fin.lastCases_castSucc,
        Fin.val_castSucc,CategoryTheory.Functor.map_comp_apply,SyntaxPolynomial.constructors]
      erw [rawSum_inverse_inl,ih]

variable {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)

def coefficientInput (X : Total.TotalCategory P) (i : Fin (N+1)) :
    R.instances i ⨯ finitePower X i.val ⟶ PolynomialComparison.coefficients R i.val ⨯ finitePower X i.val :=
  prod.map (eqToHom (PolynomialComparison.coefficients_fin R i).symm) (𝟙 _)

theorem coefficientInput_injection (X : Total.TotalCategory P) (i : Fin (N+1)) :
    coefficientInput R X i ≫ PolynomialComparison.injection (PolynomialComparison.coefficients R) X N i ≫
      (PolynomialComparison.comparison R).hom.app X=
        Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower X j.val) i := by
  rw [PolynomialComparison.injection_comparison]
  unfold coefficientInput
  rw [← Category.assoc,prod.map_map]
  simp

theorem ordinaryInput_inverse_value (i : Fin (N+1))
    (p : (U).obj (R.instances i ⨯ finitePower (ordinaryTree R).a i.val)) :
    ((U).map (ordinaryInputIso R).inv
      ((U).map (Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower (ordinaryTree R).a j.val) i) p)).val=
      ruleTag N i (Nat.pair (((U).map prod.fst p).val)
        (((U).map (rawPowerIso (ordinaryTree R).a i.val).hom ((U).map prod.snd p)).val)) := by
  let labels := PolynomialComparison.coefficients R
  let X := (ordinaryTree R).a
  let pc := (U).map (coefficientInput R X i) p
  have he : (U).map ((PolynomialComparison.comparison R).app X).inv
      ((U).map (Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower X j.val) i) p)=
        (U).map (PolynomialComparison.injection labels X N i) pc := by
    have hh := congrArg (fun f : R.instances i ⨯ finitePower X i.val ⟶
        (PolynomialComparison.ordinary R).obj X =>
          f≫((PolynomialComparison.comparison R).app X).inv)
      (coefficientInput_injection R X i)
    simp only [Category.assoc] at hh
    change coefficientInput R X i≫PolynomialComparison.injection labels X N i≫
        ((PolynomialComparison.comparison R).app X).hom≫((PolynomialComparison.comparison R).app X).inv=
      Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower X j.val) i≫
        ((PolynomialComparison.comparison R).app X).inv at hh
    rw [Iso.hom_inv_id,Category.comp_id] at hh
    have hv := congrArg (fun f : R.instances i ⨯ finitePower X i.val ⟶
        (SyntacticSyntax.constructorFunctor labels N).obj X => (U).map f p) hh
    simp only [CategoryTheory.Functor.map_comp_apply] at hv
    exact hv.symm
  have hcoordinates := projection_inverse_value labels N (treePair R)
    ((U).map ((PolynomialComparison.comparison R).app X).inv
      ((U).map (Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower X j.val) i) p))
  simp only [CategoryTheory.Functor.map_comp_apply] at hcoordinates
  simp only [ordinaryInputIso,Iso.trans_inv,CategoryTheory.Functor.map_comp_apply]
  erw [hcoordinates,he,injection_inverse_value]
  have hf : ((U).map prod.fst pc).val=((U).map prod.fst p).val := by
    change ((U).map prod.fst ((U).map (prod.map _ (𝟙 _)) p)).val=_
    erw [← CategoryTheory.Functor.map_comp_apply,prod.map_fst,CategoryTheory.Functor.map_comp_apply,eqToHom_value]
  have hs : (U).map prod.snd pc=(U).map prod.snd p := by
    change (U).map prod.snd ((U).map (prod.map _ (𝟙 _)) p)=_
    erw [← CategoryTheory.Functor.map_comp_apply,prod.map_snd,Category.comp_id]
  erw [hf,hs]
  rfl

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
