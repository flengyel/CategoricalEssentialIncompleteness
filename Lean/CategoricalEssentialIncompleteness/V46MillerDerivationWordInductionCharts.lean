import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionPowers

/-! # Exact raw charts after forgetting the unused formula sort

The complete source, target and isomorphism are compared together by
dependent equality. This removes the unused sort without identifying
chosen products or coproducts with their scalar encodings.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
open SyntacticDerivation SyntacticSyntax
variable {P : Uniform.Family}
local notation "U" => (Total.underlying (P := P))

structure ChartData where
  source : Total.TotalCategory P
  target : Total.TotalCategory P
  iso : source ≅ target

def ChartData.product (a b : ChartData (P := P)) : ChartData (P := P) where
  source := ⟨Total.product a.source.obj b.source.obj⟩
  target := a.target ⨯ b.target
  iso := Syntax.Raw.baseProductIso a.source b.source ≪≫ prod.mapIso a.iso b.iso

def ChartData.sum (a b : ChartData (P := P)) : ChartData (P := P) where
  source := Syntax.Raw.taggedSumObject a.source b.source
  target := a.target ⨿ b.target
  iso := Syntax.Raw.taggedSumIso a.source b.source ≪≫
    Syntax.Raw.baseCoproductIso a.source b.source ≪≫ coprod.mapIso a.iso b.iso

theorem chart_square {a b : ChartData (P := P)} (h : a=b) :
    eqToHom (congrArg ChartData.source h) ≫ b.iso.hom=
      a.iso.hom ≫ eqToHom (congrArg ChartData.target h) := by
  cases h
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

theorem prod_map_eqToHom {A B A' B' : Total.TotalCategory P} (h : A=A') (k : B=B') :
    prod.map (eqToHom h) (eqToHom k)=eqToHom (congrArg₂ (fun X Y => X ⨯ Y) h k) := by
  cases h
  cases k
  simp only [eqToHom_refl,prod.map_id_id]

theorem coprod_map_eqToHom {A B A' B' : Total.TotalCategory P} (h : A=A') (k : B=B') :
    coprod.map (eqToHom h) (eqToHom k)=eqToHom (congrArg₂ (fun X Y => X ⨿ Y) h k) := by
  cases h
  cases k
  simp only [eqToHom_refl,coprod.map_id_id]

theorem eqToHom_value {X Y : Total.TotalCategory P} (h : X=Y) (x : (U).obj X) :
    ((U).map (eqToHom h) x).val=x.val := by
  cases h
  simp only [eqToHom_refl,CategoryTheory.Functor.map_id_apply]

def powerData (X Y : Total.TotalCategory P) (n : ℕ) : ChartData (P := P) where
  source := Syntax.Raw.baseObject X Y (SyntaxPolynomial.power .term n)
  target := (SyntaxPolynomial.power .term n).eval.obj (X,Y)
  iso := Syntax.Raw.baseComparison X Y (SyntaxPolynomial.power .term n)

theorem powerData_second (X Y Z : Total.TotalCategory P) (n : ℕ) : powerData X Y n=powerData X Z n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change ChartData.product (powerData X Y (n+1)) ⟨X,X,Iso.refl X⟩=
        ChartData.product (powerData X Z (n+1)) ⟨X,X,Iso.refl X⟩
      exact congrArg (fun a => ChartData.product a ⟨X,X,Iso.refl X⟩) ih

theorem powerData_map (X Y Z : Total.TotalCategory P) (g : Y ⟶ Z) (n : ℕ) :
    (SyntaxPolynomial.power .term n).eval.map ((𝟙 X,g) : (X,Y) ⟶ (X,Z))=
      eqToHom (congrArg ChartData.target (powerData_second X Y Z n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change prod.map _ (𝟙 X)=_
      rw [ih]
      simpa only [eqToHom_refl] using
        prod_map_eqToHom (congrArg ChartData.target (powerData_second X Y Z (n+1))) (rfl : X=X)

def coefficientData (C : Total.TotalCategory P) : ChartData (P := P) := ⟨C,C,Iso.refl C⟩

def constructorsData (labels : ℕ → Total.TotalCategory P) (X Y : Total.TotalCategory P) (n : ℕ) : ChartData (P := P) where
  source := Syntax.Raw.baseObject X Y (SyntaxPolynomial.constructors labels n)
  target := (SyntaxPolynomial.constructors labels n).eval.obj (X,Y)
  iso := Syntax.Raw.baseComparison X Y (SyntaxPolynomial.constructors labels n)

theorem constructorsData_second (labels : ℕ → Total.TotalCategory P) (X Y Z : Total.TotalCategory P) (n : ℕ) :
    constructorsData labels X Y n=constructorsData labels X Z n := by
  induction n with
  | zero =>
    change ChartData.product (coefficientData (labels 0)) (powerData X Y 0)=
      ChartData.product (coefficientData (labels 0)) (powerData X Z 0)
    exact congrArg (ChartData.product (coefficientData (labels 0))) (powerData_second X Y Z 0)
  | succ n ih =>
    change ChartData.sum (constructorsData labels X Y n)
      (ChartData.product (coefficientData (labels (n+1))) (powerData X Y (n+1)))=
      ChartData.sum (constructorsData labels X Z n)
        (ChartData.product (coefficientData (labels (n+1))) (powerData X Z (n+1)))
    exact congrArg₂ ChartData.sum ih
      (congrArg (ChartData.product (coefficientData (labels (n+1)))) (powerData_second X Y Z (n+1)))

theorem constructorsData_map (labels : ℕ → Total.TotalCategory P) (X Y Z : Total.TotalCategory P)
    (g : Y ⟶ Z) (n : ℕ) :
    (SyntaxPolynomial.constructors labels n).eval.map ((𝟙 X,g) : (X,Y) ⟶ (X,Z))=
      eqToHom (congrArg ChartData.target (constructorsData_second labels X Y Z n)) := by
  induction n with
  | zero =>
    change prod.map (𝟙 (labels 0)) _=_
    rw [powerData_map]
    change prod.map (𝟙 (labels 0)) (𝟙 (⊤_ (Total.TotalCategory P)))=𝟙 _
    exact prod.map_id_id
  | succ n ih =>
    change coprod.map _ (prod.map (𝟙 (labels (n+1))) _)=_
    rw [ih,powerData_map]
    rw [show (𝟙 (labels (n+1)))=eqToHom (rfl : labels (n+1)=labels (n+1)) from rfl,
      prod_map_eqToHom,coprod_map_eqToHom]

theorem constructors_raw_square (labels : ℕ → Total.TotalCategory P) (X Y Z : Total.TotalCategory P)
    (g : Y ⟶ Z) (n : ℕ) :
    eqToHom (congrArg ChartData.source (constructorsData_second labels X Y Z n)) ≫
      (Syntax.Raw.baseComparison X Z (SyntaxPolynomial.constructors labels n)).hom=
      (Syntax.Raw.baseComparison X Y (SyntaxPolynomial.constructors labels n)).hom ≫
        (SyntaxPolynomial.constructors labels n).eval.map ((𝟙 X,g) : (X,Y) ⟶ (X,Z)) := by
  rw [constructorsData_map]
  exact chart_square (constructorsData_second labels X Y Z n)

theorem constructors_inverse_square (labels : ℕ → Total.TotalCategory P) (X Y Z : Total.TotalCategory P)
    (g : Y ⟶ Z) (n : ℕ) :
    (Syntax.Raw.baseComparison X Y (SyntaxPolynomial.constructors labels n)).inv ≫
      eqToHom (congrArg ChartData.source (constructorsData_second labels X Y Z n))=
      (SyntaxPolynomial.constructors labels n).eval.map ((𝟙 X,g) : (X,Y) ⟶ (X,Z)) ≫
        (Syntax.Raw.baseComparison X Z (SyntaxPolynomial.constructors labels n)).inv := by
  apply (cancel_epi (Syntax.Raw.baseComparison X Y (SyntaxPolynomial.constructors labels n)).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have h := congrArg (fun k : Syntax.Raw.baseObject X Y (SyntaxPolynomial.constructors labels n) ⟶
    (SyntaxPolynomial.constructors labels n).eval.obj (X,Z) =>
      k≫(Syntax.Raw.baseComparison X Z (SyntaxPolynomial.constructors labels n)).inv)
        (constructors_raw_square labels X Y Z g n)
  simpa only [Category.assoc,Iso.hom_inv_id,Category.comp_id] using h

/-- An inverse raw chart reads the same ordered children in either
choice of the unused second sort. -/
theorem projection_inverse_value (labels : ℕ → Total.TotalCategory P) (n : ℕ)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors labels n) .unit))
    (z : (U).obj ((SyntacticSyntax.constructorFunctor labels n).obj A.a.1)) :
    ((U).map ((asIso (SyntacticSyntax.constructorProjection labels n A)).inv ≫
      (Syntax.Raw.baseComparison A.a.1 A.a.2 (SyntaxPolynomial.constructors labels n)).inv) z).val=
      ((U).map (Syntax.Raw.baseComparison A.a.1 (⊤_ (Total.TotalCategory P))
        (SyntaxPolynomial.constructors labels n)).inv z).val := by
  let h := constructorsData_second labels A.a.1 A.a.2 (⊤_ (Total.TotalCategory P)) n
  have hs := constructors_inverse_square labels A.a.1 A.a.2 (⊤_ (Total.TotalCategory P))
    (terminal.from A.a.2) n
  have he : (asIso (SyntacticSyntax.constructorProjection labels n A)).inv ≫
      (Syntax.Raw.baseComparison A.a.1 A.a.2 (SyntaxPolynomial.constructors labels n)).inv ≫
        eqToHom (congrArg ChartData.source h)=
      (Syntax.Raw.baseComparison A.a.1 (⊤_ (Total.TotalCategory P))
        (SyntaxPolynomial.constructors labels n)).inv := by
    erw [hs]
    change inv (SyntacticSyntax.constructorProjection labels n A) ≫
      (SyntacticSyntax.constructorProjection labels n A ≫ _)=_
    rw [IsIso.inv_hom_id_assoc]
  have hp := congrArg (fun k => ((U).map k z).val) he
  simp only [CategoryTheory.Functor.map_comp_apply] at hp
  erw [eqToHom_value] at hp
  exact hp

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
