import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeSubstitutionFrame
import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformAlgebra

/-! # Native nodes in the actual parameter-word algebra

All points and point morphisms belong to the uniform target. The parameter
chart is proved within that category. The input calculation retains the
literal coefficient, name, summand tag, and ordered finite children.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
open NamedFiniteSyntax NamedPostfixEncoding

section FrameGeometry
variable {D : Type u} [Category.{v} D] [HasFiniteLimits D]
variable {O R X Y : D}

def nodeFrame (a : O ⟶ R) (f : O ⟶ X) : Over.mk a ⟶ constantFamily R X :=
  Over.homMk (prod.lift a f) (prod.lift_fst a f)

private theorem nodeFrame_eta (a : O ⟶ R) (f : Over.mk a ⟶ constantFamily R X) :
    f=nodeFrame a (f.left ≫ (prod.snd : R ⨯ X ⟶ X)) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · change f.left ≫ prod.fst=prod.lift a (f.left ≫ prod.snd) ≫ prod.fst
    rw [prod.lift_fst]
    exact Over.w f
  · exact (prod.lift_snd a (f.left ≫ prod.snd)).symm

private theorem nodeFrame_map (a : O ⟶ R) (f : O ⟶ X) (g : X ⟶ Y) :
    nodeFrame a f ≫ (constantFamilyFunctor R).map g=nodeFrame a (f ≫ g) := by
  apply Over.OverMorphism.ext
  change prod.lift a f ≫ prod.map (𝟙 R) g=prod.lift a (f ≫ g)
  rw [prod.lift_map,Category.comp_id]

private theorem nodeFrame_unit (a : O ⟶ R) :
    terminal.from (Over.mk a) ≫ constantUnitComparison R=
      nodeFrame a (terminal.from O) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · exact terminalIsTerminal.hom_ext _ _

private theorem nodeFrame_product (a : O ⟶ R) (f : O ⟶ X) (g : O ⟶ Y) :
    prod.lift (nodeFrame a f) (nodeFrame a g) ≫ constantProductComparison R X Y=
      nodeFrame a (prod.lift f g) := by
  have hv :
      (prod.lift (nodeFrame a f) (nodeFrame a g) ≫ constantProductComparison R X Y).left ≫
          (prod.snd : R ⨯ (X ⨯ Y) ⟶ X ⨯ Y)=
        prod.lift
          ((prod.lift (nodeFrame a f) (nodeFrame a g) ≫
            (prod.fst : constantFamily R X ⨯ constantFamily R Y ⟶ constantFamily R X)).left ≫
              (prod.snd : R ⨯ X ⟶ X))
          ((prod.lift (nodeFrame a f) (nodeFrame a g) ≫
            (prod.snd : constantFamily R X ⨯ constantFamily R Y ⟶ constantFamily R Y)).left ≫
              (prod.snd : R ⨯ Y ⟶ Y)) := by
    simp only [Over.comp_left,constantProductComparison,Over.homMk_left,
      Category.assoc,prod.lift_snd,prod.comp_lift]
    apply congrArg (fun k => prod.lift _ k)
    simpa only [Over.comp_left,Category.assoc] using
      congrArg (fun k : Over.mk a ⟶ constantFamily R Y => k.left ≫ prod.snd)
        (prod.lift_snd (nodeFrame a f) (nodeFrame a g))
  have hv' :
      (prod.lift (nodeFrame a f) (nodeFrame a g) ≫ constantProductComparison R X Y).left ≫
          (prod.snd : R ⨯ (X ⨯ Y) ⟶ X ⨯ Y)=prod.lift f g := by
    simpa only [prod.lift_fst,prod.lift_snd,nodeFrame,Over.homMk_left] using hv
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · exact hv'.trans (prod.lift_snd a (prod.lift f g)).symm

end FrameGeometry

namespace PointFrame
variable {P : Uniform.Family}
local notation "U" => Total.underlying (P := P)

/-- Forget only the common frame, retaining the actual ordered input. -/
def nodeBaseArrow (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) :
    (p : SyntaxPolynomial (Total.TotalCategory P)) →
      Data R r (constantFamily R X,constantFamily R Y) p →
        ((source R r).left ⟶ p.eval.obj (X,Y))
  | .term,f => f.left ≫ prod.snd
  | .formula,f => f.left ≫ prod.snd
  | .coefficient _,x => Total.underlyingPoint x
  | .unit,_ => terminal.from _
  | .product p q,z => prod.lift (nodeBaseArrow R r X Y p z.1) (nodeBaseArrow R r X Y q z.2)
  | .sum p _,.inl z => nodeBaseArrow R r X Y p z ≫ coprod.inl
  | .sum _ q,.inr z => nodeBaseArrow R r X Y q z ≫ coprod.inr

/-- The parameter chart is evaluated in the same target category. -/
theorem realize_parameterComparison (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P))
    (z : Data R r (constantFamily R X,constantFamily R Y) p) :
    realize R r (constantFamily R X,constantFamily R Y) p z ≫
        SyntaxPolynomial.parameterComparison R (X,Y) p=
      nodeFrame (Total.underlyingPoint r) (nodeBaseArrow R r X Y p z) := by
  induction p with
  | term =>
      change z ≫ 𝟙 _=nodeFrame (Total.underlyingPoint r) (z.left ≫ prod.snd)
      rw [Category.comp_id]
      exact nodeFrame_eta (Total.underlyingPoint r) z
  | formula =>
      change z ≫ 𝟙 _=nodeFrame (Total.underlyingPoint r) (z.left ≫ prod.snd)
      rw [Category.comp_id]
      exact nodeFrame_eta (Total.underlyingPoint r) z
  | coefficient C =>
      change PointFrame.constant R r C z ≫ 𝟙 _=nodeFrame (Total.underlyingPoint r) (Total.underlyingPoint z)
      rw [Category.comp_id]
      rfl
  | unit => exact nodeFrame_unit (Total.underlyingPoint r)
  | product p q hp hq =>
      change prod.lift (realize R r _ p z.1) (realize R r _ q z.2) ≫
        (prod.map (SyntaxPolynomial.parameterComparison R (X,Y) p)
          (SyntaxPolynomial.parameterComparison R (X,Y) q) ≫
            constantProductComparison R (p.eval.obj (X,Y)) (q.eval.obj (X,Y)))=_
      rw [← Category.assoc,prod.lift_map,hp,hq]
      exact nodeFrame_product (Total.underlyingPoint r)
        (nodeBaseArrow R r X Y p z.1) (nodeBaseArrow R r X Y q z.2)
  | sum p q hp hq =>
      cases z with
      | inl z =>
          change (realize R r _ p z ≫ coprod.inl) ≫
            (coprod.map (SyntaxPolynomial.parameterComparison R (X,Y) p)
              (SyntaxPolynomial.parameterComparison R (X,Y) q) ≫
                coprod.desc ((constantFamilyFunctor R).map coprod.inl)
                  ((constantFamilyFunctor R).map coprod.inr))=_
          simp only [Category.assoc,coprod.inl_map_assoc,coprod.inl_desc]
          rw [← Category.assoc,hp]
          exact nodeFrame_map (Total.underlyingPoint r) (nodeBaseArrow R r X Y p z) coprod.inl
      | inr z =>
          change (realize R r _ q z ≫ coprod.inr) ≫
            (coprod.map (SyntaxPolynomial.parameterComparison R (X,Y) p)
              (SyntaxPolynomial.parameterComparison R (X,Y) q) ≫
                coprod.desc ((constantFamilyFunctor R).map coprod.inl)
                  ((constantFamilyFunctor R).map coprod.inr))=_
          simp only [Category.assoc,coprod.inr_map_assoc,coprod.inr_desc]
          rw [← Category.assoc,hq]
          exact nodeFrame_map (Total.underlyingPoint r) (nodeBaseArrow R r X Y q z) coprod.inr

/-- The public second-projection form has no private frame constructor in
its statement. It evaluates the actual parameter comparison, within one
uniform category, on arbitrary framed polynomial data. -/
theorem realize_parameter_value (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P))
    (z : Data R r (constantFamily R X,constantFamily R Y) p) :
    (realize R r (constantFamily R X,constantFamily R Y) p z ≫
        SyntaxPolynomial.parameterComparison R (X,Y) p).left ≫
          (prod.snd : R ⨯ p.eval.obj (X,Y) ⟶ p.eval.obj (X,Y))=
      nodeBaseArrow R r X Y p z := by
  have h := congrArg (fun f : source R r ⟶ constantFamily R (p.eval.obj (X,Y)) => f.left ≫
      (prod.snd : R ⨯ p.eval.obj (X,Y) ⟶ p.eval.obj (X,Y)))
    (realize_parameterComparison R r X Y p z)
  exact h.trans (prod.lift_snd _ _)

theorem realize_parameterTerm (R : Total.TotalCategory P) (r : (U).obj R)
    (p q : SyntaxPolynomial (Total.TotalCategory P))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (z : Data R r (SyntaxPolynomial.algebraWithParameters p q B R).a p) :
    realize R r (SyntaxPolynomial.algebraWithParameters p q B R).a p z ≫
        (SyntaxPolynomial.algebraWithParameters p q B R).str.1=
      nodeFrame (Total.underlyingPoint r) (nodeBaseArrow R r B.a.1 B.a.2 p z ≫ B.str.1) := by
  change realize R r (constantFamily R B.a.1,constantFamily R B.a.2) p z ≫
    (SyntaxPolynomial.parameterComparison R (B.a.1,B.a.2) p ≫
      (constantFamilyFunctor R).map B.str.1)=_
  rw [← Category.assoc,realize_parameterComparison R r B.a.1 B.a.2 p z]
  exact nodeFrame_map (Total.underlyingPoint r) _ B.str.1

theorem realize_parameterFormula (R : Total.TotalCategory P) (r : (U).obj R)
    (p q : SyntaxPolynomial (Total.TotalCategory P))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (z : Data R r (SyntaxPolynomial.algebraWithParameters p q B R).a q) :
    realize R r (SyntaxPolynomial.algebraWithParameters p q B R).a q z ≫
        (SyntaxPolynomial.algebraWithParameters p q B R).str.2=
      nodeFrame (Total.underlyingPoint r) (nodeBaseArrow R r B.a.1 B.a.2 q z ≫ B.str.2) := by
  change realize R r (constantFamily R B.a.1,constantFamily R B.a.2) q z ≫
    (SyntaxPolynomial.parameterComparison R (B.a.1,B.a.2) q ≫
      (constantFamilyFunctor R).map B.str.2)=_
  rw [← Category.assoc,realize_parameterComparison R r B.a.1 B.a.2 q z]
  exact nodeFrame_map (Total.underlyingPoint r) _ B.str.2

/-- Numerical raw inputs use the already proved standard pairing chart. -/
def nodeInputCode (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) :
    (p : SyntaxPolynomial (Total.TotalCategory P)) →
      Data R r (constantFamily R X,constantFamily R Y) p → ℕ
  | .term,f => ((U).map (f.left ≫ prod.snd) ⟨0,rfl⟩).val
  | .formula,f => ((U).map (f.left ≫ prod.snd) ⟨0,rfl⟩).val
  | .coefficient _,x => x.val
  | .unit,_ => 0
  | .product p q,z => Nat.pair (nodeInputCode R r X Y p z.1) (nodeInputCode R r X Y q z.2)
  | .sum p _,.inl z => Nat.pair (nodeInputCode R r X Y p z) 0
  | .sum _ q,.inr z => Nat.pair (nodeInputCode R r X Y q z) 1

private theorem point_value {X : Total.TotalCategory P} (x : (U).obj X) :
    (U).map (Total.underlyingPoint x) ⟨0,rfl⟩=x :=
  (Total.pointHomEquiv X).left_inv x

private theorem coded_fst_value (X Y : Total.TotalCategory P)
    (z : (U).obj (Total.totalProduct X Y)) :
    ((U).map (Total.totalFst X Y) z).val=(Nat.unpair z.val).1 :=
  ((Total.mem_partialFst X.obj Y.obj _ _).mp (Total.totalFunction_mem (Total.totalFst X Y) z)).2.symm

private theorem coded_snd_value (X Y : Total.TotalCategory P)
    (z : (U).obj (Total.totalProduct X Y)) :
    ((U).map (Total.totalSnd X Y) z).val=(Nat.unpair z.val).2 :=
  ((Total.mem_partialSnd X.obj Y.obj _ _).mp (Total.totalFunction_mem (Total.totalSnd X Y) z)).2.symm

private theorem tagged_inl_value (X Y : Total.TotalCategory P) (z : (U).obj X) :
    ((U).map (Syntax.Raw.taggedInl X Y) z).val=Nat.pair z.val 0 := by
  have h := Total.totalFunction_mem (Syntax.Raw.taggedInl X Y) z
  exact ((Total.mem_totalFromFunction (fun n => Nat.pair n 0)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0))
    (Syntax.Raw.taggedInl_supported X Y) _ _).mp h).2

private theorem tagged_inr_value (X Y : Total.TotalCategory P) (z : (U).obj Y) :
    ((U).map (Syntax.Raw.taggedInr X Y) z).val=Nat.pair z.val 1 := by
  have h := Total.totalFunction_mem (Syntax.Raw.taggedInr X Y) z
  exact ((Total.mem_totalFromFunction (fun n => Nat.pair n 1)
    (Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 1))
    (Syntax.Raw.taggedInr_supported X Y) _ _).mp h).2

private theorem mapped_comp_id_value {O X : Total.TotalCategory P}
    (f : O ⟶ X) (x : (U).obj O) :
    ((U).map (f ≫ 𝟙 X) x).val=((U).map f x).val :=
  congrArg (fun m => ((U).map m x).val) (Category.comp_id f)

private theorem mapped_square_value {O X Y : Total.TotalCategory P}
    (f : O ⟶ X) (g : X ⟶ Y) (h : O ⟶ Y) (he : f ≫ g=h) (x : (U).obj O) :
    ((U).map g ((U).map f x)).val=((U).map h x).val := by
  rw [← CategoryTheory.Functor.map_comp_apply,he]

/-- The chosen input chart recovers exactly the ordered literal payload. -/
theorem nodeBaseArrow_code (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P))
    (z : Data R r (constantFamily R X,constantFamily R Y) p) :
    ((U).map (nodeBaseArrow R r X Y p z ≫ (Syntax.Raw.baseComparison X Y p).inv) ⟨0,rfl⟩).val=
      nodeInputCode R r X Y p z := by
  induction p with
  | term =>
      change ((U).map ((z.left ≫ prod.snd) ≫ 𝟙 X) ⟨0,rfl⟩).val=
        ((U).map (z.left ≫ prod.snd) ⟨0,rfl⟩).val
      exact mapped_comp_id_value _ _
  | formula =>
      change ((U).map ((z.left ≫ prod.snd) ≫ 𝟙 Y) ⟨0,rfl⟩).val=
        ((U).map (z.left ≫ prod.snd) ⟨0,rfl⟩).val
      exact mapped_comp_id_value _ _
  | coefficient C =>
      change ((U).map (Total.underlyingPoint z ≫ 𝟙 C) ⟨0,rfl⟩).val=z.val
      exact (mapped_comp_id_value _ _).trans (congrArg Subtype.val (point_value z))
  | unit =>
      let x : (U).obj (⟨Total.terminalCarrier⟩ : Total.TotalCategory P) :=
        (U).map (terminal.from ((source R r).left) ≫
          (Syntax.Raw.baseUnitIso (P := P)).inv) ⟨0,rfl⟩
      change x.val=0
      exact x.property
  | product a b ha hb =>
      let w := (U).map (nodeBaseArrow R r X Y (.product a b) z ≫
        (Syntax.Raw.baseComparison X Y (.product a b)).inv) ⟨0,rfl⟩
      have hf : (Nat.unpair w.val).1=nodeInputCode R r X Y a z.1 := by
        have hfmap : nodeBaseArrow R r X Y (.product a b) z ≫
            (Syntax.Raw.baseComparison X Y (.product a b)).inv ≫
              Total.totalFst (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)=
            nodeBaseArrow R r X Y a z.1 ≫ (Syntax.Raw.baseComparison X Y a).inv := by
          change prod.lift (nodeBaseArrow R r X Y a z.1) (nodeBaseArrow R r X Y b z.2) ≫ _=_
          rw [Syntax.Raw.baseComparison_product_inv_fst,← Category.assoc,prod.lift_fst]
        calc
          (Nat.unpair w.val).1=
              ((U).map (Total.totalFst (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)) w).val :=
            (coded_fst_value _ _ w).symm
          _=((U).map (nodeBaseArrow R r X Y a z.1 ≫
              (Syntax.Raw.baseComparison X Y a).inv) ⟨0,rfl⟩).val := by
            exact mapped_square_value
              (nodeBaseArrow R r X Y (.product a b) z ≫
                (Syntax.Raw.baseComparison X Y (.product a b)).inv)
              (Total.totalFst (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b))
              (nodeBaseArrow R r X Y a z.1 ≫ (Syntax.Raw.baseComparison X Y a).inv)
              ((Category.assoc _ _ _).trans hfmap) ⟨0,rfl⟩
          _=nodeInputCode R r X Y a z.1 := ha z.1
      have hs : (Nat.unpair w.val).2=nodeInputCode R r X Y b z.2 := by
        have hsmap : nodeBaseArrow R r X Y (.product a b) z ≫
            (Syntax.Raw.baseComparison X Y (.product a b)).inv ≫
              Total.totalSnd (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)=
            nodeBaseArrow R r X Y b z.2 ≫ (Syntax.Raw.baseComparison X Y b).inv := by
          change prod.lift (nodeBaseArrow R r X Y a z.1) (nodeBaseArrow R r X Y b z.2) ≫ _=_
          rw [Syntax.Raw.baseComparison_product_inv_snd,← Category.assoc,prod.lift_snd]
        calc
          (Nat.unpair w.val).2=
              ((U).map (Total.totalSnd (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)) w).val :=
            (coded_snd_value _ _ w).symm
          _=((U).map (nodeBaseArrow R r X Y b z.2 ≫
              (Syntax.Raw.baseComparison X Y b).inv) ⟨0,rfl⟩).val := by
            exact mapped_square_value
              (nodeBaseArrow R r X Y (.product a b) z ≫
                (Syntax.Raw.baseComparison X Y (.product a b)).inv)
              (Total.totalSnd (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b))
              (nodeBaseArrow R r X Y b z.2 ≫ (Syntax.Raw.baseComparison X Y b).inv)
              ((Category.assoc _ _ _).trans hsmap) ⟨0,rfl⟩
          _=nodeInputCode R r X Y b z.2 := hb z.2
      change w.val=Nat.pair _ _
      exact (Nat.pair_unpair w.val).symm.trans (congrArg₂ Nat.pair hf hs)
  | sum a b ha hb =>
      cases z with
      | inl z =>
          have h : nodeBaseArrow R r X Y (.sum a b) (.inl z) ≫
              (Syntax.Raw.baseComparison X Y (.sum a b)).inv=
              (nodeBaseArrow R r X Y a z ≫ (Syntax.Raw.baseComparison X Y a).inv) ≫
                Syntax.Raw.taggedInl (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b) := by
            change (nodeBaseArrow R r X Y a z ≫ coprod.inl) ≫ _=_
            rw [Category.assoc,Syntax.Raw.baseComparison_sum_inv_inl,← Category.assoc]
          rw [h,CategoryTheory.Functor.map_comp_apply]
          exact (tagged_inl_value (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)
            ((U).map (nodeBaseArrow R r X Y a z ≫ (Syntax.Raw.baseComparison X Y a).inv) ⟨0,rfl⟩)).trans
              (congrArg (fun n => Nat.pair n 0) (ha z))
      | inr z =>
          have h : nodeBaseArrow R r X Y (.sum a b) (.inr z) ≫
              (Syntax.Raw.baseComparison X Y (.sum a b)).inv=
              (nodeBaseArrow R r X Y b z ≫ (Syntax.Raw.baseComparison X Y b).inv) ≫
                Syntax.Raw.taggedInr (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b) := by
            change (nodeBaseArrow R r X Y b z ≫ coprod.inr) ≫ _=_
            rw [Category.assoc,Syntax.Raw.baseComparison_sum_inv_inr,← Category.assoc]
          rw [h,CategoryTheory.Functor.map_comp_apply]
          exact (tagged_inr_value (Syntax.Raw.baseObject X Y a) (Syntax.Raw.baseObject X Y b)
            ((U).map (nodeBaseArrow R r X Y b z ≫ (Syntax.Raw.baseComparison X Y b).inv) ⟨0,rfl⟩)).trans
              (congrArg (fun n => Nat.pair n 1) (hb z))

theorem nodeInputCode_powerData (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) (n : ℕ)
    (children : Fin n → (source R r ⟶ constantFamily R X)) :
    nodeInputCode R r X Y (SyntaxPolynomial.power .term n)
        (powerData R r (constantFamily R X,constantFamily R Y) n children)=
      childTuple n (fun i => ((U).map ((children i).left ≫ prod.snd) ⟨0,rfl⟩).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change Nat.pair
            (nodeInputCode R r X Y (SyntaxPolynomial.power .term (n+1))
              (powerData R r (constantFamily R X,constantFamily R Y) (n+1)
                (fun i => children i.castSucc)))
            (((U).map ((children (Fin.last (n+1))).left ≫ prod.snd) ⟨0,rfl⟩).val)=_
          rw [ih,childTuple,Arithmetic.nat_pair_eq]

theorem nodeInputCode_arityData (R : Total.TotalCategory P) (r : (U).obj R)
    (X Y : Total.TotalCategory P) (τ : ℕ → Total.TotalCategory P)
    (d : ℕ) (k : Fin (d+1)) (c : (U).obj (τ k.val))
    (children : Fin k.val → (source R r ⟶ constantFamily R X)) :
    nodeInputCode R r X Y (SyntaxPolynomial.constructors τ d)
        (arityData R r (constantFamily R X,constantFamily R Y) τ d k c children)=
      arityInput d k (Nat.pair c.val
        (childTuple k.val (fun i => ((U).map ((children i).left ≫ prod.snd) ⟨0,rfl⟩).val))) := by
  induction d with
  | zero =>
      have hk : k=0 := Fin.eq_zero k
      subst k
      rfl
  | succ d ih =>
      revert c children
      refine Fin.lastCases ?_ (fun j => ?_) k
      · intro c children
        simp only [arityData,Fin.lastCases_last,SyntaxPolynomial.constructors,nodeInputCode,
          nodeInputCode_powerData,arityInput,Arithmetic.nat_pair_eq]
        rfl
      · intro c children
        simp only [arityData,Fin.lastCases_castSucc,SyntaxPolynomial.constructors,nodeInputCode,
          ih,arityInput,Arithmetic.nat_pair_eq]
        rfl

end PointFrame

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution
