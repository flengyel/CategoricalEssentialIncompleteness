import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionInputs

/-! # Strict decrease for every actual typed child of a uniform proof -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
open SyntacticDerivation SyntacticSyntax
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
local notation "U" => (Total.underlying (P := P))
local notation "A" => wordAlgebra R

def constructor (i : Fin (N+1)) : R.ruleObject (A).a i ⟶ (A).a.left :=
  Sigma.ι (R.ruleObject (A).a) i ≫ (A).str.left

@[simp] theorem constructor_eq_wordConstructor (i : Fin (N+1)) :
    constructor R i=Derivation.wordConstructor R i := rfl

def ruleChildren (i : Fin (N+1)) : R.ruleObject (A).a i ⟶ finitePower (A).a.left i.val :=
  pullback.snd (R.premises i) (finitePowerMap (A).a.hom i.val)

def typedChild (i : Fin (N+1)) (k : Fin i.val) : R.ruleObject (A).a i ⟶ (A).a.left :=
  ruleChildren R i ≫ finiteChild (A).a.left i.val k

def typedPremise (i : Fin (N+1)) (k : Fin i.val) : R.ruleObject (A).a i ⟶ F :=
  pullback.fst (R.premises i) (finitePowerMap (A).a.hom i.val) ≫
    R.premises i ≫ finiteChild F i.val k

@[reassoc] theorem typedChild_conclusion (i : Fin (N+1)) (k : Fin i.val) :
    typedChild R i k ≫ wordConclusion R=typedPremise R i k := by
  unfold typedChild ruleChildren typedPremise
  erw [Category.assoc,← finiteChild_natural (wordConclusion R) i.val k,← Category.assoc,← pullback.condition]
  exact Category.assoc _ _ _

@[reassoc] theorem constructor_conclusion (i : Fin (N+1)) :
    constructor R i ≫ wordConclusion R=R.ruleConclusion (A).a i :=
  Derivation.wordConstructor_conclusion R i

theorem typed_constructor_tree (i : Fin (N+1)) :
    constructor R i ≫ wordInclusion R=
      CheckedRoot.matchingMap R (A).a i ≫
        prod.map (𝟙 (R.instances i)) (finitePowerMap (wordInclusion R) i.val) ≫
        Sigma.ι (fun j : Fin (N+1) => R.instances j ⨯ finitePower (ordinaryTree R).a j.val) i ≫
          (ordinaryTree R).str := by
  have he := congrArg (fun k => Sigma.ι (R.ruleObject (A).a) i ≫ k) (word_constructor_tree R)
  simpa only [constructor,InputGeometry.forget,PolynomialComparison.ordinary,
    Category.assoc,Sigma.ι_comp_desc_assoc,Sigma.ι_map_assoc] using he

theorem wordInclusion_value (x : (U).obj (A).a.left) :
    ((U).map (wordInclusion R) x).val=x.val :=
  ((wordInclusion_graph R _ _).mp (Total.totalFunction_mem (wordInclusion R) x)).2

theorem ordinary_constructor_value
    (w : (U).obj ((PolynomialComparison.ordinary R).obj (ordinaryTree R).a)) :
    ((U).map (ordinaryTree R).str w).val=
      Coding.constructor false (Syntax.Raw.skeleton (treePolynomial R))
        ((U).map (ordinaryInputIso R).inv w).val := by
  let u := (U).map (ordinaryInputIso R).inv w
  have he : (U).map (Syntax.Raw.rawWordConstructor (treePolynomial R) .unit false) u=
      (U).map (ordinaryTree R).str w := by
    have hc : (ordinaryInputIso R).inv≫Syntax.Raw.rawWordConstructor (treePolynomial R) .unit false=
        (ordinaryTree R).str := by
      rw [← ordinaryInputIso_constructor, Iso.inv_hom_id_assoc]
    have hh := congrArg (fun f : (PolynomialComparison.ordinary R).obj (ordinaryTree R).a ⟶
        (ordinaryTree R).a => (U).map f w) hc
    erw [CategoryTheory.Functor.map_comp_apply] at hh
    exact hh
  have hm := Total.totalFunction_mem (Syntax.Raw.rawWordConstructor (treePolynomial R) .unit false) u
  have hv := ((Syntax.Raw.rawWordConstructor_graph (treePolynomial R) .unit false _ _).mp hm).2
  exact (congrArg Subtype.val he).symm.trans hv

/-- The conclusion of each child is matched to its own prescribed
premise. This rank statement does not identify it with the parent conclusion. -/
theorem typed_children_smaller (i : Fin (N+1))
    (r : (U).obj (R.ruleObject (A).a i)) (k : Fin i.val) :
    FFL.FirstOrder.Arithmetic.len ((U).map (typedChild R i k) r).val<
      FFL.FirstOrder.Arithmetic.len ((U).map (constructor R i) r).val := by
  let Q := (A).a
  let X := (ordinaryTree R).a
  let j := wordInclusion R
  let p := (U).map (CheckedRoot.matchingMap R Q i) r
  let p' := (U).map (prod.map (𝟙 (R.instances i)) (finitePowerMap j i.val)) p
  let w := (U).map (Sigma.ι (fun h : Fin (N+1) => R.instances h ⨯ finitePower X h.val) i) p'
  let parent := (U).map (constructor R i) r
  let tuple := (U).map (rawPowerIso X i.val).hom ((U).map prod.snd p')
  let label := ((U).map prod.fst p').val
  let input := ruleTag N i (Nat.pair label tuple.val)
  have htree : (U).map j parent=(U).map (ordinaryTree R).str w := by
    have h := congrArg (fun f => (U).map f r) (typed_constructor_tree R i)
    simp only [CategoryTheory.Functor.map_comp_apply] at h
    dsimp only [j,parent,w,p',p,Q,X]
    exact h
  have hparent : parent.val=((U).map (ordinaryTree R).str w).val :=
    (wordInclusion_value R parent).symm.trans (congrArg Subtype.val htree)
  have hinput : ((U).map (ordinaryInputIso R).inv w).val=input :=
    ordinaryInput_inverse_value R i p'
  have hv : parent.val=Coding.constructor false (Syntax.Raw.skeleton (treePolynomial R)) input :=
    hparent.trans ((ordinary_constructor_value R w).trans
      (congrArg (Coding.constructor false (Syntax.Raw.skeleton (treePolynomial R))) hinput))
  have hs : Coding.ChildSize (Syntax.Raw.skeleton (treePolynomial R)) (FFL.FirstOrder.Arithmetic.len parent.val) input := by
    rw [hv]
    exact (Coding.childSizeGraph_eval _ _ _).mp
      (Coding.children_smaller false (Syntax.Raw.skeleton (treePolynomial R)) input)
  have ht := ruleTag_childSize (PolynomialComparison.coefficients R) N i
    (FFL.FirstOrder.Arithmetic.len parent.val) label tuple.val hs
  have hsmall : FFL.FirstOrder.Arithmetic.len (tupleChild i.val k tuple.val)<FFL.FirstOrder.Arithmetic.len parent.val :=
    tupleChild_smaller X (⊤_ (Total.TotalCategory P)) i.val k _ tuple.val tuple.property ht
  have hchildren : (U).map prod.snd p'=
      (U).map (finitePowerMap j i.val) ((U).map (ruleChildren R i) r) := by
    rw [show (U).map prod.snd p'=(U).map (finitePowerMap j i.val) ((U).map prod.snd p) by
      dsimp only [p']
      rw [← CategoryTheory.Functor.map_comp_apply,prod.map_snd,CategoryTheory.Functor.map_comp_apply]]
    congr 1
    dsimp only [p]
    have hproj : CheckedRoot.matchingMap R Q i≫prod.snd=ruleChildren R i := by
      dsimp only [CheckedRoot.matchingMap,ruleChildren]
      exact prod.lift_snd _ _
    have hh := congrArg (fun f : R.ruleObject (A).a i ⟶ finitePower (A).a.left i.val =>
      (U).map f r) hproj
    erw [CategoryTheory.Functor.map_comp_apply] at hh
    exact hh
  have hchild : (U).map j ((U).map (typedChild R i k) r)=
      (U).map (finiteChild X i.val k) ((U).map prod.snd p') := by
    rw [hchildren]
    have hh := congrArg (fun f : finitePower (A).a.left i.val ⟶ X =>
        (U).map f ((U).map (ruleChildren R i) r)) (finiteChild_natural j i.val k)
    erw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply] at hh
    dsimp only [typedChild]
    erw [CategoryTheory.Functor.map_comp_apply]
    exact hh.symm
  have he : ((U).map (typedChild R i k) r).val=tupleChild i.val k tuple.val :=
    (wordInclusion_value R ((U).map (typedChild R i k) r)).symm.trans
      ((congrArg Subtype.val hchild).trans (finiteChild_value X i.val k ((U).map prod.snd p')))
  rw [he]
  exact hsmall

end CategoricalEssentialIncompleteness.V46.Miller.Derivation.WordInduction
