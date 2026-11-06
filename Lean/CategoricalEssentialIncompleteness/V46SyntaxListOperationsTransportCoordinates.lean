import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransport
import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportBooleans
import CategoricalEssentialIncompleteness.V46CategoricalListOperations

/-! Constructor and cons-step coordinates under the genuine family,
coefficient and product comparisons. These are categorical equations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem list_map_lift {X A B : C} (f : X ⟶ A) (g : X ⟶ B) :
    E.functor.map (prod.lift f g) ≫ prodComparison E.functor A B =
      prod.lift (E.functor.map f) (E.functor.map g) := by
  apply prod.hom_ext
  · simp only [Category.assoc,prodComparison_fst,← E.functor.map_comp,prod.lift_fst]
  · simp only [Category.assoc,prodComparison_snd,← E.functor.map_comp,prod.lift_snd]

variable (V : C) (W : D) (e : E.functor.obj V ≅ W) (L : StableListAlgebra V)

theorem map_list_nil : E.functor.map L.algebra.nil = terminalComparison E.functor ≫
    (mappedStableListAlgebra E V W e L).algebra.nil := by
  change E.functor.map L.algebra.nil = terminalComparison E.functor ≫
    (inv (terminalComparison E.functor) ≫ E.functor.map L.algebra.nil)
  simp only [IsIso.hom_inv_id_assoc]

theorem map_list_cons : E.functor.map L.algebra.cons =
    prodComparison E.functor V L.algebra.carrier ≫ prod.map e.hom (𝟙 _) ≫
      (mappedStableListAlgebra E V W e L).algebra.cons := by
  change E.functor.map L.algebra.cons = prodComparison E.functor V L.algebra.carrier ≫
    prod.map e.hom (𝟙 _) ≫ (prod.map e.inv (𝟙 _) ≫
      inv (prodComparison E.functor V L.algebra.carrier) ≫ E.functor.map L.algebra.cons)
  simp only [prod.map_map_assoc,e.hom_inv_id,Category.id_comp,
    prod.map_id_id,IsIso.hom_inv_id_assoc]

/-- The singleton comparison is derived from the actual nil/cons
diagrams, including the terminal comparison. -/
theorem map_list_singleton : E.functor.map L.singleton = e.hom ≫
    (mappedStableListAlgebra E V W e L).singleton := by
  let R := mappedStableListAlgebra E V W e L
  let s := prod.lift (𝟙 V) (terminal.from V ≫ L.algebra.nil)
  let t := prod.lift (𝟙 W) (terminal.from W ≫ R.algebra.nil)
  have ht : E.functor.map (terminal.from V) ≫ terminalComparison E.functor =
      terminal.from (E.functor.obj V) := terminalIsTerminal.hom_ext _ _
  have hp : E.functor.map s ≫ prodComparison E.functor V L.algebra.carrier ≫
      prod.map e.hom (𝟙 _) = e.hom ≫ t := by
    rw [← Category.assoc,list_map_lift,prod.lift_map]
    apply prod.hom_ext
    · simp [t]
      erw [prod.lift_fst]
    · simp only [prod.lift_snd,Category.comp_id]
      rw [E.functor.map_comp,map_list_nil E V W e L,← Category.assoc,ht]
      simp [t]
      erw [prod.lift_snd]
  change E.functor.map (s ≫ L.algebra.cons) = e.hom ≫ (t ≫ R.algebra.cons)
  rw [E.functor.map_comp,map_list_cons E V W e L]
  simpa only [Category.assoc] using congrArg (fun f => f ≫ R.algebra.cons) hp

section Step
variable {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (X Y : C) (X' Y' : D) (i : E.functor.obj X ≅ X') (j : E.functor.obj Y ≅ Y')

def listStepComparison :
    (sliceEquivalence E b).functor.obj (constantFamily P X ⨯ constantFamily P Y) ≅
      constantFamily Q X' ⨯ constantFamily Q Y' :=
  asIso (prodComparison (sliceEquivalence E b).functor (constantFamily P X) (constantFamily P Y)) ≪≫
    prod.mapIso (coefficientComparison E b X X' i) (coefficientComparison E b Y Y' j)

omit [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D] in
private theorem slice_map_left {A B : Over P} (f : A ⟶ B) :
    ((sliceEquivalence E b).functor.map f).left = E.functor.map f.left := rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem listStepComparison_parameter :
    (listStepComparison E b X Y X' Y' i j).hom.left ≫
      (constantFamily Q X' ⨯ constantFamily Q Y').hom =
      E.functor.map (constantFamily P X ⨯ constantFamily P Y).hom ≫ b.hom := by
  exact Over.w (listStepComparison E b X Y X' Y' i j).hom

omit [FinitaryExtensive C] [FinitaryExtensive D] in
private theorem listStepComparison_fst :
    (listStepComparison E b X Y X' Y' i j).hom ≫
      (prod.fst : constantFamily Q X' ⨯ constantFamily Q Y' ⟶ constantFamily Q X') =
    (sliceEquivalence E b).functor.map
      (prod.fst : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P X) ≫
      (coefficientComparison E b X X' i).hom := by
  change (prodComparison (sliceEquivalence E b).functor (constantFamily P X) (constantFamily P Y) ≫
    prod.map (coefficientComparison E b X X' i).hom (coefficientComparison E b Y Y' j).hom) ≫
      prod.fst = _
  simp only [Category.assoc,prod.map_fst,prodComparison_fst_assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
private theorem listStepComparison_snd :
    (listStepComparison E b X Y X' Y' i j).hom ≫
      (prod.snd : constantFamily Q X' ⨯ constantFamily Q Y' ⟶ constantFamily Q Y') =
    (sliceEquivalence E b).functor.map
      (prod.snd : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P Y) ≫
      (coefficientComparison E b Y Y' j).hom := by
  change (prodComparison (sliceEquivalence E b).functor (constantFamily P X) (constantFamily P Y) ≫
    prod.map (coefficientComparison E b X X' i).hom (coefficientComparison E b Y Y' j).hom) ≫
      prod.snd = _
  simp only [Category.assoc,prod.map_snd,prodComparison_snd_assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem listStepComparison_head :
    (listStepComparison E b X Y X' Y' i j).hom.left ≫ listStepHead Q X' Y' =
      E.functor.map (listStepHead P X Y) ≫ i.hom := by
  have hp : (listStepComparison E b X Y X' Y' i j).hom.left ≫
      (prod.fst : constantFamily Q X' ⨯ constantFamily Q Y' ⟶ constantFamily Q X').left =
      E.functor.map (prod.fst : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P X).left ≫
        (coefficientComparison E b X X' i).hom.left := by
    simpa only [Over.comp_left,slice_map_left] using congrArg Over.Hom.left
      (listStepComparison_fst E b X Y X' Y' i j)
  calc
    _ = ((listStepComparison E b X Y X' Y' i j).hom.left ≫
        (prod.fst : constantFamily Q X' ⨯ constantFamily Q Y' ⟶ constantFamily Q X').left) ≫
          prod.snd := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ prod.snd) hp
    _ = E.functor.map (prod.fst : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P X).left ≫
        (E.functor.map (prod.snd : P ⨯ X ⟶ X) ≫ i.hom) := by
      rw [Category.assoc,coefficientComparison_snd]
    _ = _ := by simp only [listStepHead,constantFamily,Functor.map_comp,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem listStepComparison_value :
    (listStepComparison E b X Y X' Y' i j).hom.left ≫ listStepValue Q X' Y' =
      E.functor.map (listStepValue P X Y) ≫ j.hom := by
  have hp : (listStepComparison E b X Y X' Y' i j).hom.left ≫
      (prod.snd : constantFamily Q X' ⨯ constantFamily Q Y' ⟶ constantFamily Q Y').left =
      E.functor.map (prod.snd : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P Y).left ≫
        (coefficientComparison E b Y Y' j).hom.left := by
    simpa only [Over.comp_left,slice_map_left] using congrArg Over.Hom.left
      (listStepComparison_snd E b X Y X' Y' i j)
  calc
    _ = ((listStepComparison E b X Y X' Y' i j).hom.left ≫
        (prod.snd : constantFamily Q X' ⨯ constantFamily Q Y' ⟶ constantFamily Q Y').left) ≫
          prod.snd := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ prod.snd) hp
    _ = E.functor.map (prod.snd : constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P Y).left ≫
        (E.functor.map (prod.snd : P ⨯ Y ⟶ Y) ≫ j.hom) := by
      rw [Category.assoc,coefficientComparison_snd]
    _ = _ := by simp only [listStepValue,constantFamily,Functor.map_comp,Category.assoc]

end Step

/-- Both the tested parameter and the cons head are transported by the
same variable isomorphism. The equality classifier follows from its
diagonal pullback, independently of the target's chosen equality data. -/
theorem listStepComparison_test {Y : C} {Y' : D} (j : E.functor.obj Y ≅ Y')
    (S : DecidableVariables V) (T : DecidableVariables W) :
    (listStepComparison E e V Y W Y' e j).hom.left ≫
      (prod.lift (constantFamily W W ⨯ constantFamily W Y').hom
        (listStepHead W W Y') ≫ T.test) =
    E.functor.map (prod.lift (constantFamily V V ⨯ constantFamily V Y).hom
      (listStepHead V V Y) ≫ S.test) ≫
        (DecidableVariables.Transport.booleanIso E).hom := by
  let k := listStepComparison E e V Y W Y' e j
  let a := prod.lift (constantFamily V V ⨯ constantFamily V Y).hom (listStepHead V V Y)
  let a' := prod.lift (constantFamily W W ⨯ constantFamily W Y').hom (listStepHead W W Y')
  have h : k.hom.left ≫ a' = E.functor.map a ≫
      (DecidableVariables.Transport.productIso E V W e).hom := by
    change k.hom.left ≫ prod.lift (constantFamily W W ⨯ constantFamily W Y').hom
      (listStepHead W W Y') = _
    rw [prod.comp_lift,listStepComparison_parameter,listStepComparison_head]
    change prod.lift
        (E.functor.map (constantFamily V V ⨯ constantFamily V Y).hom ≫ e.hom)
        (E.functor.map (listStepHead V V Y) ≫ e.hom) =
      E.functor.map a ≫
        (prodComparison E.functor V V ≫ prod.map e.hom e.hom)
    rw [← Category.assoc,list_map_lift,prod.lift_map]
  change k.hom.left ≫ (a' ≫ T.test) = E.functor.map (a ≫ S.test) ≫ _
  rw [← Category.assoc,h,Category.assoc,← map_decidable_test E S W e T,
    ← Category.assoc,← E.functor.map_comp]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
