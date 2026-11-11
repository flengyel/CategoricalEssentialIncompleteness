/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalListOperations
public import CategoricalEssentialIncompleteness.V46CategoricalListLawsParameters

/-! # Parameter recursion and identities for categorical lists -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D]

namespace StableListAlgebra

variable [HasFiniteCoproducts D]
variable {V : D} (L : StableListAlgebra V)

/-- A list algebra with parameter object `P`, written in base-category
coordinates. -/
def parameterAlgebra {P X : D} (n : P ⟶ X) (c : P ⨯ (V ⨯ X) ⟶ X) :
    ListAlgebra (constantFamily P V) where
  carrier := constantFamily P X
  nil := Over.homMk (prod.lift (⊤_ (Over P)).hom
    ((⊤_ (Over P)).hom ≫ n)) (by simp [constantFamily])
  cons := Over.homMk (prod.lift
    (constantFamily P V ⨯ constantFamily P X).hom
    (prod.lift (constantFamily P V ⨯ constantFamily P X).hom
      (prod.lift (listStepHead P V X) (listStepValue P V X)) ≫ c))
    (by simp [constantFamily])

def parameterFold {P X : D} (n : P ⟶ X) (c : P ⨯ (V ⨯ X) ⟶ X) :
    P ⨯ L.algebra.carrier ⟶ X :=
  (L.foldWithParameters P (parameterAlgebra (V := V) n c)).left ≫ prod.snd

def parameterNil (P : D) : P ⟶ P ⨯ L.algebra.carrier :=
  prod.lift (𝟙 P) (terminal.from P ≫ L.algebra.nil)

def parameterCons (P : D) :
    P ⨯ (V ⨯ L.algebra.carrier) ⟶ P ⨯ L.algebra.carrier :=
  prod.map (𝟙 P) L.algebra.cons

def parameterRec {P X : D} (f : P ⨯ L.algebra.carrier ⟶ X) :
    P ⨯ (V ⨯ L.algebra.carrier) ⟶ P ⨯ (V ⨯ X) :=
  prod.lift prod.fst
    (prod.lift (prod.snd ≫ prod.fst)
      (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f))

theorem parameterFold_nil {P X : D} (n : P ⟶ X)
    (c : P ⨯ (V ⨯ X) ⟶ X) :
    L.parameterNil P ≫ L.parameterFold n c = n := by
  let f : constantFamily P L.algebra.carrier ⟶ constantFamily P X :=
    L.foldWithParameters P (parameterAlgebra (V := V) n c)
  let j : Over.mk (𝟙 P) ⟶ ⊤_ (Over P) := terminal.from _
  have h : prod.lift (⊤_ (Over P)).hom
      (terminal.from (⊤_ (Over P)).left ≫ L.algebra.nil) ≫ f.left =
      prod.lift (⊤_ (Over P)).hom ((⊤_ (Over P)).hom ≫ n) :=
    congrArg Over.Hom.left (L.foldWithParameters_nil P (parameterAlgebra (V := V) n c))
  have hh := congrArg (fun k => j.left ≫ k ≫ prod.snd) h
  have hj : j.left ≫ (⊤_ (Over P)).hom = 𝟙 P := Over.w j
  have hn : j.left ≫ prod.lift (⊤_ (Over P)).hom
      (terminal.from (⊤_ (Over P)).left ≫ L.algebra.nil) = L.parameterNil P := by
    rw [prod.comp_lift, hj, ← Category.assoc, terminal.comp_from]
    rfl
  simp only [← Category.assoc] at hh
  rw [hn] at hh
  simp only [Category.assoc, prod.lift_snd] at hh
  rw [← Category.assoc j.left, hj] at hh
  change L.parameterNil P ≫ L.parameterFold n c = 𝟙 P ≫ n at hh
  simpa only [Category.id_comp] using hh

theorem parameterStep_cons (P : D) :
    (parameterStep P V L.algebra.carrier).left ≫
      (L.algebra.withParameters P).cons.left = L.parameterCons P := by
  change (parameterStep P V L.algebra.carrier).left ≫
    prod.lift (constantFamily P V ⨯ constantFamily P L.algebra.carrier).hom
      (prod.lift (listStepHead P V L.algebra.carrier)
        (listStepValue P V L.algebra.carrier) ≫ L.algebra.cons) = _
  rw [prod.comp_lift, parameterStep_base, ← Category.assoc, prod.comp_lift,
    parameterStep_head, parameterStep_value]
  apply prod.hom_ext
  · simp [parameterCons]
  · have he : prod.lift
        ((prod.snd : P ⨯ (V ⨯ L.algebra.carrier) ⟶ _) ≫ prod.fst)
        (prod.snd ≫ prod.snd) = prod.snd := by
      apply prod.hom_ext <;> simp
    simp only [prod.lift_snd, parameterCons, prod.map_snd]
    rw [he]

theorem parameterFold_cons {P X : D} (n : P ⟶ X)
    (c : P ⨯ (V ⨯ X) ⟶ X) :
    L.parameterCons P ≫ L.parameterFold n c =
      L.parameterRec (L.parameterFold n c) ≫ c := by
  let f : constantFamily P L.algebra.carrier ⟶ constantFamily P X :=
    L.foldWithParameters P (parameterAlgebra (V := V) n c)
  let j := parameterStep P V L.algebra.carrier
  let sc := (L.algebra.withParameters P).cons.left
  let tc := (parameterAlgebra (V := V) n c).cons.left
  have h : sc ≫ f.left = (prod.map (𝟙 (constantFamily P V)) f).left ≫ tc :=
    congrArg Over.Hom.left (L.foldWithParameters_cons P (parameterAlgebra (V := V) n c))
  have hh := congrArg (fun k => j.left ≫ k ≫ prod.snd) h
  have hj : j.left ≫ (L.algebra.withParameters P).cons.left = L.parameterCons P :=
    L.parameterStep_cons P
  have hbase :
      (j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫
        (constantFamily P V ⨯ constantFamily P X).hom = prod.fst := Over.w _
  have hhead :
      (j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫ listStepHead P V X =
        (prod.snd : P ⨯ (V ⨯ L.algebra.carrier) ⟶ _) ≫ prod.fst := by
    calc
      _ = ((j ≫ prod.map (𝟙 (constantFamily P V)) f) ≫
          (prod.fst : constantFamily P V ⨯ constantFamily P X ⟶ _)).left ≫ prod.snd :=
        (Category.assoc _ _ _).symm
      _ = (j ≫ (prod.fst : constantFamily P V ⨯
          constantFamily P L.algebra.carrier ⟶ _)).left ≫ prod.snd := by
        rw [Category.assoc, prod.map_fst, Category.comp_id]
      _ = _ := by
        simpa only [Over.comp_left, Category.assoc, listStepHead] using
          parameterStep_head P V L.algebra.carrier
  have hvalue :
      (j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫ listStepValue P V X =
        prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ L.parameterFold n c := by
    calc
      _ = ((j ≫ prod.map (𝟙 (constantFamily P V)) f) ≫
          (prod.snd : constantFamily P V ⨯ constantFamily P X ⟶ _)).left ≫ prod.snd :=
        (Category.assoc _ _ _).symm
      _ = ((j ≫ (prod.snd : constantFamily P V ⨯
          constantFamily P L.algebra.carrier ⟶ _)) ≫ f).left ≫ prod.snd := by
        rw [Category.assoc, prod.map_snd, ← Category.assoc]
      _ = _ := by
        change ((prod.lift _ _ ≫ prod.snd) ≫ f).left ≫ prod.snd = _
        rw [prod.lift_snd]
        simpa only [Over.comp_left, parameterHom, Over.homMk_left, parameterFold] using
          Category.assoc (prod.lift (prod.fst : P ⨯ (V ⨯ L.algebra.carrier) ⟶ P)
            (prod.snd ≫ prod.snd)) f.left (prod.snd : P ⨯ X ⟶ X)
  have hh' : (j.left ≫ sc) ≫ f.left ≫ prod.snd =
      (j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫ tc ≫ prod.snd := by
    simpa only [Over.comp_left, Category.assoc] using hh
  change j.left ≫ sc = L.parameterCons P at hj
  rw [hj] at hh'
  change L.parameterCons P ≫ L.parameterFold n c =
    (j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫
      (prod.lift (constantFamily P V ⨯ constantFamily P X).hom
        (prod.lift (constantFamily P V ⨯ constantFamily P X).hom
          (prod.lift (listStepHead P V X) (listStepValue P V X)) ≫ c)) ≫ prod.snd at hh'
  have hres :
      (j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫
        prod.lift (constantFamily P V ⨯ constantFamily P X).hom
          (prod.lift (listStepHead P V X) (listStepValue P V X)) =
        L.parameterRec (L.parameterFold n c) := by
    rw [prod.comp_lift, prod.comp_lift, hbase, hhead, hvalue]
    rfl
  calc
    _ = ((j ≫ prod.map (𝟙 (constantFamily P V)) f).left ≫
        prod.lift (constantFamily P V ⨯ constantFamily P X).hom
          (prod.lift (listStepHead P V X) (listStepValue P V X))) ≫ c := by
      simpa only [Category.assoc, prod.lift_snd] using hh'
    _ = _ := congrArg (fun k => k ≫ c) hres

theorem parameterFold_unique {P X : D} (n : P ⟶ X)
    (c : P ⨯ (V ⨯ X) ⟶ X) (f : P ⨯ L.algebra.carrier ⟶ X)
    (hn : L.parameterNil P ≫ f = n)
    (hc : L.parameterCons P ≫ f = L.parameterRec f ≫ c) :
    f = L.parameterFold n c := by
  have hf : parameterHom f =
      L.foldWithParameters P (parameterAlgebra (V := V) n c) := by
    apply L.foldWithParameters_unique P (parameterAlgebra (V := V) n c)
    · apply Over.OverMorphism.ext
      apply prod.hom_ext
      · exact (Over.w _).trans (Over.w _).symm
      · let e := Over.mkIdTerminal (X := P) |>.uniqueUpToIso
          (terminalIsTerminal : IsTerminal (⊤_ (Over P)))
        apply (cancel_epi e.hom.left).mp
        have he : e.hom.left ≫ (⊤_ (Over P)).hom = 𝟙 P := Over.w e.hom
        simp only [Over.comp_left, Category.assoc]
        change e.hom.left ≫
          prod.lift (⊤_ (Over P)).hom
            (terminal.from (⊤_ (Over P)).left ≫ L.algebra.nil) ≫
              (prod.lift prod.fst f) ≫ prod.snd =
          e.hom.left ≫ prod.lift (⊤_ (Over P)).hom ((⊤_ (Over P)).hom ≫ n) ≫ prod.snd
        simp only [prod.lift_snd]
        have hnil : e.hom.left ≫ prod.lift (⊤_ (Over P)).hom
            (terminal.from (⊤_ (Over P)).left ≫ L.algebra.nil) = L.parameterNil P := by
          rw [prod.comp_lift, he, ← Category.assoc, terminal.comp_from]
          rfl
        rw [← Category.assoc, hnil, hn, ← Category.assoc, he]
        simpa only [Over.mk_left] using (Category.id_comp n).symm
    · apply (cancel_epi (parameterStep P V L.algebra.carrier)).mp
      apply Over.OverMorphism.ext
      apply prod.hom_ext
      · exact (Over.w _).trans (Over.w _).symm
      · have hbase :
            (parameterStep P V L.algebra.carrier ≫
              prod.map (𝟙 (constantFamily P V)) (parameterHom f)).left ≫
              (constantFamily P V ⨯ constantFamily P X).hom = prod.fst := Over.w _
        have hl :
            (parameterStep P V L.algebra.carrier ≫
              (L.algebra.withParameters P).cons ≫ parameterHom f).left ≫ prod.snd =
              L.parameterCons P ≫ f := by
          simp only [Over.comp_left, parameterHom, Over.homMk_left, Category.assoc,
            prod.lift_snd]
          rw [← Category.assoc, L.parameterStep_cons]
        have hr :
            (parameterStep P V L.algebra.carrier ≫
              prod.map (𝟙 (constantFamily P V)) (parameterHom f) ≫
                (parameterAlgebra (V := V) n c).cons).left ≫ prod.snd =
              L.parameterRec f ≫ c := by
          rw [← Category.assoc, Over.comp_left]
          simp only [Category.assoc]
          change _ ≫ (prod.lift (constantFamily P V ⨯ constantFamily P X).hom
            (prod.lift (constantFamily P V ⨯ constantFamily P X).hom
              (prod.lift (listStepHead P V X) (listStepValue P V X)) ≫ c)) ≫ prod.snd = _
          simp only [prod.lift_snd]
          rw [← Category.assoc, prod.comp_lift, prod.comp_lift, hbase,
            parameterStep_map_head, parameterStep_map_value]
          simp only [parameterHom, Over.homMk_left, prod.lift_snd, parameterRec]
        exact hl.trans (hc.trans hr.symm)
  simpa only [parameterHom_value, parameterFold] using
    congrArg (fun k => k.left ≫ prod.snd) hf

end StableListAlgebra

section BooleanOperations

variable [FinitaryExtensive D]

attribute [local simp] prod.comp_lift_assoc prod.lift_fst_assoc prod.lift_snd_assoc
  prod.map_fst_assoc prod.map_snd_assoc

namespace DecidableVariables

variable {V : D} (E : DecidableVariables V)

theorem test_reflexive : prod.lift (𝟙 V) (𝟙 V) ≫ E.test = Two.constant V true :=
  E.diagonal.w

theorem test_true_iff {X : D} (f g : X ⟶ V) :
    prod.lift f g ≫ E.test = Two.constant X true ↔ f = g := by
  constructor
  · intro h
    let l := E.diagonal.lift (prod.lift f g) (terminal.from X) h
    have hpair : l ≫ prod.lift (𝟙 V) (𝟙 V) = prod.lift f g := E.diagonal.lift_fst _ _ h
    have hf : l = f := by
      simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using
        congrArg (fun k => k ≫ prod.fst) hpair
    have hg : l = g := by
      simpa only [Category.assoc, prod.lift_snd, Category.comp_id] using
        congrArg (fun k => k ≫ prod.snd) hpair
    exact hf.symm.trans hg
  · rintro rfl
    have h := congrArg (fun k => f ≫ k) E.test_reflexive
    simpa only [← Category.assoc, prod.comp_lift, prod.comp_lift_assoc, Category.comp_id,
      Two.comp_constant] using h

end DecidableVariables

@[reassoc] theorem branch_natural {X Y Z : D} (k : Z ⟶ X)
    (b : X ⟶ Two D) (f g : X ⟶ Y) :
    k ≫ Two.branch b f g = Two.branch (k ≫ b) (k ≫ f) (k ≫ g) := by
  apply Two.hom_ext (k ≫ b)
  · rw [← Category.assoc]
    rw [Two.comp_branch b f g (Two.fiberι (k ≫ b) false ≫ k) false
      (by simp [Category.assoc])]
    rw [Two.fiberι_branch]
    simp
  · rw [← Category.assoc]
    rw [Two.comp_branch b f g (Two.fiberι (k ≫ b) true ≫ k) true
      (by simp [Category.assoc])]
    rw [Two.fiberι_branch]
    simp

namespace StableListAlgebra

variable {V : D} (L : StableListAlgebra V) (E : DecidableVariables V)

def membershipStep : V ⨯ (V ⨯ Two D) ⟶ Two D :=
  Two.binary Bool.or (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ E.test)
    (prod.snd ≫ prod.snd)

theorem membershipAlgebra_eq_parameterAlgebra :
    membershipAlgebra E = parameterAlgebra (Two.constant V false) (membershipStep E) := by
  unfold membershipAlgebra parameterAlgebra membershipStep
  congr 1
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp [Two.comp_binary]

theorem membership_eq_parameterFold :
    L.membership E = L.parameterFold (Two.constant V false) (membershipStep E) := by
  have hf : L.membershipFold E = L.foldWithParameters V
      (parameterAlgebra (Two.constant V false) (membershipStep E)) := by
    refine L.foldWithParameters_unique V
      (parameterAlgebra (Two.constant V false) (membershipStep E)) (L.membershipFold E) ?_ ?_
    · rw [L.membershipFold_nil E]
      apply Over.OverMorphism.ext
      apply prod.hom_ext <;> simp [membershipAlgebra, parameterAlgebra]
    · rw [L.membershipFold_cons E]
      congr 1
      apply Over.OverMorphism.ext
      apply prod.hom_ext <;>
        simp [membershipAlgebra, parameterAlgebra, membershipStep, Two.comp_binary]
  exact congrArg (fun k => k.left ≫ prod.snd) hf

theorem membership_cons :
    prod.map (𝟙 V) L.algebra.cons ≫ L.membership E =
      Two.binary Bool.or (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ E.test)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ L.membership E) := by
  have h := L.parameterFold_cons (Two.constant V false) (membershipStep E)
  rw [← membership_eq_parameterFold] at h
  simpa [parameterCons, parameterRec, membershipStep, Two.comp_binary,
    prod.comp_lift, prod.comp_lift_assoc, Category.assoc] using h

@[simp] theorem membership_nil_general {X : D} (x : X ⟶ V) :
    prod.lift x (terminal.from X ≫ L.algebra.nil) ≫ L.membership E =
      Two.constant X false := by
  simpa [prod.comp_lift, prod.comp_lift_assoc, Category.assoc] using
    congrArg (fun k => x ≫ k) (L.membership_nil E)

@[simp] theorem membership_cons_general {X : D} (x y : X ⟶ V)
    (w : X ⟶ L.algebra.carrier) :
    prod.lift x (prod.lift y w ≫ L.algebra.cons) ≫ L.membership E =
      Two.binary Bool.or (prod.lift x y ≫ E.test)
        (prod.lift x w ≫ L.membership E) := by
  simpa [prod.comp_lift, prod.comp_lift_assoc, Category.assoc, Two.comp_binary] using
    congrArg (fun k => prod.lift x (prod.lift y w) ≫ k) (L.membership_cons E)

@[simp] theorem membership_cons_arrow {X : D} (x : X ⟶ V)
    (p : X ⟶ V ⨯ L.algebra.carrier) :
    prod.lift x (p ≫ L.algebra.cons) ≫ L.membership E =
      Two.binary Bool.or (prod.lift x (p ≫ prod.fst) ≫ E.test)
        (prod.lift x (p ≫ prod.snd) ≫ L.membership E) := by
  simpa using L.membership_cons_general E x (p ≫ prod.fst) (p ≫ prod.snd)

theorem appendAlgebra_eq_parameterAlgebra :
    L.appendAlgebra =
      parameterAlgebra (𝟙 L.algebra.carrier) (prod.snd ≫ L.algebra.cons) := by
  unfold appendAlgebra parameterAlgebra ListAlgebra.withParameters
  congr 1
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp [listStepHead, listStepValue]

def appendParameterValue : L.algebra.carrier ⨯ L.algebra.carrier ⟶ L.algebra.carrier :=
  L.appendWithParameter.left ≫ prod.snd

theorem appendParameterValue_eq_parameterFold :
    L.appendParameterValue = L.parameterFold (𝟙 L.algebra.carrier)
      (prod.snd ≫ L.algebra.cons) := by
  have hf : L.appendWithParameter = L.foldWithParameters L.algebra.carrier
      (parameterAlgebra (𝟙 L.algebra.carrier) (prod.snd ≫ L.algebra.cons)) := by
    refine L.foldWithParameters_unique L.algebra.carrier
      (parameterAlgebra (𝟙 L.algebra.carrier) (prod.snd ≫ L.algebra.cons))
      L.appendWithParameter ?_ ?_
    · rw [L.appendWithParameter_nil]
      apply Over.OverMorphism.ext
      apply prod.hom_ext <;> simp [appendAlgebra, parameterAlgebra]
    · rw [L.appendWithParameter_cons]
      congr 1
      apply Over.OverMorphism.ext
      apply prod.hom_ext <;>
        simp [ListAlgebra.withParameters, parameterAlgebra, listStepHead, listStepValue]
  exact congrArg (fun k => k.left ≫ prod.snd) hf

@[simp] theorem appendParameterValue_nil {X : D} (w : X ⟶ L.algebra.carrier) :
    prod.lift w (terminal.from X ≫ L.algebra.nil) ≫ L.appendParameterValue = w := by
  have h := L.parameterFold_nil (𝟙 L.algebra.carrier) (prod.snd ≫ L.algebra.cons)
  rw [← appendParameterValue_eq_parameterFold] at h
  simpa [parameterNil, prod.comp_lift, prod.comp_lift_assoc, Category.assoc] using
    congrArg (fun k => w ≫ k) h

@[simp] theorem appendParameterValue_cons {X : D}
    (w : X ⟶ L.algebra.carrier) (y : X ⟶ V) (t : X ⟶ L.algebra.carrier) :
    prod.lift w (prod.lift y t ≫ L.algebra.cons) ≫ L.appendParameterValue =
      prod.lift y (prod.lift w t ≫ L.appendParameterValue) ≫ L.algebra.cons := by
  have h := L.parameterFold_cons (𝟙 L.algebra.carrier) (prod.snd ≫ L.algebra.cons)
  rw [← appendParameterValue_eq_parameterFold] at h
  simpa [parameterCons, parameterRec, prod.comp_lift, prod.comp_lift_assoc, Category.assoc] using
    congrArg (fun k => prod.lift w (prod.lift y t) ≫ k) h

@[simp] theorem appendParameterValue_map_cons {P : D} (f : P ⟶ L.algebra.carrier) :
    prod.map f L.algebra.cons ≫ L.appendParameterValue =
      prod.lift (prod.snd ≫ prod.fst)
        (prod.map f prod.snd ≫ L.appendParameterValue) ≫ L.algebra.cons := by
  simpa using L.appendParameterValue_cons (prod.fst ≫ f)
    (prod.snd ≫ prod.fst) (prod.snd ≫ prod.snd)

/-- Membership of a concatenation is the disjunction of its two
membership predicates. The source coordinates are `(x,w',w)`, with
`w'` the fixed right-hand list. -/
theorem membership_append_parameter :
    prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ L.appendParameterValue) ≫
      L.membership E =
      Two.binary Bool.or
        (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ L.membership E)
        ((prod.fst : (V ⨯ L.algebra.carrier) ⨯ L.algebra.carrier ⟶ _) ≫ L.membership E) := by
  let n := L.membership E
  let c : (V ⨯ L.algebra.carrier) ⨯ (V ⨯ Two D) ⟶ Two D :=
    Two.binary Bool.or (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.fst) ≫ E.test)
      (prod.snd ≫ prod.snd)
  let f : (V ⨯ L.algebra.carrier) ⨯ L.algebra.carrier ⟶ Two D :=
    prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ L.appendParameterValue) ≫ L.membership E
  let g : (V ⨯ L.algebra.carrier) ⨯ L.algebra.carrier ⟶ Two D :=
    Two.binary Bool.or
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ L.membership E)
      (prod.fst ≫ L.membership E)
  change f = g
  have hf : f = L.parameterFold n c := by
    apply L.parameterFold_unique n c f
    · simp [f, n, parameterNil]
    · simp [f, c, parameterCons, parameterRec, Two.comp_binary]
  have hg : g = L.parameterFold n c := by
    apply L.parameterFold_unique n c g
    · suffices h : Two.binary Bool.or (Two.constant (V ⨯ L.algebra.carrier) false)
          (L.membership E) = n by
        simpa [g, parameterNil] using h
      exact bot_sup_eq _
    · simpa [g, c, parameterCons, parameterRec, Two.comp_binary,
        -prod.lift_fst_comp_snd_comp] using
        (Two.binary_assoc (C := D) Bool.or (by decide)
          (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.fst) ≫ E.test :
            (V ⨯ L.algebra.carrier) ⨯ (V ⨯ L.algebra.carrier) ⟶ Two D)
          (prod.lift (prod.fst ≫ prod.fst) (prod.snd ≫ prod.snd) ≫ L.membership E)
          (prod.fst ≫ L.membership E))
  exact hf.trans hg.symm

/-- The concatenation identity with arbitrary generalized elements,
in the manuscript order `(x,w,w')`. -/
theorem membership_append {X : D} (x : X ⟶ V)
    (w w' : X ⟶ L.algebra.carrier) :
    prod.lift x (prod.lift w w' ≫ L.append) ≫ L.membership E =
      Two.binary Bool.or (prod.lift x w ≫ L.membership E)
        (prod.lift x w' ≫ L.membership E) := by
  simpa [append, appendParameterValue, prod.comp_lift, prod.comp_lift_assoc, Category.assoc,
    Two.comp_binary] using
    congrArg (fun k => prod.lift (prod.lift x w') w ≫ k) (L.membership_append_parameter E)

def deletionStep : V ⨯ (V ⨯ L.algebra.carrier) ⟶ L.algebra.carrier :=
  Two.branch (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ E.test)
    (prod.snd ≫ L.algebra.cons) (prod.snd ≫ prod.snd)

theorem deletionAlgebra_eq_parameterAlgebra :
    L.deletionAlgebra E =
      parameterAlgebra (terminal.from V ≫ L.algebra.nil) (L.deletionStep E) := by
  unfold deletionAlgebra parameterAlgebra deletionStep
  congr 1
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;> simp
  · apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [branch_natural]

theorem deletion_eq_parameterFold :
    L.deletion E = L.parameterFold
      (terminal.from V ≫ L.algebra.nil) (L.deletionStep E) := by
  have hf : L.deletionFold E = L.foldWithParameters V
      (parameterAlgebra (terminal.from V ≫ L.algebra.nil) (L.deletionStep E)) := by
    refine L.foldWithParameters_unique V
      (parameterAlgebra (terminal.from V ≫ L.algebra.nil) (L.deletionStep E))
      (L.deletionFold E) ?_ ?_
    · rw [L.deletionFold_nil E]
      apply Over.OverMorphism.ext
      apply prod.hom_ext <;> simp [deletionAlgebra, parameterAlgebra]
    · rw [L.deletionFold_cons E]
      congr 1
      apply Over.OverMorphism.ext
      apply prod.hom_ext <;>
        simp [deletionAlgebra, parameterAlgebra, deletionStep, branch_natural]
  exact congrArg (fun k => k.left ≫ prod.snd) hf

theorem deletion_cons :
    prod.map (𝟙 V) L.algebra.cons ≫ L.deletion E =
      Two.branch (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ E.test)
        (prod.lift (prod.snd ≫ prod.fst)
          (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ L.deletion E) ≫ L.algebra.cons)
        (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ L.deletion E) := by
  have h := L.parameterFold_cons
    (terminal.from V ≫ L.algebra.nil) (L.deletionStep E)
  rw [← deletion_eq_parameterFold] at h
  simpa [parameterCons, parameterRec, deletionStep, branch_natural,
    prod.comp_lift, prod.comp_lift_assoc, Category.assoc] using h

end StableListAlgebra

end BooleanOperations

end CategoricalEssentialIncompleteness.V46
