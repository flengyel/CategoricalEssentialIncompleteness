/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation
public import CategoricalEssentialIncompleteness.V46NumericalUnderlyingCoproducts
public import CategoricalEssentialIncompleteness.ForkNumericalProofs
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.Tactic.FinCases

/-! # The six-tag fork proof carrier as an inference algebra

The coefficient predicates occur only in the positive and negative leaf
objects. The binary input is the original ordered-premise pullback. The
comparison with the constructed numerical initial algebra is obtained from
its fold and Lambek decomposition; no universal property of the old tree
carrier is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Component
open ForkSyntax
open NumericalTuples

def firstPoint {X Y : Object} (x : Point (X ⨯ Y)) : Point X :=
  (prod.fst : X ⨯ Y ⟶ X).toFun x

def secondPoint {X Y : Object} (x : Point (X ⨯ Y)) : Point Y :=
  (prod.snd : X ⨯ Y ⟶ Y).toFun x

/-- A literal unary carrier; its scalar coordinates are the original codes. -/
def scalarObject (C : Set ℕ) (hC : REPred (· ∈ C)) : Object := ⟨1,C,hC⟩

def formulaObject : Object := scalarObject Set.univ (REPred.const True)

def formulaPoint (p : Formula) : Point formulaObject := ⟨p.encode,Set.mem_univ _⟩

def formulaAt (x : Point formulaObject) : Formula := Formula.decode x.val

@[simp] theorem formulaAt_encode (x : Point formulaObject) : (formulaAt x).encode = x.val :=
  Formula.encode_decode x.val

@[simp] theorem formulaAt_point (p : Formula) : formulaAt (formulaPoint p) = p :=
  Formula.decode_encode p

@[simp] theorem formulaPoint_at (x : Point formulaObject) : formulaPoint (formulaAt x) = x := by
  apply Subtype.ext
  exact Formula.encode_decode x.val

/-- A fixed scalar algorithm on unary inputs. -/
def scalarMap {C D : Set ℕ} (hC : REPred (· ∈ C)) (hD : REPred (· ∈ D))
    (f : ℕ → ℕ) (hf : Computable f) (hs : ∀ n ∈ C,f n ∈ D) :
    scalarObject C hC ⟶ scalarObject D hD where
  toFun x := ⟨f x.val,hs _ x.property⟩
  represented := ⟨fun n => Part.some (f n),hf.partrec,fun _ => rfl⟩

/-- Two represented scalar observations can be combined by a fixed
computable scalar algorithm. No value outside the input carrier is used. -/
def scalarCombine {X : Object} (f g : X ⟶ formulaObject)
    (h : ℕ × ℕ → ℕ) (hh : Computable h) : X ⟶ formulaObject where
  toFun x := ⟨h ((f.toFun x).val,(g.toFun x).val),Set.mem_univ _⟩
  represented := by
    obtain ⟨p,hp,hf⟩ := f.represented
    obtain ⟨q,hq,hg⟩ := g.represented
    refine ⟨fun z => (p z).bind (fun a => (q z).map (fun b => h (a,b))),
      hp.bind ((hq.comp Computable.fst).map
        (hh.comp (Computable.pair (Computable.snd.comp Computable.fst)
          Computable.snd)).to₂).to₂,?_⟩
    intro x
    change (p x.val).bind (fun a : ℕ => (q x.val).map (fun b : ℕ => h (a,b))) = _
    erw [hf x,Part.bind_some,hg x]
    rfl

@[simp] theorem scalarCombine_value {X : Object} (f g : X ⟶ formulaObject)
    (h : ℕ × ℕ → ℕ) (hh : Computable h) (x : Point X) :
    ((scalarCombine f g h hh).toFun x).val =
      h ((f.toFun x).val,(g.toFun x).val) := rfl

def scalarUnary {X : Object} (f : X ⟶ formulaObject)
    (h : ℕ → ℕ) (hh : Computable h) : X ⟶ formulaObject :=
  f ≫ scalarMap (REPred.const True) (REPred.const True) h hh
    (fun _ _ => Set.mem_univ _)

def formulaBinary (f : Formula × Formula → Formula) (hf : Computable f) :
    formulaObject ⨯ formulaObject ⟶ formulaObject :=
  scalarCombine prod.fst prod.snd
    (fun n => (f (Formula.decode n.1,Formula.decode n.2)).encode)
    (Formula.encode_computable.comp (hf.comp
      ((Formula.decode_computable.comp Computable.fst).pair
        (Formula.decode_computable.comp Computable.snd))))

def implication : formulaObject ⨯ formulaObject ⟶ formulaObject :=
  formulaBinary (fun p => .imp p.1 p.2)
    (Formula.imp_computable.comp (Computable.fst.pair Computable.snd))

@[simp] theorem implication_value (x : Point (formulaObject ⨯ formulaObject)) :
    (implication.toFun x).val =
      (Formula.imp (formulaAt (firstPoint x)) (formulaAt (secondPoint x))).encode := rfl

theorem implication_formulaAt (x : Point (formulaObject ⨯ formulaObject)) :
    formulaAt (implication.toFun x) = .imp (formulaAt (firstPoint x)) (formulaAt (secondPoint x)) :=
  (congrArg Formula.decode (implication_value x)).trans (Formula.decode_encode _)

variable (A B : Set ℕ) (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))

def positiveObject : Object := scalarObject A hA
def negativeObject : Object := scalarObject B hB

/-- This is the old carrier, on its original six-tag word. -/
def proofObject : Object := NumericalTuples.unary
  ⟨ForkSyntax.proofCarrier A B hA hB⟩

theorem proofObject_mem (n : ℕ) :
    n ∈ (proofObject A B hA hB).support ↔ ProofTree.Valid A B (ProofTree.decode n) :=
  ForkSyntax.mem_proofCarrier A B hA hB n

def proofPoint (t : ProofTree) (ht : ProofTree.Valid A B t) :
    Point (proofObject A B hA hB) :=
  ⟨t.encode,(proofObject_mem A B hA hB _).mpr (by rw [ProofTree.decode_encode]; exact ht)⟩

@[simp] theorem proofPoint_value (t : ProofTree) (ht : ProofTree.Valid A B t) :
    (proofPoint A B hA hB t ht).val = t.encode := rfl

def proofAt (x : Point (proofObject A B hA hB)) : ProofTree := ProofTree.decode x.val

@[simp] theorem proofAt_point (t : ProofTree) (ht : ProofTree.Valid A B t) :
    proofAt A B hA hB (proofPoint A B hA hB t ht) = t := ProofTree.decode_encode t

@[simp] theorem proofAt_encode (x : Point (proofObject A B hA hB)) :
    (proofAt A B hA hB x).encode = x.val := ProofTree.encode_decode x.val

theorem proofAt_valid (x : Point (proofObject A B hA hB)) :
    ProofTree.Valid A B (proofAt A B hA hB x) :=
  (proofObject_mem A B hA hB x.val).mp x.property

@[simp] theorem proofPoint_at (x : Point (proofObject A B hA hB)) :
    proofPoint A B hA hB (proofAt A B hA hB x) (proofAt_valid A B hA hB x) = x := by
  apply Subtype.ext
  exact ProofTree.encode_decode x.val

def conclusion : proofObject A B hA hB ⟶ formulaObject :=
  scalarMap (ForkSyntax.proofCarrier A B hA hB).enumerable (REPred.const True)
    ForkSyntax.conclusionCode ForkSyntax.conclusionCode_computable
      (fun _ _ => Set.mem_univ _)

theorem conclusion_value (x : Point (proofObject A B hA hB)) :
    ((conclusion A B hA hB).toFun x).val = ForkSyntax.conclusionCode x.val := rfl

theorem proofPoint_conclusion {t : ProofTree} {p : Formula} (ht : Concludes A B t p) :
    ((conclusion A B hA hB).toFun (proofPoint A B hA hB t ⟨p,ht⟩)).val = p.encode :=
  ForkSyntax.conclusionCode_of_concludes ht

theorem proofAt_concludes (x : Point (proofObject A B hA hB)) :
    Concludes A B (proofAt A B hA hB x)
      (formulaAt ((conclusion A B hA hB).toFun x)) := by
  obtain ⟨p,hp⟩ := proofAt_valid A B hA hB x
  have he := ForkSyntax.conclusionCode_of_concludes hp
  change ForkSyntax.conclusionCode (ProofTree.decode x.val).encode = p.encode at he
  erw [ProofTree.encode_decode] at he
  simpa only [formulaAt,conclusion_value,he,Formula.decode_encode] using hp

/-- Corestriction retains the supplied fixed code algorithm. -/
def proofFromCode {X : Object} (t : Point X → ProofTree)
    (ht : ∀ x,ProofTree.Valid A B (t x)) (f : X ⟶ formulaObject)
    (hf : ∀ x,(f.toFun x).val = (t x).encode) : X ⟶ proofObject A B hA hB where
  toFun x := proofPoint A B hA hB (t x) (ht x)
  represented := by
    obtain ⟨p,hp,hp'⟩ := f.represented
    exact ⟨p,hp,fun x => (hp' x).trans (congrArg Part.some (hf x))⟩

def axiomFamily : Fin 5 → Object :=
  ![finitePower formulaObject 2,finitePower formulaObject 3,finitePower formulaObject 2,
    positiveObject A hA,negativeObject B hB]

def axiomObject : Object := ∐ axiomFamily A B hA hB

def logical1Tree (x : Point (finitePower formulaObject 2)) : ProofTree :=
  .logical1 (formulaAt (firstPoint x)) (formulaAt (secondPoint x))

def logical2Tree (x : Point (finitePower formulaObject 3)) : ProofTree :=
  .logical2 (formulaAt (firstPoint (firstPoint x)))
    (formulaAt (secondPoint (firstPoint x))) (formulaAt (secondPoint x))

def logical3Tree (x : Point (finitePower formulaObject 2)) : ProofTree :=
  .logical3 (formulaAt (firstPoint x)) (formulaAt (secondPoint x))

def pairCodes {X : Object} (f g : X ⟶ formulaObject) : X ⟶ formulaObject :=
  scalarCombine f g (fun n => Nat.pair n.1 n.2) Primrec₂.natPair.to_comp

def tagCode {X : Object} (tag : ℕ) (f : X ⟶ formulaObject) : X ⟶ formulaObject :=
  scalarUnary f (fun n => 6*n+tag)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
      (Primrec.const tag)).to_comp

def logical1Proof : finitePower formulaObject 2 ⟶ proofObject A B hA hB :=
  proofFromCode A B hA hB logical1Tree
    (fun x => ⟨_,Concludes.logical1 _ _⟩) (tagCode 0 (pairCodes prod.fst prod.snd))
    (by
      intro x
      change 6 * Nat.pair (firstPoint x).val (secondPoint x).val + 0 =
        (logical1Tree x).encode
      simp only [logical1Tree,ProofTree.encode,formulaAt_encode,Nat.add_zero])

def logical2Proof : finitePower formulaObject 3 ⟶ proofObject A B hA hB :=
  proofFromCode A B hA hB logical2Tree
    (fun x => ⟨_,Concludes.logical2 _ _ _⟩)
    (tagCode 1 (pairCodes (prod.fst ≫ prod.fst)
      (pairCodes (prod.fst ≫ prod.snd) prod.snd)))
    (by
      intro x
      change 6 * Nat.pair (firstPoint (firstPoint x)).val
        (Nat.pair (secondPoint (firstPoint x)).val (secondPoint x).val) + 1 =
          (logical2Tree x).encode
      simp only [logical2Tree,ProofTree.encode,formulaAt_encode])

def logical3Proof : finitePower formulaObject 2 ⟶ proofObject A B hA hB :=
  proofFromCode A B hA hB logical3Tree
    (fun x => ⟨_,Concludes.logical3 _ _⟩) (tagCode 2 (pairCodes prod.fst prod.snd))
    (by
      intro x
      change 6 * Nat.pair (firstPoint x).val (secondPoint x).val + 2 =
        (logical3Tree x).encode
      simp only [logical3Tree,ProofTree.encode,formulaAt_encode])

def positiveProof : positiveObject A hA ⟶ proofObject A B hA hB :=
  proofFromCode A B hA hB (fun x => .positive x.val)
    (fun x => ⟨_,Concludes.positive x.property⟩)
    (scalarMap hA (REPred.const True) (fun n => 6*n+3)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
        (Primrec.const 3)).to_comp
      (fun _ _ => Set.mem_univ _)) (fun _ => rfl)

def negativeProof : negativeObject B hB ⟶ proofObject A B hA hB :=
  proofFromCode A B hA hB (fun x => .negative x.val)
    (fun x => ⟨_,Concludes.negative x.property⟩)
    (scalarMap hB (REPred.const True) (fun n => 6*n+4)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id)
        (Primrec.const 4)).to_comp
      (fun _ _ => Set.mem_univ _)) (fun _ => rfl)

def axiomBranch (i : Fin 5) : axiomFamily A B hA hB i ⟶ proofObject A B hA hB :=
  Fin.cases (logical1Proof A B hA hB)
    (Fin.cases (logical2Proof A B hA hB)
      (Fin.cases (logical3Proof A B hA hB)
        (Fin.cases (positiveProof A B hA hB)
          (Fin.cases (negativeProof A B hA hB) (fun i => Fin.elim0 i))))) i

def axiomProof : axiomObject A B hA hB ⟶ proofObject A B hA hB :=
  Sigma.desc (axiomBranch A B hA hB)

/-- Exactly the displayed finite signature: five nullary leaf families,
an empty unary family, and binary ordered modus ponens. -/
def rules : RulePresentation formulaObject 2 where
  instances := ![axiomObject A B hA hB,⊥_ Object,formulaObject ⨯ formulaObject]
  premises := Fin.cases (terminal.from _) (Fin.cases (initial.to _)
    (Fin.cases (prod.lift prod.fst implication) (fun i => Fin.elim0 i)))
  conclusion := Fin.cases (axiomProof A B hA hB ≫ conclusion A B hA hB)
    (Fin.cases (initial.to _) (Fin.cases prod.snd (fun i => Fin.elim0 i)))

/-! Point constructors are induced by the categorical limits. -/

theorem point_comp {X Y : Object} (x : Point X) (f : X ⟶ Y) :
    NumericalUnderlying.point x ≫ f = NumericalUnderlying.point (f.toFun x) :=
  Map.ext rfl

@[simp] theorem prodLift_first {W X Y : Object} (f : W ⟶ X) (g : W ⟶ Y) (x : Point W) :
    firstPoint ((prod.lift f g).toFun x) = f.toFun x :=
  congrArg (fun k => k.toFun x) (prod.lift_fst f g)

@[simp] theorem prodLift_second {W X Y : Object} (f : W ⟶ X) (g : W ⟶ Y) (x : Point W) :
    secondPoint ((prod.lift f g).toFun x) = g.toFun x :=
  congrArg (fun k => k.toFun x) (prod.lift_snd f g)

@[simp] theorem prodMap_first {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) (x : Point (W ⨯ Y)) :
    firstPoint ((prod.map f g).toFun x) = f.toFun (firstPoint x) :=
  congrArg (fun k => k.toFun x) (prod.map_fst f g)

@[simp] theorem prodMap_second {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) (x : Point (W ⨯ Y)) :
    secondPoint ((prod.map f g).toFun x) = g.toFun (secondPoint x) :=
  congrArg (fun k => k.toFun x) (prod.map_snd f g)

def pairPoint {X Y : Object} (x : Point X) (y : Point Y) : Point (X ⨯ Y) :=
  (prod.lift (NumericalUnderlying.point x) (NumericalUnderlying.point y)).toFun
    NumericalUnderlying.terminalPoint

@[simp] theorem pairPoint_fst {X Y : Object} (x : Point X) (y : Point Y) :
    firstPoint (pairPoint x y) = x :=
  congrArg (fun f => f.toFun NumericalUnderlying.terminalPoint)
    (prod.lift_fst (NumericalUnderlying.point x) (NumericalUnderlying.point y))

@[simp] theorem pairPoint_snd {X Y : Object} (x : Point X) (y : Point Y) :
    secondPoint (pairPoint x y) = y :=
  congrArg (fun f => f.toFun NumericalUnderlying.terminalPoint)
    (prod.lift_snd (NumericalUnderlying.point x) (NumericalUnderlying.point y))

theorem prodPoint_ext {X Y : Object} {x y : Point (X ⨯ Y)}
    (h₁ : firstPoint x = firstPoint y)
    (h₂ : secondPoint x = secondPoint y) : x = y := by
  apply (NumericalUnderlying.pointHomEquiv (X ⨯ Y)).injective
  apply prod.hom_ext
  · exact (point_comp x prod.fst).trans ((congrArg NumericalUnderlying.point h₁).trans
      (point_comp y prod.fst).symm)
  · exact (point_comp x prod.snd).trans ((congrArg NumericalUnderlying.point h₂).trans
      (point_comp y prod.snd).symm)

theorem pairPoint_projections {X Y : Object} (x : Point (X ⨯ Y)) :
    pairPoint (firstPoint x) (secondPoint x) = x := by
  apply prodPoint_ext <;> simp

theorem pullbackPoint_ext {X Y Z : Object} (f : X ⟶ Z) (g : Y ⟶ Z)
    {x y : Point (pullback f g)}
    (h₁ : (pullback.fst f g).toFun x = (pullback.fst f g).toFun y)
    (h₂ : (pullback.snd f g).toFun x = (pullback.snd f g).toFun y) : x = y := by
  apply (NumericalUnderlying.pointHomEquiv (pullback f g)).injective
  apply pullback.hom_ext
  · exact (point_comp x _).trans ((congrArg NumericalUnderlying.point h₁).trans
      (point_comp y _).symm)
  · exact (point_comp x _).trans ((congrArg NumericalUnderlying.point h₂).trans
      (point_comp y _).symm)

def logical1Label (p q : Formula) : Point (axiomObject A B hA hB) :=
  (Sigma.ι (axiomFamily A B hA hB) 0).toFun (pairPoint (formulaPoint p) (formulaPoint q))

def logical2Label (p q r : Formula) : Point (axiomObject A B hA hB) :=
  (Sigma.ι (axiomFamily A B hA hB) 1).toFun
    (pairPoint (pairPoint (formulaPoint p) (formulaPoint q)) (formulaPoint r))

def logical3Label (p q : Formula) : Point (axiomObject A B hA hB) :=
  (Sigma.ι (axiomFamily A B hA hB) 2).toFun (pairPoint (formulaPoint p) (formulaPoint q))

def positiveLabel (x : ℕ) (hx : x ∈ A) : Point (axiomObject A B hA hB) :=
  (Sigma.ι (axiomFamily A B hA hB) 3).toFun ⟨x,hx⟩

def negativeLabel (x : ℕ) (hx : x ∈ B) : Point (axiomObject A B hA hB) :=
  (Sigma.ι (axiomFamily A B hA hB) 4).toFun ⟨x,hx⟩

def mpLabel (p q : Formula) : Point (formulaObject ⨯ formulaObject) :=
  pairPoint (formulaPoint p) (formulaPoint q)

theorem axiomProof_branch (i : Fin 5) (u : Point (axiomFamily A B hA hB i)) :
    (axiomProof A B hA hB).toFun ((Sigma.ι (axiomFamily A B hA hB) i).toFun u) =
      (axiomBranch A B hA hB i).toFun u :=
  congrArg (fun f => f.toFun u) (Sigma.ι_comp_desc (axiomBranch A B hA hB) i)

theorem axiomProof_logical1 (p q : Formula) :
    (axiomProof A B hA hB).toFun (logical1Label A B hA hB p q) =
      proofPoint A B hA hB (.logical1 p q) ⟨_,Concludes.logical1 p q⟩ := by
  erw [logical1Label,axiomProof_branch]
  change (logical1Proof A B hA hB).toFun (pairPoint (formulaPoint p) (formulaPoint q)) = _
  apply Subtype.ext
  change (ProofTree.logical1 (formulaAt (firstPoint (pairPoint (formulaPoint p) (formulaPoint q))))
    (formulaAt (secondPoint (pairPoint (formulaPoint p) (formulaPoint q))))).encode = _
  rw [pairPoint_fst,pairPoint_snd,formulaAt_point,formulaAt_point]
  rfl

theorem axiomProof_logical2 (p q r : Formula) :
    (axiomProof A B hA hB).toFun (logical2Label A B hA hB p q r) =
      proofPoint A B hA hB (.logical2 p q r) ⟨_,Concludes.logical2 p q r⟩ := by
  erw [logical2Label,axiomProof_branch]
  change (logical2Proof A B hA hB).toFun
    (pairPoint (pairPoint (formulaPoint p) (formulaPoint q)) (formulaPoint r)) = _
  apply Subtype.ext
  change (logical2Tree (pairPoint (pairPoint (formulaPoint p) (formulaPoint q)) (formulaPoint r))).encode = _
  simp only [logical2Tree,pairPoint_fst,pairPoint_snd,formulaAt_point]
  rfl

theorem axiomProof_logical3 (p q : Formula) :
    (axiomProof A B hA hB).toFun (logical3Label A B hA hB p q) =
      proofPoint A B hA hB (.logical3 p q) ⟨_,Concludes.logical3 p q⟩ := by
  erw [logical3Label,axiomProof_branch]
  change (logical3Proof A B hA hB).toFun (pairPoint (formulaPoint p) (formulaPoint q)) = _
  apply Subtype.ext
  change (ProofTree.logical3 (formulaAt (firstPoint (pairPoint (formulaPoint p) (formulaPoint q))))
    (formulaAt (secondPoint (pairPoint (formulaPoint p) (formulaPoint q))))).encode = _
  rw [pairPoint_fst,pairPoint_snd,formulaAt_point,formulaAt_point]
  rfl

theorem axiomProof_positive (x : ℕ) (hx : x ∈ A) :
    (axiomProof A B hA hB).toFun (positiveLabel A B hA hB x hx) =
      proofPoint A B hA hB (.positive x) ⟨_,Concludes.positive hx⟩ := by
  rw [positiveLabel,axiomProof_branch]
  rfl

theorem axiomProof_negative (x : ℕ) (hx : x ∈ B) :
    (axiomProof A B hA hB).toFun (negativeLabel A B hA hB x hx) =
      proofPoint A B hA hB (.negative x) ⟨_,Concludes.negative hx⟩ := by
  rw [negativeLabel,axiomProof_branch]
  rfl

theorem logical1Label_conclusion (p q : Formula) :
    (((rules A B hA hB).conclusion 0).toFun (logical1Label A B hA hB p q)).val = (H1 p q).encode := by
  change ((conclusion A B hA hB).toFun
    ((axiomProof A B hA hB).toFun (logical1Label A B hA hB p q))).val = _
  rw [axiomProof_logical1]
  exact proofPoint_conclusion A B hA hB (Concludes.logical1 p q)

theorem logical2Label_conclusion (p q r : Formula) :
    (((rules A B hA hB).conclusion 0).toFun (logical2Label A B hA hB p q r)).val = (H2 p q r).encode := by
  change ((conclusion A B hA hB).toFun
    ((axiomProof A B hA hB).toFun (logical2Label A B hA hB p q r))).val = _
  rw [axiomProof_logical2]
  exact proofPoint_conclusion A B hA hB (Concludes.logical2 p q r)

theorem logical3Label_conclusion (p q : Formula) :
    (((rules A B hA hB).conclusion 0).toFun (logical3Label A B hA hB p q)).val = (H3 p q).encode := by
  change ((conclusion A B hA hB).toFun
    ((axiomProof A B hA hB).toFun (logical3Label A B hA hB p q))).val = _
  rw [axiomProof_logical3]
  exact proofPoint_conclusion A B hA hB (Concludes.logical3 p q)

theorem positiveLabel_conclusion (x : ℕ) (hx : x ∈ A) :
    (((rules A B hA hB).conclusion 0).toFun (positiveLabel A B hA hB x hx)).val = (Formula.atom x).encode := by
  change ((conclusion A B hA hB).toFun
    ((axiomProof A B hA hB).toFun (positiveLabel A B hA hB x hx))).val = _
  rw [axiomProof_positive]
  exact proofPoint_conclusion A B hA hB (Concludes.positive hx)

theorem negativeLabel_conclusion (x : ℕ) (hx : x ∈ B) :
    (((rules A B hA hB).conclusion 0).toFun (negativeLabel A B hA hB x hx)).val =
      (Formula.neg (.atom x)).encode := by
  change ((conclusion A B hA hB).toFun
    ((axiomProof A B hA hB).toFun (negativeLabel A B hA hB x hx))).val = _
  rw [axiomProof_negative]
  exact proofPoint_conclusion A B hA hB (Concludes.negative hx)

def nullaryInputPoint (Q : Over formulaObject) (ξ : Point (axiomObject A B hA hB)) :
    Point ((rules A B hA hB).ruleObject Q 0) :=
  ((rules A B hA hB).nullaryRule Q).toFun ξ

def nullaryNodePoint (Q : Over formulaObject) (ξ : Point (axiomObject A B hA hB)) :
    Point (((rules A B hA hB).inference.obj Q).left) :=
  (Sigma.ι ((rules A B hA hB).ruleObject Q) 0).toFun
    (nullaryInputPoint A B hA hB Q ξ)

def mpInputPoint (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode)
    (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    Point ((rules A B hA hB).ruleObject Q 2) :=
  (pullback.lift (NumericalUnderlying.point (mpLabel p q))
    (NumericalUnderlying.point (pairPoint x y)) (by
      apply Map.ext
      funext u
      change (prod.lift (prod.fst : formulaObject ⨯ formulaObject ⟶ formulaObject) implication).toFun
        (mpLabel p q) = (prod.map Q.hom Q.hom).toFun (pairPoint x y)
      apply prodPoint_ext
      · apply Subtype.ext
        exact (congrArg Subtype.val (prodLift_first (prod.fst : _ ⟶ formulaObject) implication
          (mpLabel p q))).trans ((congrArg Subtype.val
            (pairPoint_fst (formulaPoint p) (formulaPoint q))).trans (hx.symm.trans
              ((congrArg Subtype.val (prodMap_first Q.hom Q.hom (pairPoint x y))).trans
                (congrArg (fun z => (Q.hom.toFun z).val) (pairPoint_fst x y))).symm))
      · apply Subtype.ext
        simpa only [prodLift_second,prodMap_second,implication_value,mpLabel,
          pairPoint_fst,pairPoint_snd,formulaAt_point] using hy.symm)).toFun
    NumericalUnderlying.terminalPoint

theorem mpInputPoint_label (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    (pullback.fst ((rules A B hA hB).premises 2) (finitePowerMap Q.hom 2)).toFun
      (mpInputPoint A B hA hB Q p q x y hx hy) = mpLabel p q := by
  unfold mpInputPoint
  exact congrArg (fun f : NumericalTuples.terminalObject ⟶ (rules A B hA hB).instances 2 =>
    f.toFun NumericalUnderlying.terminalPoint) (pullback.lift_fst _ _ _)

theorem mpInputPoint_children (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    (pullback.snd ((rules A B hA hB).premises 2) (finitePowerMap Q.hom 2)).toFun
      (mpInputPoint A B hA hB Q p q x y hx hy) = pairPoint x y := by
  unfold mpInputPoint
  exact congrArg (fun f : NumericalTuples.terminalObject ⟶ finitePower Q.left 2 =>
    f.toFun NumericalUnderlying.terminalPoint) (pullback.lift_snd _ _ _)

theorem mpInputPoint_first (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    firstPoint ((pullback.snd ((rules A B hA hB).premises 2)
      (finitePowerMap Q.hom 2)).toFun (mpInputPoint A B hA hB Q p q x y hx hy)) = x := by
  erw [mpInputPoint_children]
  exact pairPoint_fst x y

theorem mpInputPoint_second (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    secondPoint ((pullback.snd ((rules A B hA hB).premises 2)
      (finitePowerMap Q.hom 2)).toFun (mpInputPoint A B hA hB Q p q x y hx hy)) = y := by
  erw [mpInputPoint_children]
  exact pairPoint_snd x y

theorem mpInputPoint_conclusion (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    (((rules A B hA hB).ruleConclusion Q 2).toFun
      (mpInputPoint A B hA hB Q p q x y hx hy)).val = q.encode := by
  change (secondPoint ((pullback.fst ((rules A B hA hB).premises 2)
    (finitePowerMap Q.hom 2)).toFun (mpInputPoint A B hA hB Q p q x y hx hy))).val = _
  erw [mpInputPoint_label]
  exact congrArg Subtype.val (pairPoint_snd (formulaPoint p) (formulaPoint q))

def mpNodePoint (Q : Over formulaObject) (p q : Formula) (x y : Point Q.left)
    (hx : (Q.hom.toFun x).val = p.encode) (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    Point (((rules A B hA hB).inference.obj Q).left) :=
  (Sigma.ι ((rules A B hA hB).ruleObject Q) 2).toFun
    (mpInputPoint A B hA hB Q p q x y hx hy)

abbrev proofSlice := Over.mk (conclusion A B hA hB)

def mpFirst : (rules A B hA hB).ruleObject (proofSlice A B hA hB) 2 ⟶ proofObject A B hA hB :=
  pullback.snd _ _ ≫ prod.fst

def mpSecond : (rules A B hA hB).ruleObject (proofSlice A B hA hB) 2 ⟶ proofObject A B hA hB :=
  pullback.snd _ _ ≫ prod.snd

theorem mp_premise_values (x : Point ((rules A B hA hB).ruleObject (proofSlice A B hA hB) 2)) :
    formulaAt ((conclusion A B hA hB).toFun ((mpSecond A B hA hB).toFun x)) =
      .imp (formulaAt ((conclusion A B hA hB).toFun ((mpFirst A B hA hB).toFun x)))
        (formulaAt (((rules A B hA hB).ruleConclusion (proofSlice A B hA hB) 2).toFun x)) := by
  let r := (pullback.fst ((rules A B hA hB).premises 2)
    (finitePowerMap (conclusion A B hA hB) 2)).toFun x
  let z := (pullback.snd ((rules A B hA hB).premises 2)
    (finitePowerMap (conclusion A B hA hB) 2)).toFun x
  have hp := congrArg (fun f => f.toFun x)
    (pullback.condition (f := (rules A B hA hB).premises 2)
      (g := finitePowerMap (conclusion A B hA hB) 2))
  change (prod.lift (prod.fst : formulaObject ⨯ formulaObject ⟶ formulaObject) implication).toFun r =
    (prod.map (conclusion A B hA hB) (conclusion A B hA hB)).toFun z at hp
  have h₁ : formulaAt (firstPoint r) =
      formulaAt ((conclusion A B hA hB).toFun (firstPoint z)) := by
    have hh := congrArg (fun w => formulaAt (firstPoint w)) hp
    simp only [prodLift_first,prodMap_first] at hh
    change formulaAt (firstPoint r) =
      formulaAt ((conclusion A B hA hB).toFun (firstPoint z)) at hh
    exact hh
  have h₂ : formulaAt (implication.toFun r) =
      formulaAt ((conclusion A B hA hB).toFun (secondPoint z)) := by
    simpa only [prodLift_second,prodMap_second]
      using congrArg (fun w => formulaAt (secondPoint w)) hp
  change formulaAt ((conclusion A B hA hB).toFun (secondPoint z)) =
    Formula.imp (formulaAt ((conclusion A B hA hB).toFun (firstPoint z)))
      (formulaAt (secondPoint r))
  calc
    _ = formulaAt (implication.toFun r) := h₂.symm
    _ = Formula.imp (formulaAt (firstPoint r)) (formulaAt (secondPoint r)) := implication_formulaAt r
    _ = _ := congrArg (fun p => Formula.imp p (formulaAt (secondPoint r))) h₁

def mpTree (x : Point ((rules A B hA hB).ruleObject (proofSlice A B hA hB) 2)) : ProofTree :=
  .mp (proofAt A B hA hB ((mpFirst A B hA hB).toFun x))
    (proofAt A B hA hB ((mpSecond A B hA hB).toFun x))

theorem mpTree_concludes (x : Point ((rules A B hA hB).ruleObject (proofSlice A B hA hB) 2)) :
    Concludes A B (mpTree A B hA hB x)
      (formulaAt (((rules A B hA hB).ruleConclusion (proofSlice A B hA hB) 2).toFun x)) := by
  apply Concludes.mp (proofAt_concludes A B hA hB ((mpFirst A B hA hB).toFun x))
  rw [← mp_premise_values A B hA hB x]
  exact proofAt_concludes A B hA hB ((mpSecond A B hA hB).toFun x)

/-- Forgetting validity retains the original proof word. -/
def proofCodeInclusion : proofObject A B hA hB ⟶ formulaObject :=
  scalarMap (ForkSyntax.proofCarrier A B hA hB).enumerable (REPred.const True) id
    Computable.id (fun _ _ => Set.mem_univ _)

def mpProof : (rules A B hA hB).ruleObject (proofSlice A B hA hB) 2 ⟶ proofObject A B hA hB :=
  proofFromCode A B hA hB (mpTree A B hA hB)
    (fun x => ⟨_,mpTree_concludes A B hA hB x⟩)
    (tagCode 5 (pairCodes (mpFirst A B hA hB ≫ proofCodeInclusion A B hA hB)
      (mpSecond A B hA hB ≫ proofCodeInclusion A B hA hB)))
    (by
      intro x
      change 6 * Nat.pair ((mpFirst A B hA hB).toFun x).val
        ((mpSecond A B hA hB).toFun x).val + 5 = (mpTree A B hA hB x).encode
      simp only [mpTree,ProofTree.encode,proofAt_encode])

def oldBranches (i : Fin 3) :
    (rules A B hA hB).ruleObject (proofSlice A B hA hB) i ⟶ proofObject A B hA hB :=
  Fin.cases (pullback.fst _ _ ≫ axiomProof A B hA hB)
    (Fin.cases (pullback.fst _ _ ≫ initial.to _) (Fin.cases (mpProof A B hA hB) (fun i => Fin.elim0 i))) i

theorem oldBranches_conclusion (i : Fin 3) :
    oldBranches A B hA hB i ≫ conclusion A B hA hB =
      (rules A B hA hB).ruleConclusion (proofSlice A B hA hB) i := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) i
  · rfl
  · change (pullback.fst _ _ ≫ initial.to _) ≫ conclusion A B hA hB =
      pullback.fst _ _ ≫ initial.to _
    rw [Category.assoc]
    exact congrArg (fun f => pullback.fst ((rules A B hA hB).premises 1)
      (finitePowerMap (conclusion A B hA hB) 1) ≫ f) (initial.hom_ext _ _)
  · apply Map.ext
    funext x
    apply Subtype.ext
    exact (ForkSyntax.conclusionCode_of_concludes (mpTree_concludes A B hA hB x)).trans
      (Formula.encode_decode _)

def algebra : Endofunctor.Algebra (rules A B hA hB).inference where
  a := proofSlice A B hA hB
  str := Over.homMk (Sigma.desc (oldBranches A B hA hB)) (by
    apply Sigma.hom_ext
    intro i
    change (Sigma.ι ((rules A B hA hB).ruleObject (proofSlice A B hA hB)) i ≫
      Sigma.desc (oldBranches A B hA hB)) ≫ conclusion A B hA hB =
      Sigma.ι ((rules A B hA hB).ruleObject (proofSlice A B hA hB)) i ≫
        Sigma.desc ((rules A B hA hB).ruleConclusion (proofSlice A B hA hB))
    rw [Sigma.ι_comp_desc,Sigma.ι_comp_desc]
    exact oldBranches_conclusion A B hA hB i)

theorem algebra_branch (i : Fin 3)
    (u : Point ((rules A B hA hB).ruleObject (proofSlice A B hA hB) i)) :
    (algebra A B hA hB).str.left.toFun
      ((Sigma.ι ((rules A B hA hB).ruleObject (proofSlice A B hA hB)) i).toFun u) =
      (oldBranches A B hA hB i).toFun u :=
  congrArg (fun f => f.toFun u) (Sigma.ι_comp_desc (oldBranches A B hA hB) i)

theorem algebra_nullary (ξ : Point (axiomObject A B hA hB)) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a ξ) =
        (axiomProof A B hA hB).toFun ξ := by
  have h := congrArg (fun f => f.toFun ξ)
    ((rules A B hA hB).nullaryRule_fst (algebra A B hA hB).a)
  change (algebra A B hA hB).str.left.toFun
    ((Sigma.ι ((rules A B hA hB).ruleObject (proofSlice A B hA hB)) 0).toFun
      (nullaryInputPoint A B hA hB (proofSlice A B hA hB) ξ)) = _
  exact (algebra_branch A B hA hB 0 _).trans
    (congrArg (axiomProof A B hA hB).toFun h)

theorem algebra_logical1 (p q : Formula) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (logical1Label A B hA hB p q)) =
      proofPoint A B hA hB (.logical1 p q) ⟨_,Concludes.logical1 p q⟩ := by
  exact (algebra_nullary A B hA hB _).trans (axiomProof_logical1 A B hA hB p q)

theorem algebra_logical2 (p q r : Formula) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (logical2Label A B hA hB p q r)) =
      proofPoint A B hA hB (.logical2 p q r) ⟨_,Concludes.logical2 p q r⟩ := by
  exact (algebra_nullary A B hA hB _).trans (axiomProof_logical2 A B hA hB p q r)

theorem algebra_logical3 (p q : Formula) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (logical3Label A B hA hB p q)) =
      proofPoint A B hA hB (.logical3 p q) ⟨_,Concludes.logical3 p q⟩ := by
  exact (algebra_nullary A B hA hB _).trans (axiomProof_logical3 A B hA hB p q)

theorem algebra_positive (x : ℕ) (hx : x ∈ A) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (positiveLabel A B hA hB x hx)) =
      proofPoint A B hA hB (.positive x) ⟨_,Concludes.positive hx⟩ := by
  exact (algebra_nullary A B hA hB _).trans (axiomProof_positive A B hA hB x hx)

theorem algebra_negative (x : ℕ) (hx : x ∈ B) :
    (algebra A B hA hB).str.left.toFun
      (nullaryNodePoint A B hA hB (algebra A B hA hB).a (negativeLabel A B hA hB x hx)) =
      proofPoint A B hA hB (.negative x) ⟨_,Concludes.negative hx⟩ := by
  exact (algebra_nullary A B hA hB _).trans (axiomProof_negative A B hA hB x hx)

theorem algebra_mp {t u : ProofTree} {p q : Formula}
    (ht : Concludes A B t p) (hu : Concludes A B u (.imp p q)) :
    (algebra A B hA hB).str.left.toFun
      (mpNodePoint A B hA hB (algebra A B hA hB).a p q
        (proofPoint A B hA hB t ⟨p,ht⟩) (proofPoint A B hA hB u ⟨_,hu⟩)
        (proofPoint_conclusion A B hA hB ht) (proofPoint_conclusion A B hA hB hu)) =
      proofPoint A B hA hB (.mp t u) ⟨q,Concludes.mp ht hu⟩ := by
  apply (algebra_branch A B hA hB 2 _).trans
  apply Subtype.ext
  let v := mpInputPoint A B hA hB (proofSlice A B hA hB) p q
    (proofPoint A B hA hB t ⟨p,ht⟩) (proofPoint A B hA hB u ⟨_,hu⟩)
    (proofPoint_conclusion A B hA hB ht) (proofPoint_conclusion A B hA hB hu)
  change (mpTree A B hA hB v).encode = (ProofTree.mp t u).encode
  apply congrArg ProofTree.encode
  apply congrArg₂ ProofTree.mp
  · exact (congrArg (proofAt A B hA hB)
      (mpInputPoint_first A B hA hB (proofSlice A B hA hB) p q
        (proofPoint A B hA hB t ⟨p,ht⟩) (proofPoint A B hA hB u ⟨_,hu⟩)
        (proofPoint_conclusion A B hA hB ht) (proofPoint_conclusion A B hA hB hu))).trans
      (proofAt_point A B hA hB t ⟨p,ht⟩)
  · exact (congrArg (proofAt A B hA hB)
      (mpInputPoint_second A B hA hB (proofSlice A B hA hB) p q
        (proofPoint A B hA hB t ⟨p,ht⟩) (proofPoint A B hA hB u ⟨_,hu⟩)
        (proofPoint_conclusion A B hA hB ht) (proofPoint_conclusion A B hA hB hu))).trans
      (proofAt_point A B hA hB u ⟨_,hu⟩)

/-!
Every inference input has exactly one of the root shapes. The following is a statement
about points of the original pullbacks; it does not replace their carriers by a
different syntax presentation.
-/

theorem sigmaPoint_cases {I : Type} [Finite I] (C : I → Object)
    (x : Point (∐ C)) : ∃ (i : I) (y : Point (C i)),(Sigma.ι C i).toFun y = x := by
  exact Cofan.inj_jointly_surjective_of_isColimit
    (isColimitOfHasCoproductOfPreservesColimit NumericalUnderlying.functor C) x

theorem terminalPoint_ext (x y : Point (⊤_ Object)) : x = y := by
  apply (NumericalUnderlying.pointHomEquiv (⊤_ Object)).injective
  exact terminal.hom_ext _ _

theorem nullaryInputPoint_fst (Q : Over formulaObject)
    (ξ : Point (axiomObject A B hA hB)) :
    (pullback.fst ((rules A B hA hB).premises 0) (finitePowerMap Q.hom 0)).toFun
      (nullaryInputPoint A B hA hB Q ξ) = ξ := by
  exact congrArg (fun f => f.toFun ξ) ((rules A B hA hB).nullaryRule_fst Q)

theorem nullaryInputPoint_eta (Q : Over formulaObject)
    (u : Point ((rules A B hA hB).ruleObject Q 0)) :
    nullaryInputPoint A B hA hB Q
      ((pullback.fst ((rules A B hA hB).premises 0) (finitePowerMap Q.hom 0)).toFun u) = u := by
  apply pullbackPoint_ext
  · exact nullaryInputPoint_fst A B hA hB Q _
  · exact terminalPoint_ext _ _

/-- The names of formulas and the order of children are retained in each
root shape. The equality hypotheses are exactly the MP pullback condition. -/
inductive Node (Q : Over formulaObject) where
  | logical1 (p q : Formula)
  | logical2 (p q r : Formula)
  | logical3 (p q : Formula)
  | positive (x : ℕ) (hx : x ∈ A)
  | negative (x : ℕ) (hx : x ∈ B)
  | mp (p q : Formula) (x y : Point Q.left)
      (hx : (Q.hom.toFun x).val = p.encode)
      (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode)

def nodeInput (Q : Over formulaObject) : Node A B Q →
    Point (((rules A B hA hB).inference.obj Q).left)
  | .logical1 p q => nullaryNodePoint A B hA hB Q (logical1Label A B hA hB p q)
  | .logical2 p q r => nullaryNodePoint A B hA hB Q (logical2Label A B hA hB p q r)
  | .logical3 p q => nullaryNodePoint A B hA hB Q (logical3Label A B hA hB p q)
  | .positive x hx => nullaryNodePoint A B hA hB Q (positiveLabel A B hA hB x hx)
  | .negative x hx => nullaryNodePoint A B hA hB Q (negativeLabel A B hA hB x hx)
  | .mp p q x y hx hy => mpNodePoint A B hA hB Q p q x y hx hy

theorem axiomPoint_cases (ξ : Point (axiomObject A B hA hB)) :
    (∃ p q,logical1Label A B hA hB p q = ξ) ∨
    (∃ p q r,logical2Label A B hA hB p q r = ξ) ∨
    (∃ p q,logical3Label A B hA hB p q = ξ) ∨
    (∃ x hx,positiveLabel A B hA hB x hx = ξ) ∨
    (∃ x hx,negativeLabel A B hA hB x hx = ξ) := by
  obtain ⟨i,u,rfl⟩ := sigmaPoint_cases (axiomFamily A B hA hB) ξ
  fin_cases i
  · left
    refine ⟨formulaAt (firstPoint u),formulaAt (secondPoint u),?_⟩
    change (Sigma.ι (axiomFamily A B hA hB) 0).toFun
      (pairPoint (formulaPoint (formulaAt (firstPoint u)))
        (formulaPoint (formulaAt (secondPoint u)))) = _
    apply congrArg (Sigma.ι (axiomFamily A B hA hB) 0).toFun
    simp only [formulaPoint_at,pairPoint_projections]
  · right; left
    refine ⟨formulaAt (firstPoint (firstPoint u)),
      formulaAt (secondPoint (firstPoint u)),formulaAt (secondPoint u),?_⟩
    change (Sigma.ι (axiomFamily A B hA hB) 1).toFun
      (pairPoint (pairPoint (formulaPoint (formulaAt (firstPoint (firstPoint u))))
        (formulaPoint (formulaAt (secondPoint (firstPoint u)))))
        (formulaPoint (formulaAt (secondPoint u)))) = _
    apply congrArg (Sigma.ι (axiomFamily A B hA hB) 1).toFun
    simp only [formulaPoint_at,pairPoint_projections]
  · right; right; left
    refine ⟨formulaAt (firstPoint u),formulaAt (secondPoint u),?_⟩
    change (Sigma.ι (axiomFamily A B hA hB) 2).toFun
      (pairPoint (formulaPoint (formulaAt (firstPoint u)))
        (formulaPoint (formulaAt (secondPoint u)))) = _
    apply congrArg (Sigma.ι (axiomFamily A B hA hB) 2).toFun
    simp only [formulaPoint_at,pairPoint_projections]
  · right; right; right; left
    exact ⟨u.val,u.property,rfl⟩
  · right; right; right; right
    exact ⟨u.val,u.property,rfl⟩

theorem mpInputPoint_cases (Q : Over formulaObject)
    (u : Point ((rules A B hA hB).ruleObject Q 2)) :
    ∃ (p q : Formula) (x y : Point Q.left)
      (hx : (Q.hom.toFun x).val = p.encode)
      (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode),mpInputPoint A B hA hB Q p q x y hx hy = u := by
  let r : Point (formulaObject ⨯ formulaObject) :=
    (pullback.fst ((rules A B hA hB).premises 2) (finitePowerMap Q.hom 2)).toFun u
  let z : Point (Q.left ⨯ Q.left) :=
    (pullback.snd ((rules A B hA hB).premises 2) (finitePowerMap Q.hom 2)).toFun u
  let p := formulaAt (firstPoint r)
  let q := formulaAt (secondPoint r)
  let x : Point Q.left := firstPoint z
  let y : Point Q.left := secondPoint z
  have hp := congrArg (fun f => f.toFun u)
    (pullback.condition (f := (rules A B hA hB).premises 2) (g := finitePowerMap Q.hom 2))
  change (prod.lift (prod.fst : formulaObject ⨯ formulaObject ⟶ formulaObject) implication).toFun r =
    (prod.map Q.hom Q.hom).toFun z at hp
  have hx : (Q.hom.toFun x).val = p.encode := by
    have h := congrArg (fun w => (firstPoint w).val) hp
    simp only [prodLift_first,prodMap_first] at h
    change (firstPoint r).val = (Q.hom.toFun x).val at h
    exact h.symm.trans (formulaAt_encode (firstPoint r)).symm
  have hy : (Q.hom.toFun y).val = (Formula.imp p q).encode := by
    have h := congrArg (fun w => (secondPoint w).val) hp
    simp only [prodLift_second,prodMap_second] at h
    exact h.symm.trans (implication_value r)
  refine ⟨p,q,x,y,hx,hy,?_⟩
  apply pullbackPoint_ext
  · exact (mpInputPoint_label A B hA hB Q p q x y hx hy).trans (by
      change pairPoint (formulaPoint (formulaAt (firstPoint r)))
        (formulaPoint (formulaAt (secondPoint r))) = r
      rw [formulaPoint_at,formulaPoint_at]
      exact pairPoint_projections r)
  · exact (mpInputPoint_children A B hA hB Q p q x y hx hy).trans (pairPoint_projections z)

theorem nodeInput_surjective (Q : Over formulaObject) :
    Function.Surjective (nodeInput A B hA hB Q) := by
  intro u
  obtain ⟨i,v,hv⟩ := sigmaPoint_cases ((rules A B hA hB).ruleObject Q) u
  fin_cases i
  · obtain h | h | h | h | h := axiomPoint_cases A B hA hB
      ((pullback.fst ((rules A B hA hB).premises 0) (finitePowerMap Q.hom 0)).toFun v)
    · obtain ⟨p,q,h⟩ := h
      refine ⟨.logical1 p q,?_⟩
      exact (congrArg (fun ξ => nullaryNodePoint A B hA hB Q ξ) h).trans
        ((congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q) 0).toFun
          (nullaryInputPoint_eta A B hA hB Q v)).trans hv)
    · obtain ⟨p,q,r,h⟩ := h
      refine ⟨.logical2 p q r,?_⟩
      exact (congrArg (fun ξ => nullaryNodePoint A B hA hB Q ξ) h).trans
        ((congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q) 0).toFun
          (nullaryInputPoint_eta A B hA hB Q v)).trans hv)
    · obtain ⟨p,q,h⟩ := h
      refine ⟨.logical3 p q,?_⟩
      exact (congrArg (fun ξ => nullaryNodePoint A B hA hB Q ξ) h).trans
        ((congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q) 0).toFun
          (nullaryInputPoint_eta A B hA hB Q v)).trans hv)
    · obtain ⟨x,hx,h⟩ := h
      refine ⟨.positive x hx,?_⟩
      exact (congrArg (fun ξ => nullaryNodePoint A B hA hB Q ξ) h).trans
        ((congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q) 0).toFun
          (nullaryInputPoint_eta A B hA hB Q v)).trans hv)
    · obtain ⟨x,hx,h⟩ := h
      refine ⟨.negative x hx,?_⟩
      exact (congrArg (fun ξ => nullaryNodePoint A B hA hB Q ξ) h).trans
        ((congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q) 0).toFun
          (nullaryInputPoint_eta A B hA hB Q v)).trans hv)
  · exact (NumericalUnderlying.initialCarrierEmpty.false
      ((pullback.fst ((rules A B hA hB).premises 1) (finitePowerMap Q.hom 1)).toFun v)).elim
  · obtain ⟨p,q,x,y,hx,hy,h⟩ := mpInputPoint_cases A B hA hB Q v
    exact ⟨.mp p q x y hx hy,(congrArg
      (Sigma.ι ((rules A B hA hB).ruleObject Q) 2).toFun h).trans hv⟩

def nodeMap {Q Q' : Over formulaObject} (f : Q ⟶ Q') : Node A B Q → Node A B Q'
  | .logical1 p q => .logical1 p q
  | .logical2 p q r => .logical2 p q r
  | .logical3 p q => .logical3 p q
  | .positive x hx => .positive x hx
  | .negative x hx => .negative x hx
  | .mp p q x y hx hy => .mp p q (f.left.toFun x) (f.left.toFun y)
      ((congrArg (fun k => (k.toFun x).val) (Over.w f)).trans hx)
      ((congrArg (fun k => (k.toFun y).val) (Over.w f)).trans hy)

theorem nullaryInput_map {Q Q' : Over formulaObject} (f : Q ⟶ Q')
    (ξ : Point (axiomObject A B hA hB)) :
    ((rules A B hA hB).ruleMap f 0).toFun (nullaryInputPoint A B hA hB Q ξ) =
      nullaryInputPoint A B hA hB Q' ξ := by
  apply pullbackPoint_ext
  · have h := congrArg (fun k => k.toFun (nullaryInputPoint A B hA hB Q ξ))
      ((rules A B hA hB).ruleMap_fst f 0)
    exact h.trans ((nullaryInputPoint_fst A B hA hB Q ξ).trans
      (nullaryInputPoint_fst A B hA hB Q' ξ).symm)
  · exact terminalPoint_ext _ _

theorem mpInput_map {Q Q' : Over formulaObject} (f : Q ⟶ Q') (p q : Formula)
    (x y : Point Q.left) (hx : (Q.hom.toFun x).val = p.encode)
    (hy : (Q.hom.toFun y).val = (Formula.imp p q).encode) :
    ((rules A B hA hB).ruleMap f 2).toFun (mpInputPoint A B hA hB Q p q x y hx hy) =
      mpInputPoint A B hA hB Q' p q (f.left.toFun x) (f.left.toFun y)
        ((congrArg (fun k => (k.toFun x).val) (Over.w f)).trans hx)
        ((congrArg (fun k => (k.toFun y).val) (Over.w f)).trans hy) := by
  apply pullbackPoint_ext
  · have h := congrArg (fun k => k.toFun (mpInputPoint A B hA hB Q p q x y hx hy))
      ((rules A B hA hB).ruleMap_fst f 2)
    exact h.trans ((mpInputPoint_label A B hA hB Q p q x y hx hy).trans
      (mpInputPoint_label A B hA hB Q' p q (f.left.toFun x) (f.left.toFun y) _ _).symm)
  · have h := congrArg (fun k => k.toFun (mpInputPoint A B hA hB Q p q x y hx hy))
      ((rules A B hA hB).ruleMap_snd f 2)
    apply prodPoint_ext
    · exact (congrArg firstPoint h).trans ((prodMap_first f.left f.left _).trans
        ((congrArg f.left.toFun (mpInputPoint_first A B hA hB Q p q x y hx hy)).trans
          (mpInputPoint_first A B hA hB Q' p q (f.left.toFun x) (f.left.toFun y) _ _).symm))
    · exact (congrArg secondPoint h).trans ((prodMap_second f.left f.left _).trans
        ((congrArg f.left.toFun (mpInputPoint_second A B hA hB Q p q x y hx hy)).trans
          (mpInputPoint_second A B hA hB Q' p q (f.left.toFun x) (f.left.toFun y) _ _).symm))

theorem inference_branch_map {Q Q' : Over formulaObject} (f : Q ⟶ Q') (i : Fin 3)
    (u : Point ((rules A B hA hB).ruleObject Q i)) :
    ((rules A B hA hB).inference.map f).left.toFun
      ((Sigma.ι ((rules A B hA hB).ruleObject Q) i).toFun u) =
      (Sigma.ι ((rules A B hA hB).ruleObject Q') i).toFun
        (((rules A B hA hB).ruleMap f i).toFun u) :=
  congrArg (fun k => k.toFun u) (Sigma.ι_map ((rules A B hA hB).ruleMap f) i)

theorem nullaryNode_map {Q Q' : Over formulaObject} (f : Q ⟶ Q')
    (ξ : Point (axiomObject A B hA hB)) :
    ((rules A B hA hB).inference.map f).left.toFun (nullaryNodePoint A B hA hB Q ξ) =
      nullaryNodePoint A B hA hB Q' ξ :=
  (inference_branch_map A B hA hB f 0 _).trans
    (congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q') 0).toFun
      (nullaryInput_map A B hA hB f ξ))

theorem nodeInput_map {Q Q' : Over formulaObject} (f : Q ⟶ Q') (n : Node A B Q) :
    ((rules A B hA hB).inference.map f).left.toFun (nodeInput A B hA hB Q n) =
      nodeInput A B hA hB Q' (nodeMap A B f n) := by
  cases n with
  | logical1 => exact nullaryNode_map A B hA hB f _
  | logical2 => exact nullaryNode_map A B hA hB f _
  | logical3 => exact nullaryNode_map A B hA hB f _
  | positive => exact nullaryNode_map A B hA hB f _
  | negative => exact nullaryNode_map A B hA hB f _
  | mp p q x y hx hy =>
    exact (inference_branch_map A B hA hB f 2 _).trans
      (congrArg (Sigma.ι ((rules A B hA hB).ruleObject Q') 2).toFun
        (mpInput_map A B hA hB f p q x y hx hy))

/-- The fold is the existing numerical initial-algebra fold into the
constructed old algebra; its computation need only be total on proofs. -/
def codeToOld : NumericalDerivation.codeAlgebra (rules A B hA hB) ⟶ algebra A B hA hB :=
  NumericalDerivation.codeFold (rules A B hA hB) (algebra A B hA hB)

theorem codeToOld_conclusion :
    (codeToOld A B hA hB).f.left ≫ conclusion A B hA hB =
      NumericalDerivation.codeConclusion (rules A B hA hB) :=
  Over.w (codeToOld A B hA hB).f

theorem codeToOld_node (n : Node A B (NumericalDerivation.codeAlgebra (rules A B hA hB)).a) :
    (codeToOld A B hA hB).f.left.toFun
      ((NumericalDerivation.codeAlgebra (rules A B hA hB)).str.left.toFun
        (nodeInput A B hA hB _ n)) =
      (algebra A B hA hB).str.left.toFun
        (nodeInput A B hA hB _ (nodeMap A B (codeToOld A B hA hB).f n)) := by
  have h := congrArg (fun f => f.left.toFun (nodeInput A B hA hB _ n))
    (codeToOld A B hA hB).h.symm
  exact h.trans (congrArg (algebra A B hA hB).str.left.toFun
    (nodeInput_map A B hA hB (codeToOld A B hA hB).f n))

/-- Lambek decomposition uses the structure morphism of the constructed numerical initial
algebra, and the inference inputs. -/
theorem code_root (x : Point (NumericalDerivation.codeObject (rules A B hA hB))) :
    ∃ n : Node A B (NumericalDerivation.codeAlgebra (rules A B hA hB)).a,
      (NumericalDerivation.codeAlgebra (rules A B hA hB)).str.left.toFun
        (nodeInput A B hA hB _ n) = x := by
  let C := NumericalDerivation.codeAlgebra (rules A B hA hB)
  let _ : IsIso C.str := Endofunctor.Algebra.Initial.str_isIso
    (NumericalDerivation.codeInitial (rules A B hA hB))
  let e := (Over.forget formulaObject).mapIso (asIso C.str)
  let u := e.inv.toFun x
  obtain ⟨n,hn⟩ := nodeInput_surjective A B hA hB C.a u
  refine ⟨n,?_⟩
  exact (congrArg e.hom.toFun hn).trans
    (congrArg (fun f => f.toFun x) e.inv_hom_id)

def nodeTree : Node A B (algebra A B hA hB).a → ProofTree
  | .logical1 p q => .logical1 p q
  | .logical2 p q r => .logical2 p q r
  | .logical3 p q => .logical3 p q
  | .positive x _ => .positive x
  | .negative x _ => .negative x
  | .mp _ _ x y _ _ => .mp (proofAt A B hA hB x) (proofAt A B hA hB y)

theorem algebra_node_value (n : Node A B (algebra A B hA hB).a) :
    ((algebra A B hA hB).str.left.toFun (nodeInput A B hA hB _ n)).val =
      (nodeTree A B hA hB n).encode := by
  cases n with
  | logical1 p q => exact congrArg Subtype.val (algebra_logical1 A B hA hB p q)
  | logical2 p q r => exact congrArg Subtype.val (algebra_logical2 A B hA hB p q r)
  | logical3 p q => exact congrArg Subtype.val (algebra_logical3 A B hA hB p q)
  | positive x hx => exact congrArg Subtype.val (algebra_positive A B hA hB x hx)
  | negative x hx => exact congrArg Subtype.val (algebra_negative A B hA hB x hx)
  | mp p q x y hx hy =>
    apply (congrArg Subtype.val (algebra_branch A B hA hB 2
      (mpInputPoint A B hA hB (proofSlice A B hA hB) p q x y hx hy))).trans
    change (mpTree A B hA hB
      (mpInputPoint A B hA hB (proofSlice A B hA hB) p q x y hx hy)).encode = _
    apply congrArg ProofTree.encode
    apply congrArg₂ ProofTree.mp
    · exact congrArg (proofAt A B hA hB)
        (mpInputPoint_first A B hA hB (proofSlice A B hA hB) p q x y hx hy)
    · exact congrArg (proofAt A B hA hB)
        (mpInputPoint_second A B hA hB (proofSlice A B hA hB) p q x y hx hy)

abbrev constructed := NumericalDerivation.codeAlgebra (rules A B hA hB)

def codeNodeTree (n : Node A B (constructed A B hA hB).a) : ProofTree :=
  nodeTree A B hA hB (nodeMap A B (codeToOld A B hA hB).f n)

theorem codeToOld_node_value (n : Node A B (constructed A B hA hB).a) :
    ((codeToOld A B hA hB).f.left.toFun
      ((constructed A B hA hB).str.left.toFun (nodeInput A B hA hB _ n))).val =
      (codeNodeTree A B hA hB n).encode :=
  (congrArg Subtype.val (codeToOld_node A B hA hB n)).trans
    (algebra_node_value A B hA hB (nodeMap A B (codeToOld A B hA hB).f n))

theorem codeToOld_conclusion_value (x : Point (constructed A B hA hB).a.left) :
    (((constructed A B hA hB).a.hom).toFun x).val =
      ForkSyntax.conclusionCode (((codeToOld A B hA hB).f.left.toFun x).val) := by
  exact (congrArg (fun f => (f.toFun x).val) (codeToOld_conclusion A B hA hB)).symm

theorem codeToOld_fiber_conclusion {t : ProofTree} {p : Formula}
    (ht : Concludes A B t p) (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = t.encode) :
    (((constructed A B hA hB).a.hom).toFun x).val = p.encode := by
  rw [codeToOld_conclusion_value,hx]
  exact ForkSyntax.conclusionCode_of_concludes ht

/-- Existence is induction on the given finite valid proof. The sole recursive calls are
its two children in the MP case. -/
theorem codeToOld_surjective_tree {t : ProofTree} {p : Formula} (ht : Concludes A B t p) :
    ∃ x : Point (constructed A B hA hB).a.left,
      ((codeToOld A B hA hB).f.left.toFun x).val = t.encode := by
  induction ht with
  | logical1 p q =>
    exact ⟨(constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.logical1 p q)),codeToOld_node_value A B hA hB _⟩
  | logical2 p q r =>
    exact ⟨(constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.logical2 p q r)),codeToOld_node_value A B hA hB _⟩
  | logical3 p q =>
    exact ⟨(constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.logical3 p q)),codeToOld_node_value A B hA hB _⟩
  | @positive x hx =>
    exact ⟨(constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.positive x hx)),codeToOld_node_value A B hA hB _⟩
  | @negative x hx =>
    exact ⟨(constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.negative x hx)),codeToOld_node_value A B hA hB _⟩
  | @mp t u p q ht hu iht ihu =>
    obtain ⟨x,hx⟩ := iht
    obtain ⟨y,hy⟩ := ihu
    let n : Node A B (constructed A B hA hB).a := .mp p q x y
      (codeToOld_fiber_conclusion A B hA hB ht x hx)
      (codeToOld_fiber_conclusion A B hA hB hu y hy)
    refine ⟨(constructed A B hA hB).str.left.toFun (nodeInput A B hA hB _ n),?_⟩
    have h := codeToOld_node_value A B hA hB n
    simpa only [n,codeNodeTree,nodeMap,nodeTree,proofAt,hx,hy,ProofTree.decode_encode] using h

theorem codeToOld_surjective :
    Function.Surjective (codeToOld A B hA hB).f.left.toFun := by
  intro x
  obtain ⟨p,hp⟩ := proofAt_valid A B hA hB x
  obtain ⟨y,hy⟩ := codeToOld_surjective_tree A B hA hB hp
  exact ⟨y,Subtype.ext (hy.trans (ProofTree.encode_decode x.val))⟩

/-- A root over a specified leaf word must be its unique literal leaf
input. There is no inference about the arithmetic code order here. -/
theorem code_root_logical1 (p q : Formula)
    (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = (ProofTree.logical1 p q).encode) :
    x = (constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.logical1 p q)) := by
  obtain ⟨n,hn⟩ := code_root A B hA hB x
  have he : codeNodeTree A B hA hB n = .logical1 p q :=
    ProofTree.codingEquiv.injective ((codeToOld_node_value A B hA hB n).symm.trans
      ((congrArg (fun z => ((codeToOld A B hA hB).f.left.toFun z).val) hn).trans hx))
  cases n <;> simp only [codeNodeTree,nodeMap,nodeTree] at he
  all_goals cases he <;> exact hn.symm

theorem code_root_logical2 (p q r : Formula)
    (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = (ProofTree.logical2 p q r).encode) :
    x = (constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.logical2 p q r)) := by
  obtain ⟨n,hn⟩ := code_root A B hA hB x
  have he : codeNodeTree A B hA hB n = .logical2 p q r :=
    ProofTree.codingEquiv.injective ((codeToOld_node_value A B hA hB n).symm.trans
      ((congrArg (fun z => ((codeToOld A B hA hB).f.left.toFun z).val) hn).trans hx))
  cases n <;> simp only [codeNodeTree,nodeMap,nodeTree] at he
  all_goals cases he <;> exact hn.symm

theorem code_root_logical3 (p q : Formula)
    (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = (ProofTree.logical3 p q).encode) :
    x = (constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.logical3 p q)) := by
  obtain ⟨n,hn⟩ := code_root A B hA hB x
  have he : codeNodeTree A B hA hB n = .logical3 p q :=
    ProofTree.codingEquiv.injective ((codeToOld_node_value A B hA hB n).symm.trans
      ((congrArg (fun z => ((codeToOld A B hA hB).f.left.toFun z).val) hn).trans hx))
  cases n <;> simp only [codeNodeTree,nodeMap,nodeTree] at he
  all_goals cases he <;> exact hn.symm

theorem code_root_positive (z : ℕ) (hz : z ∈ A)
    (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = (ProofTree.positive z).encode) :
    x = (constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.positive z hz)) := by
  obtain ⟨n,hn⟩ := code_root A B hA hB x
  have he : codeNodeTree A B hA hB n = .positive z :=
    ProofTree.codingEquiv.injective ((codeToOld_node_value A B hA hB n).symm.trans
      ((congrArg (fun w => ((codeToOld A B hA hB).f.left.toFun w).val) hn).trans hx))
  cases n <;> simp only [codeNodeTree,nodeMap,nodeTree] at he
  all_goals cases he <;> exact hn.symm

theorem code_root_negative (z : ℕ) (hz : z ∈ B)
    (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = (ProofTree.negative z).encode) :
    x = (constructed A B hA hB).str.left.toFun
      (nodeInput A B hA hB _ (.negative z hz)) := by
  obtain ⟨n,hn⟩ := code_root A B hA hB x
  have he : codeNodeTree A B hA hB n = .negative z :=
    ProofTree.codingEquiv.injective ((codeToOld_node_value A B hA hB n).symm.trans
      ((congrArg (fun w => ((codeToOld A B hA hB).f.left.toFun w).val) hn).trans hx))
  cases n <;> simp only [codeNodeTree,nodeMap,nodeTree] at he
  all_goals cases he <;> exact hn.symm

/-- Decomposition over an MP word retains its two ordered children and
their separately prescribed conclusions. -/
theorem code_root_mp {t u : ProofTree} (x : Point (constructed A B hA hB).a.left)
    (hx : ((codeToOld A B hA hB).f.left.toFun x).val = (ProofTree.mp t u).encode) :
    ∃ (p q : Formula) (a b : Point (constructed A B hA hB).a.left)
      (ha : ((constructed A B hA hB).a.hom.toFun a).val = p.encode)
      (hb : ((constructed A B hA hB).a.hom.toFun b).val = (Formula.imp p q).encode),
      (constructed A B hA hB).str.left.toFun
        (nodeInput A B hA hB _ (.mp p q a b ha hb)) = x ∧
      ((codeToOld A B hA hB).f.left.toFun a).val = t.encode ∧
      ((codeToOld A B hA hB).f.left.toFun b).val = u.encode := by
  obtain ⟨n,hn⟩ := code_root A B hA hB x
  have he : codeNodeTree A B hA hB n = .mp t u :=
    ProofTree.codingEquiv.injective ((codeToOld_node_value A B hA hB n).symm.trans
      ((congrArg (fun w => ((codeToOld A B hA hB).f.left.toFun w).val) hn).trans hx))
  cases n with
  | logical1 | logical2 | logical3 | positive | negative => cases he
  | mp p q a b ha hb =>
    have ht : proofAt A B hA hB ((codeToOld A B hA hB).f.left.toFun a) = t :=
      (ProofTree.mp.inj he).1
    have hu : proofAt A B hA hB ((codeToOld A B hA hB).f.left.toFun b) = u :=
      (ProofTree.mp.inj he).2
    exact ⟨p,q,a,b,ha,hb,hn,
      (ProofTree.encode_decode _).symm.trans (congrArg ProofTree.encode ht),
      (ProofTree.encode_decode _).symm.trans (congrArg ProofTree.encode hu)⟩

theorem concludes_unique {t : ProofTree} {p q : Formula}
    (hp : Concludes A B t p) (hq : Concludes A B t q) : p = q :=
  Option.some.inj ((ProofTree.concludes_conclusion hp).symm.trans
    (ProofTree.concludes_conclusion hq))

/-- Every fiber of the fold over a valid original tree is a singleton.
The induction is on that tree, not on a numerical search bound. -/
theorem codeToOld_fiber_unique {t : ProofTree} {p : Formula} (ht : Concludes A B t p) :
    ∀ x y : Point (constructed A B hA hB).a.left,
      ((codeToOld A B hA hB).f.left.toFun x).val = t.encode →
      ((codeToOld A B hA hB).f.left.toFun y).val = t.encode → x = y := by
  induction ht with
  | logical1 p q =>
    intro x y hx hy
    exact (code_root_logical1 A B hA hB p q x hx).trans
      (code_root_logical1 A B hA hB p q y hy).symm
  | logical2 p q r =>
    intro x y hx hy
    exact (code_root_logical2 A B hA hB p q r x hx).trans
      (code_root_logical2 A B hA hB p q r y hy).symm
  | logical3 p q =>
    intro x y hx hy
    exact (code_root_logical3 A B hA hB p q x hx).trans
      (code_root_logical3 A B hA hB p q y hy).symm
  | @positive z hz =>
    intro x y hx hy
    exact (code_root_positive A B hA hB z hz x hx).trans
      (code_root_positive A B hA hB z hz y hy).symm
  | @negative z hz =>
    intro x y hx hy
    exact (code_root_negative A B hA hB z hz x hx).trans
      (code_root_negative A B hA hB z hz y hy).symm
  | @mp t u p q ht hu iht ihu =>
    intro x y hx hy
    obtain ⟨p₁,q₁,a,b,ha,hb,hn,hat,hbu⟩ := code_root_mp A B hA hB x hx
    obtain ⟨p₂,q₂,c,d,hc,hd,hm,hct,hdu⟩ := code_root_mp A B hA hB y hy
    have hac : a = c := iht a c hat hct
    have hbd : b = d := ihu b d hbu hdu
    subst c
    subst d
    have hp : p₁ = p₂ := Formula.codingEquiv.injective (ha.symm.trans hc)
    subst p₂
    have hq : q₁ = q₂ := (Formula.imp.inj (Formula.codingEquiv.injective
      (hb.symm.trans hd))).2
    subst q₂
    exact hn.symm.trans hm

theorem codeToOld_bijective :
    Function.Bijective (codeToOld A B hA hB).f.left.toFun := by
  refine ⟨?_,codeToOld_surjective A B hA hB⟩
  intro x y h
  obtain ⟨p,hp⟩ := proofAt_valid A B hA hB ((codeToOld A B hA hB).f.left.toFun x)
  apply codeToOld_fiber_unique A B hA hB hp x y
  · exact (ProofTree.encode_decode _).symm
  · exact (congrArg Subtype.val h).symm.trans (ProofTree.encode_decode _).symm

/-- Bijectivity supplies a computable inverse in the numerical category, by its proved
conservative carrier functor. -/
instance codeToOld_underlying_isIso : IsIso (codeToOld A B hA hB).f.left := by
  have : IsIso (NumericalUnderlying.functor.map (codeToOld A B hA hB).f.left) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (codeToOld_bijective A B hA hB)
  exact isIso_of_reflects_iso (codeToOld A B hA hB).f.left NumericalUnderlying.functor

def codeToOldIso : NumericalDerivation.codeAlgebra (rules A B hA hB) ≅ algebra A B hA hB :=
  Endofunctor.Algebra.isoMk
    (Over.isoMk (asIso (codeToOld A B hA hB).f.left) (Over.w (codeToOld A B hA hB).f))
    (codeToOld A B hA hB).h

/-- The comparison is an isomorphism of the inference algebras, including the original
conclusion and every constructor. -/
def algebraIso : algebra A B hA hB ≅ NumericalDerivation.codeAlgebra (rules A B hA hB) :=
  (codeToOldIso A B hA hB).symm

def initial : IsInitial (algebra A B hA hB) :=
  (NumericalDerivation.codeInitial (rules A B hA hB)).ofIso (algebraIso A B hA hB).symm

def codeIso : proofObject A B hA hB ≅ NumericalDerivation.codeObject (rules A B hA hB) :=
  (Over.forget formulaObject).mapIso
    ((Endofunctor.Algebra.forget (rules A B hA hB).inference).mapIso (algebraIso A B hA hB))

theorem codeIso_conclusion :
    (codeIso A B hA hB).hom ≫ NumericalDerivation.codeConclusion (rules A B hA hB) =
      conclusion A B hA hB := Over.w (algebraIso A B hA hB).hom.f

theorem codeIso_inverse_conclusion :
    (codeIso A B hA hB).inv ≫ conclusion A B hA hB =
      NumericalDerivation.codeConclusion (rules A B hA hB) := Over.w (algebraIso A B hA hB).inv.f

theorem codeIso_constructor :
    (algebra A B hA hB).str ≫ (algebraIso A B hA hB).hom.f =
      (rules A B hA hB).inference.map (algebraIso A B hA hB).hom.f ≫
        (NumericalDerivation.codeAlgebra (rules A B hA hB)).str :=
  (algebraIso A B hA hB).hom.h.symm

theorem codeIso_inverse_constructor :
    (NumericalDerivation.codeAlgebra (rules A B hA hB)).str ≫ (algebraIso A B hA hB).inv.f =
      (rules A B hA hB).inference.map (algebraIso A B hA hB).inv.f ≫
        (algebra A B hA hB).str :=
  (algebraIso A B hA hB).inv.h.symm

theorem codeIso_roundtrip (x : Point (proofObject A B hA hB)) :
    (codeIso A B hA hB).inv.toFun ((codeIso A B hA hB).hom.toFun x) = x :=
  congrArg (fun f => f.toFun x) (codeIso A B hA hB).hom_inv_id

theorem codeIso_inverse_roundtrip (x : Point (NumericalDerivation.codeObject (rules A B hA hB))) :
    (codeIso A B hA hB).hom.toFun ((codeIso A B hA hB).inv.toFun x) = x :=
  congrArg (fun f => f.toFun x) (codeIso A B hA hB).inv_hom_id

theorem codeIso_inverse_word (x : Point (NumericalDerivation.codeObject (rules A B hA hB))) :
    ((codeIso A B hA hB).inv.toFun x).val =
      ((codeToOld A B hA hB).f.left.toFun x).val := rfl

theorem codeIso_node (n : Node A B (algebra A B hA hB).a) :
    (codeIso A B hA hB).hom.toFun
      ((algebra A B hA hB).str.left.toFun (nodeInput A B hA hB _ n)) =
      (NumericalDerivation.codeAlgebra (rules A B hA hB)).str.left.toFun
        (nodeInput A B hA hB _ (nodeMap A B (algebraIso A B hA hB).hom.f n)) := by
  have h := congrArg (fun f => f.left.toFun (nodeInput A B hA hB _ n))
    (codeIso_constructor A B hA hB)
  exact h.trans (congrArg (NumericalDerivation.codeAlgebra (rules A B hA hB)).str.left.toFun
    (nodeInput_map A B hA hB (algebraIso A B hA hB).hom.f n))

theorem codeIso_inverse_node (n : Node A B (NumericalDerivation.codeAlgebra (rules A B hA hB)).a) :
    (codeIso A B hA hB).inv.toFun
      ((NumericalDerivation.codeAlgebra (rules A B hA hB)).str.left.toFun
        (nodeInput A B hA hB _ n)) =
      (algebra A B hA hB).str.left.toFun
        (nodeInput A B hA hB _ (nodeMap A B (algebraIso A B hA hB).inv.f n)) :=
  codeToOld_node A B hA hB n

/-- The guarded source program has exactly the old successful six-tag
carrier as its domain. It is not asserted to halt on invalid tree codes. -/
def oldToCodeProgram : ℕ → Part ℕ := (codeIso A B hA hB).hom.restrictedProgram

def codeToOldProgram : ℕ → Part ℕ := (codeIso A B hA hB).inv.restrictedProgram

theorem oldToCodeProgram_partrec : Partrec (oldToCodeProgram A B hA hB) :=
  (codeIso A B hA hB).hom.restrictedProgram_partrec

theorem codeToOldProgram_partrec : Partrec (codeToOldProgram A B hA hB) :=
  (codeIso A B hA hB).inv.restrictedProgram_partrec

theorem oldToCodeProgram_graph (n k : ℕ) :
    k ∈ oldToCodeProgram A B hA hB n ↔
      ∃ x : Point (proofObject A B hA hB),x.val = n ∧
        ((codeIso A B hA hB).hom.toFun x).val = k :=
  (codeIso A B hA hB).hom.restrictedProgram_graph n k

theorem codeToOldProgram_graph (n k : ℕ) :
    k ∈ codeToOldProgram A B hA hB n ↔
      ∃ x : Point (NumericalDerivation.codeObject (rules A B hA hB)),x.val = n ∧
        ((codeIso A B hA hB).inv.toFun x).val = k :=
  (codeIso A B hA hB).inv.restrictedProgram_graph n k

theorem oldToCodeProgram_roundtrip (x : Point (proofObject A B hA hB)) :
    (oldToCodeProgram A B hA hB x.val).bind (codeToOldProgram A B hA hB) =
      Part.some x.val := by
  have h₁ := (codeIso A B hA hB).hom.restrictedProgram_apply x
  have h₂ := (codeIso A B hA hB).inv.restrictedProgram_apply ((codeIso A B hA hB).hom.toFun x)
  change oldToCodeProgram A B hA hB x.val =
    Part.some ((codeIso A B hA hB).hom.toFun x).val at h₁
  change codeToOldProgram A B hA hB ((codeIso A B hA hB).hom.toFun x).val =
    Part.some ((codeIso A B hA hB).inv.toFun ((codeIso A B hA hB).hom.toFun x)).val at h₂
  rw [h₁,Part.bind_some]
  exact h₂.trans (congrArg (fun y => Part.some y.val) (codeIso_roundtrip A B hA hB x))

theorem codeToOldProgram_roundtrip
    (x : Point (NumericalDerivation.codeObject (rules A B hA hB))) :
    (codeToOldProgram A B hA hB x.val).bind (oldToCodeProgram A B hA hB) =
      Part.some x.val := by
  have h₁ := (codeIso A B hA hB).inv.restrictedProgram_apply x
  have h₂ := (codeIso A B hA hB).hom.restrictedProgram_apply ((codeIso A B hA hB).inv.toFun x)
  change codeToOldProgram A B hA hB x.val =
    Part.some ((codeIso A B hA hB).inv.toFun x).val at h₁
  change oldToCodeProgram A B hA hB ((codeIso A B hA hB).inv.toFun x).val =
    Part.some ((codeIso A B hA hB).hom.toFun ((codeIso A B hA hB).inv.toFun x)).val at h₂
  rw [h₁,Part.bind_some]
  exact h₂.trans (congrArg (fun y => Part.some y.val) (codeIso_inverse_roundtrip A B hA hB x))

end CategoricalEssentialIncompleteness.V46.ForkDerivation.Component
