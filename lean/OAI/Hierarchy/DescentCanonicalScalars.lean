import OAI.Hierarchy.DescentRotorAlphabet
import OAI.Hierarchy.DescentGateGather
import OAI.Hierarchy.DescentRotorRootRefs

namespace OAI
/-! # A shared scalar instruction alphabet for all physical reset sites -/

namespace Hierarchy.DescentResetGates
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRotor
open scoped Classical BigOperators
noncomputable section
variable {A B K : Type} {width : A→ℕ} {nextWidth : B→ℕ} {Y : ℕ}

/-- A real local bit or the fixed value of an unoccupied packet digit. -/
inductive Source (width : A→ℕ) where
  | bit (r : BitRef width)
  | fixed (value : Bool)

def Source.read (z : Source width) (x : BitRef width→Bool) := match z with
  | .bit p=>x p
  | .fixed b=>b

def Source.reroute (z : Source width) (f : BitRef width→BitRef nextWidth) : Source nextWidth := match z with
  | .bit p=>.bit (f p)
  | .fixed b=>.fixed b

theorem canonicalTag_card (Y : ℕ) : Fintype.card (CanonicalTag Y)=Y.factorial*Y+5 := by
  simp [CanonicalTag,Fintype.card_perm]

def argumentBit (args : List (List Bool)) (i j : ℕ) := (args.getD i []).getD j false

/-- The scalar engine determines a Boolean value or a shared table address without using any field data. -/
def canonicalRequest (c : Fin Y→Fin Y→ℕ) (C w : ℕ) :
    CanonicalTag Y→List (List Bool)→Request (Fin (Fintype.card (Entry c C w)))
  | .inl (perm,v),args=>
    let read (s : Slot c v) := bitWord (SlotWidth c C w v s) (fun j=>argumentBit args ((Fintype.equivFin (Slot c v) s).val) j.val)
    .lookup (key c C w (perm,⟨v,read (.inl false),read (.inl true),fun p=>read (.inr p)⟩))
  | .inr (.inl v),_=>.check v
  | .inr (.inr (.inl b)),args=>.check (decide (argumentBit args 0 0=b))
  | .inr (.inr (.inr ())),args=>.check (decide (argumentBit args 0 0=argumentBit args 1 0))

def canonicalScalar [Zero K] [One K] (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (rom : Fin (Fintype.card (Entry c C w))→K)
    (tag : CanonicalTag Y) (words : List (List Bool)) : K := (canonicalRequest c C w tag words).value rom

def fieldAddress (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (tag : CanonicalTag Y) (words : List (List Bool)) : Bool ⊕ Fin (Fintype.card (Entry c C w)) :=
  match canonicalRequest c C w tag words with
  | .lookup j=>.inr j
  | .check b=>.inl b

def dictionary [Zero K] [One K] (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (rom : Fin (Fintype.card (Entry c C w))→K) :
    Bool ⊕ Fin (Fintype.card (Entry c C w))→K := Sum.elim (fun b=>if b then 1 else 0) rom

theorem dictionary_read [Zero K] [One K] (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (rom : Fin (Fintype.card (Entry c C w))→K)
    (t : CanonicalTag Y) (words : List (List Bool)) : dictionary c C w rom (fieldAddress c C w t words)=canonicalScalar c C w rom t words := by
  unfold fieldAddress canonicalScalar
  cases canonicalRequest c C w t words <;> rfl

structure Operation (Y : ℕ) (width : A→ℕ) where
  tag : CanonicalTag Y
  arity : ℕ
  size : Fin arity→ℕ
  ref : (i : Fin arity)→Fin (size i)→BitRef width

def Operation.reroute (op : Operation Y width) (f : BitRef width→BitRef nextWidth) : Operation Y nextWidth :=
  {op with ref:=fun i j=>f (op.ref i j)}

def Operation.value (op : Operation Y width) (scalar : CanonicalTag Y→List (List Bool)→K) (x : BitRef width→Bool) :=
  scalar op.tag (List.ofFn fun i=>wordList (fun j=>x (op.ref i j)))

def fixedOp (b : Bool) : Operation Y width := ⟨.inr (.inl b),0,Fin.elim0,fun i _ => Fin.elim0 i⟩

def expectOp (p : BitRef width) (b : Bool) : Operation Y width := ⟨.inr (.inr (.inl b)),1,fun _=>1,fun _ _=>p⟩

def equalOp : Source width→Source width→Operation Y width
  | .fixed a,.fixed b=>fixedOp (decide (a=b))
  | .bit p,.fixed b=>expectOp p b
  | .fixed b,.bit p=>expectOp p b
  | .bit p,.bit q=>⟨.inr (.inr (.inr ())),2,fun _=>1,fun i _=>if i=0 then p else q⟩

def rotorOp (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (perm : Equiv.Perm (Fin Y)) (v : Fin Y)
    (f : (s : Slot c v)→Fin (SlotWidth c C w v s)→BitRef width) : Operation Y width :=
  let ord:=Fintype.equivFin (Slot c v)
  ⟨.inl (perm,v),Fintype.card (Slot c v),fun i=>SlotWidth c C w v (ord.symm i),fun i=>f (ord.symm i)⟩

def Operation.bitCount (op : Operation Y width) := ∑i,op.size i

theorem equalOp_bits (p q : Source width) : (equalOp (Y:=Y) p q).bitCount ≤ 2 := by
  have oneBit : (∑ _ : Fin 1, (1 : ℕ)) ≤ 2 := by simp
  cases p <;> cases q
  · exact (show (∑ _ : Fin 2, (1 : ℕ)) ≤ 2 by simp)
  · exact oneBit
  · exact oneBit
  · exact (show (∑ i : Fin 0, (Fin.elim0 i : ℕ)) ≤ 2 by simp)

theorem equalOp_arity (p q : Source width) : (equalOp (Y:=Y) p q).arity ≤ 2 := by
  cases p <;> cases q <;> simp [equalOp,fixedOp,expectOp]

theorem rotorOp_bits (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (perm : Equiv.Perm (Fin Y)) (v : Fin Y)
    (f : (s : Slot c v)→Fin (SlotWidth c C w v s)→BitRef width) :
    (rotorOp c C w perm v f).bitCount=∑s,SlotWidth c C w v s := by
  let slots := (Fintype.equivFin (Slot c v)).symm
  change (∑ i, SlotWidth c C w v (slots i)) = ∑ s, SlotWidth c C w v s
  exact slots.sum_comp (fun s => SlotWidth c C w v s)

variable [CommSemiring K] (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (rom : Fin (Fintype.card (Entry c C w))→K)

theorem equalOp_read (p q : Source width) (x : BitRef width→Bool) :
    (equalOp (Y:=Y) p q).value (canonicalScalar c C w rom) x=if p.read x=q.read x then 1 else 0 := by
  cases p <;> cases q <;>
    simp [Operation.value,equalOp,expectOp,fixedOp,canonicalScalar,canonicalRequest,
      Request.value,argumentBit,Source.read,wordList,List.ofFn_succ,eq_comm] <;>
    split_ifs <;> simp_all

theorem rotorOp_read (perm : Equiv.Perm (Fin Y)) (v : Fin Y) (f : (s : Slot c v)→Fin (SlotWidth c C w v s)→BitRef width) (x : BitRef width→Bool) :
    (rotorOp c C w perm v f).value (canonicalScalar c C w rom) x =
      let z (s : Slot c v):=bitWord (SlotWidth c C w v s) (fun j=>x (f s j))
      rom (key c C w (perm,⟨v,z (.inl false),z (.inl true),fun p=>z (.inr p)⟩)) := by
  let ord:=Fintype.equivFin (Slot c v)
  let row (s : Slot c v) := wordList (fun k => x (f s k))
  have select (s : Slot c v) :
      (List.ofFn (fun i => row (ord.symm i))).getD (ord s).val [] = row s :=
    (finiteWord_read (fun i => row (ord.symm i)) (ord s) []).trans
      (congrArg row (ord.symm_apply_apply s))
  have lookup (s : Slot c v) (j : Fin (SlotWidth c C w v s)) :
      argumentBit (List.ofFn fun i=>wordList fun k=>x (f (ord.symm i) k)) (ord s).val j.val=x (f s j) := by
    change ((List.ofFn (fun i => row (ord.symm i))).getD (ord s).val []).getD j.val false = _
    rw [select s]
    exact finiteWord_read (fun k => x (f s k)) j false
  simp [Operation.value,rotorOp,canonicalScalar,canonicalRequest,Request.value,lookup,ord]

structure Program (Y : ℕ) (width : A→ℕ) where
  Node : Type
  [finite : Fintype Node]
  op : Node→Operation Y width
attribute [instance] Program.finite

def Program.recipe (s : Program Y width) : BitRecipe (CanonicalTag Y) A width where
  Hidden := Empty
  hiddenWidth := Empty.elim
  Node := s.Node
  tag i := (s.op i).tag
  arity i := (s.op i).arity
  size i := (s.op i).size
  arg i j k := .inl ((s.op i).ref j k)

def Program.reroute (s : Program Y width) (f : BitRef width→BitRef nextWidth) : Program Y nextWidth :=
  { Node:=s.Node, op:=fun i=>(s.op i).reroute f }

theorem Program.reroute_recipe (s : Program Y width) (f : BitRef width→BitRef nextWidth) :
    (s.reroute f).recipe=s.recipe.reroute f := rfl

theorem Program.value (s : Program Y width) (scalar : CanonicalTag Y→List (List Bool)→K) (x : BitRef width→Bool) :
    s.recipe.value scalar x=∏i,(s.op i).value scalar x := by
  change (∑_ : (j:Empty)→Word (Empty.elim j),∏i,(s.op i).value scalar x)=_
  simp

theorem product_checks {I : Type} [Fintype I] (p : I→Prop) [DecidablePred p] :
    (∏i,if p i then (1:K) else 0) = if ∀i,p i then 1 else 0 := by
  by_cases h : ∀i,p i
  · simp [h]
  · obtain ⟨i,hi⟩:=not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end
end Hierarchy.DescentResetGates

end OAI
