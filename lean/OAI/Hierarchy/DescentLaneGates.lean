import OAI.Hierarchy.DescentCanonicalScalars
import OAI.Hierarchy.DescentLanePortMap

namespace OAI
/-! # Powered ROM and equality requests with one affine operand per physical lane -/

namespace Hierarchy.DescentLaneGates
open Computability.BorderVNP.Crossing DescentKernelHistory DescentRotor DescentResetGates
open scoped Classical BigOperators
noncomputable section
variable {A B K : Type} {width : A→ℕ} {nextWidth : B→ℕ} {Y p : ℕ}

inductive LaneSource (p : ℕ) (width : A→ℕ) where
  | fixed (b : Bool)
  | wire (l : Lane p width)

def LaneSource.read (s : LaneSource p width) (x : BitRef width→Bool) : Word p := match s with
  | .fixed b=>fun _=>b
  | .wire l=>l.word x

def Op.value (o : Op Y p width) (f : CanonicalTag Y→List (List Bool)→K) (x : BitRef width→Bool) :=
  f o.tag (List.ofFn fun i=>wordList ((o.arg i).word x))

def fixedOp (b : Bool) : Op Y p width := ⟨.inr (.inl b),0,Fin.elim0⟩
def expectOp (t : Lane p width) (b : Bool) : Op Y p width := ⟨.inr (.inr (.inl b)),1,fun _=>t⟩
def equalOp : LaneSource p width→LaneSource p width→Op Y p width
  | .fixed a,.fixed b=>fixedOp (decide (a=b))
  | .wire l,.fixed b=>expectOp l b
  | .fixed b,.wire l=>expectOp l b
  | .wire l,.wire r=>⟨.inr (.inr (.inr ())),2,fun i=>if i=0 then l else r⟩

abbrev RowBit (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (v : Fin Y) := Σs : Slot c v,Fin (SlotWidth c C w v s)

/-- Argument order is part of the fixed small rotor menu, independent of every selected
occurrence, batch, epoch, packet list and physical embedding. -/
abbrev rowSerial (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (v : Fin Y) : RowBit c C w v ≃ Fin (Fintype.card (RowBit c C w v)) := Fintype.equivFin _

def rotorOp (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (perm : Equiv.Perm (Fin Y)) (v : Fin Y)
    (f : RowBit c C w v→Lane p width) : Op Y p width :=
  ⟨.inl (perm,v),Fintype.card (RowBit c C w v),fun i=>f ((rowSerial c C w v).symm i)⟩

theorem rotor_operand (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (perm : Equiv.Perm (Fin Y)) (v : Fin Y)
    (f : RowBit c C w v→Lane p width) (t : RowBit c C w v) :
    (rotorOp c C w perm v f).arg (rowSerial c C w v t)=f t := by simp [rotorOp]

def selectedKey (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (perm : Equiv.Perm (Fin Y)) (v : Fin Y)
    (digit : ℕ) (args : List (List Bool)) :=
  let part (s : Slot c v):=bitWord (SlotWidth c C w v s) (fun k=>argumentBit args
    ((rowSerial c C w v ⟨s,k⟩).val) digit)
  key c C w (perm,⟨v,part (.inl false),part (.inl true),fun t=>part (.inr t)⟩)

/-- A powered gate reads the fixed ROM on all the columns in its actual lane. Equality gates compare
entire named columns. The field alphabet is identical at every group and powered width. -/
def scalar [CommSemiring K] (c : Fin Y→Fin Y→ℕ) (C w p : ℕ) (rom : Fin (Fintype.card (Entry c C w))→K) :
    CanonicalTag Y→List (List Bool)→K
  | .inl (perm,v),args=>∏d : Fin p,rom (selectedKey c C w perm v d.val args)
  | .inr (.inl b),_=>if b then 1 else 0
  | .inr (.inr (.inl b)),args=>if ∀d : Fin p,argumentBit args 0 d.val=b then 1 else 0
  | .inr (.inr (.inr ())),args=>if ∀d : Fin p,argumentBit args 0 d.val=argumentBit args 1 d.val then 1 else 0

variable [CommSemiring K] (c : Fin Y→Fin Y→ℕ) (C w : ℕ) (rom : Fin (Fintype.card (Entry c C w))→K)

theorem equal_read (hp : 0<p) (l r : LaneSource p width) (x : BitRef width→Bool) :
    (equalOp (Y:=Y) l r).value (scalar c C w p rom) x=if l.read x=r.read x then 1 else 0 := by
  let _ : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have all_const (a b : Bool) : (fun _ : Fin p=>a)=(fun _ : Fin p=>b) ↔ a=b :=
    ⟨fun eq=>congrFun eq ⟨0,hp⟩,fun eq=>congrArg (fun a=>fun _ : Fin p=>a) eq⟩
  cases l <;> cases r <;> simp [Op.value,equalOp,fixedOp,expectOp,scalar,LaneSource.read,argumentBit,wordList,
    List.ofFn_succ,all_const,funext_iff,eq_comm]

theorem rotor_read (perm : Equiv.Perm (Fin Y)) (v : Fin Y) (f : RowBit c C w v→Lane p width) (x : BitRef width→Bool) :
    (rotorOp c C w perm v f).value (scalar c C w p rom) x = ∏d : Fin p,
      let z (s : Slot c v):=bitWord (SlotWidth c C w v s) (fun j=>(f ⟨s,j⟩).word x d)
      rom (key c C w (perm,⟨v,z (.inl false),z (.inl true),fun t=>z (.inr t)⟩)) := by
  let ord := rowSerial c C w v
  let row (q : RowBit c C w v) := wordList ((f q).word x)
  let words := List.ofFn (fun i => row (ord.symm i))
  have select (q : RowBit c C w v) : words.getD (ord q).val [] = row q :=
    (finiteWord_read (fun i => row (ord.symm i)) (ord q) []).trans
      (congrArg row (ord.symm_apply_apply q))
  change (∏ d : Fin p, rom (selectedKey c C w perm v d.val words)) = _
  apply Finset.prod_congr rfl
  intro d _
  have read (q : RowBit c C w v) :
      argumentBit words ((rowSerial c C w v) q).val d.val = (f q).word x d := by
    change (words.getD (ord q).val []).getD d.val false = _
    rw [select q]
    exact finiteWord_read ((f q).word x) d false
  simp only [selectedKey, read]

theorem Program.read (q : Program Y p width) (f : CanonicalTag Y→List (List Bool)→K) (x : BitRef width→Bool) :
    q.recipe.value f x=∏i,(q.op i).value f x := by
  change (∑_ : (i:Empty)→Word (Empty.elim i),∏i,(q.op i).value f x)=_
  simp

theorem equal_arity (l r : LaneSource p width) : (equalOp (Y:=Y) l r).arity≤2 := by
  cases l <;> cases r <;> simp [equalOp,fixedOp,expectOp]

theorem equal_stride (l r : LaneSource p width) (b : ℕ)
    (hl : ∀t,l=.wire t→t.stride≤b) (hr : ∀t,r=.wire t→t.stride≤b) (i : Fin (equalOp (Y:=Y) l r).arity) :
    ((equalOp (Y:=Y) l r).arg i).stride≤b := by
  rcases l with v|l <;> rcases r with u|r
  · exact i.elim0
  · exact hr r rfl
  · exact hl l rfl
  · change Fin 2 at i
    change (if i = (0 : Fin 2) then l else r).stride ≤ b
    split <;> first | exact hl _ rfl | exact hr _ rfl

theorem Program.transport_recipe (z : Program Y p width) (f : PortMap width nextWidth) :
    (z.transport f).recipe=z.recipe.reroute f.bit := rfl

end
end Hierarchy.DescentLaneGates

end OAI
