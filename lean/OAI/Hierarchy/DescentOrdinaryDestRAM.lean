import OAI.Hierarchy.DescentRawFieldOps
import OAI.Hierarchy.DescentVenueRAM

namespace OAI
/-! # Real indexed stores for the two cut original cables in every selected demand pair -/

namespace Hierarchy.DescentOrdinaryDestRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentVenueRAM
open scoped Fin.CommRing Classical
noncomputable section
variable {w n : ℕ}


/-- The matched-pair source table has nine words. Field one is the thick cable
and field two its thin partner. The two input parties are zero and two respectively. -/
structure Banks where
  pairs : Bank
  births : Bank
  dest : Bank
  outAddress : ℕ
  outValue : ℕ
namespace Banks
def left (t : Fin 2) := 1+t.val
def party (t : Fin 2) := 2*t.val
def record (S : Banks) (t : Fin 2) :=
  Expr.lookup S.pairs (add (times 9 .row) (.lit (left t)))
def pointer (S : Banks) (t : Fin 2) := add (.lit S.dest.base) (record S t)
def value (S : Banks) (t : Fin 2) :=
  Expr.lookup S.births (add (times 6 .row) (.lit (party t)))

def pass (S : Banks) (w n : ℕ) (t : Fin 2) :=
  ProtocolRAMGeneratedWrite.program w S.outAddress S.outValue n (pointer S t) (value S t)

structure Room (S : Banks) (w n : ℕ) : Prop where
  pair : S.pairs.Fits w S.outAddress
  birth : S.births.Fits w S.outAddress
  dest : S.dest.Fits w S.outAddress
  np : 9*n≤S.pairs.size
  nb : 6*n≤S.births.size
  scratch : S.outAddress+n≤S.outValue
  endRoom : S.outValue+n<2^w

structure Records (S : Banks) (t : Fin 2) (edge : Fin n→Fin S.dest.size) (site : Fin n→ℕ)
    (m : Memory w) : Prop where
  edgeField : ∀i,m (S.pairs.base+(9*i.val+left t))=(edge i).val
  siteField : ∀i,m (S.births.base+(6*i.val+party t))=site i

def after (S : Banks) (t : Fin 2) (edge : Fin n→Fin S.dest.size) (site : Fin n→ℕ) (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image S.outAddress S.outValue (pointer S t) (value S t)
    (fun i=>S.dest.base+(edge i).val) (fun i=>(site i:Word w)) m

theorem intermediate (S : Banks) (t : Fin 2) (room : Room S w n)
    (edge : Fin n→Fin S.dest.size) (site : Fin n→ℕ) (m : Memory w)
    (fields : Records S t edge site m) :
    (S.pass w n t).Exec m (S.after t edge site m)
      (ProtocolRAMGeneratedWrite.work n (S.pointer t) (S.value t)) := by
  have ef (i : Fin n) : (S.record t).eval m (i.val:Word w)=(edge i).val := by
    change S.pairs.read m ((times 9 .row).eval m _ + (left t:Word w))=_
    rw [times_eval]
    change S.pairs.read m ((9:Word w)*i.val+left t)=_
    rw [←Nat.cast_ofNat (R:=Word w) (n:=9),←Nat.cast_mul,←Nat.cast_add]
    have field : 9*i.val+left t < 9*n := by
      unfold left
      have row := i.isLt
      have side := t.isLt
      omega
    exact (bank_at S.pairs m (9*i.val+left t) (field.trans_le room.np) room.pair.2.1).trans
      (fields.edgeField i)
  have vf (i : Fin n) : (S.value t).eval m (i.val:Word w)=(site i:Word w) := by
    change S.births.read m ((times 6 .row).eval m _+(party t:Word w))=_
    rw [times_eval]
    change S.births.read m ((6:Word w)*i.val+party t)=_
    rw [←Nat.cast_ofNat (R:=Word w) (n:=6),←Nat.cast_mul,←Nat.cast_add]
    have field : 6*i.val+party t < 6*n := by
      unfold party
      have row := i.isLt
      have side := t.isLt
      omega
    exact (bank_at S.births m (6*i.val+party t) (field.trans_le room.nb) room.birth.2.1).trans
      (fields.siteField i)
  apply ProtocolRAMGeneratedWrite.run
  · simp [pointer,record,times,add,Expr.Fits,room.pair]
  · simp [value,times,add,Expr.Fits,room.birth]
  · exact room.scratch
  · exact room.endRoom
  · intro i; change (S.dest.base:Word w)+(S.record t).eval m _=_
    rw [ef,Nat.cast_add]
  · exact vf
  · intro i; have := (edge i).isLt; have := room.dest.2.2; have := room.scratch; have := room.endRoom; omega
  · intro i j; have := (edge j).isLt; have := room.dest.2.2; omega
  · intro i j; have := (edge j).isLt; have := room.dest.2.2; have := room.scratch; omega

theorem read (S : Banks) (t : Fin 2) (edge : Fin n→Fin S.dest.size) (inj : Function.Injective edge)
    (site : Fin n→ℕ) (m : Memory w) (i : Fin n) :
    S.after t edge site m (S.dest.base+(edge i).val)=site i :=
  ProtocolRAMGeneratedWrite.read _ _ _ _ _ _ _ (fun _ _ eqn=>inj (Fin.ext (Nat.add_left_cancel eqn))) i

theorem frame (S : Banks) (t : Fin 2) (e : Fin n→Fin S.dest.size) (s : Fin n→ℕ) (m : Memory w)
    (u : ℕ) (away : ∀i,u≠S.dest.base+(e i).val) (low : u<S.outAddress) (room : Room S w n) :
    S.after t e s m u=m u :=
  ProtocolRAMGeneratedWrite.frame _ _ _ _ _ _ _ _ away (Or.inl low) (Or.inl (by have := room.scratch; omega))

end Banks
export Banks (left party record pointer value pass Room Records after intermediate read frame)
end
end Hierarchy.DescentOrdinaryDestRAM

end OAI
