import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # One physical host-register update for each distinct exterior ancestry -/

namespace Hierarchy.DescentExteriorReplay
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- The old host row and the digit of this common frozen address select one
actual host key. A reset also reads the newly issued sparse-to-dense directory. -/
structure Hop where
  source : Bank
  hostBase : Bank
  frozenDigit : Bank
  localShape : Bank
  compact : Option Bank
  dest : Bank

def key (H : Hop) : Expr :=
  .op .add (.lookup H.hostBase (.lookup H.source .row))
    (.lookup H.localShape (.lookup H.frozenDigit .row))

def read (H : Hop) : Expr :=
  match H.compact with
  | none=>key H
  | some bank=>.lookup bank (key H)

variable {w n : ℕ}
theorem read_ordinary (H : Hop) (kind : H.compact=none) (m : Memory w) (row : Fin n)
    (ancestor offset : ℕ) (digit : Word w) (a : H.source.read m (row.val:Word w)=(ancestor:Word w))
    (s : H.frozenDigit.read m (row.val:Word w)=digit)
    (base : ℕ) (b : H.hostBase.read m (ancestor:Word w)=(base:Word w))
    (d : H.localShape.read m digit=(offset:Word w)) :
    (read H).eval m (row.val:Word w)=((base+offset:ℕ):Word w) := by
  simp [read,kind,key,Expr.eval,RowOp.opcode,BinaryOp.eval,a,s,b,d,Nat.cast_add]

theorem read_reset (H : Hop) (bank : Bank) (kind : H.compact=some bank) (m : Memory w) (row : Fin n)
    (ancestor offset : ℕ) (digit : Word w) (a : H.source.read m (row.val:Word w)=(ancestor:Word w))
    (s : H.frozenDigit.read m (row.val:Word w)=digit)
    (base : ℕ) (b : H.hostBase.read m (ancestor:Word w)=(base:Word w))
    (d : H.localShape.read m digit=(offset:Word w)) (ordinal : ℕ)
    (observed : bank.read m ((base+offset:ℕ):Word w)=(ordinal:Word w)) :
    (read H).eval m (row.val:Word w)=(ordinal:Word w) := by
  simp [read,kind,key,Expr.eval,RowOp.opcode,BinaryOp.eval,a,s,b,d,←Nat.cast_add,observed]

def code (w n : ℕ) (H : Hop) := scan w H.dest.base n (read H)
def result (n : ℕ) (H : Hop) (m : Memory w) := image H.dest.base n (read H) m
def cost (n : ℕ) (H : Hop) := 4+n*(2*(read H).work+4)
structure Room (w n : ℕ) (H : Hop) : Prop where
  reads : (read H).Fits w H.dest.base
  write : H.dest.base+n<2^w

theorem run (n : ℕ) (H : Hop) (m : Memory w) (ok : Room w n H) :
    (code w n H).Exec m (result n H m) (cost n H) ∧ CheapCode (code w n H) :=
  ⟨@scan_exec w H.dest.base n (read H) m ok.reads ok.write,@scan_cheap w H.dest.base n (read H)⟩

theorem physical (H : Hop) (m : Memory w) (i : Fin n) :
    result n H m (H.dest.base+i.val)=(read H).eval m (i.val:Word w) := by
  have lo : H.dest.base≤H.dest.base+i.val:=by omega
  have hi : H.dest.base+i.val<H.dest.base+n:=by have:=i.isLt;omega
  simp [result,image,fillSegment,lo,hi]

theorem early (H : Hop) (m : Memory w) {a : ℕ} (lo : a<H.dest.base) :
    result n H m a=m a :=by simp [result,image,fillSegment,Nat.not_le_of_lt lo]

theorem price (n : ℕ) (H : Hop) : cost n H≤4+96*n := by
  obtain ⟨a,b,c,d,x,f⟩:=H
  cases x <;> simp only [cost,read,key,Expr.work] <;> omega

def steps (w n : ℕ) : List Hop → Procedure w
  | []=>scan w 0 0 .row
  | h::t=>(code w n h).seq (steps w n t)
def final (n : ℕ) : List Hop → Memory w → Memory w
  | [],m=>m
  | h::t,m=>final n t (result n h m)
def clocks (n : ℕ) : List Hop → ℕ
  | []=>4
  | h::t=>cost n h+clocks n t

theorem control (n : ℕ) (hs : List Hop) (m : Memory w) (room : ∀H∈hs,Room w n H) :
    (steps w n hs).Exec m (final n hs m) (clocks n hs) ∧ CheapCode (steps w n hs) := by
  induction hs generalizing m with
  | nil=>
    have empty : (scan w 0 0 .row).Exec m (image 0 0 .row m) 4 :=
      @scan_exec w 0 0 Expr.row m trivial (by simp)
    have blank : image 0 0 .row m=m := by funext a;simp [image,fillSegment]
    rw [blank] at empty
    exact ⟨@empty,@scan_cheap w 0 0 .row⟩
  | cons h t ih=>
    have x:=run n h m (room _ (by simp))
    have y:=ih (result n h m) (fun H mem=>room _ (by simp [mem]))
    exact ⟨Procedure.Exec.then x.1 y.1,@cheap_seq _ (code w n h) (steps w n t) x.2 y.2⟩

theorem total_price (n : ℕ) (hs : List Hop) : clocks n hs≤hs.length*(4+96*n)+4 := by
  induction hs with
  | nil=>simp [clocks]
  | cons h t ih=>
    change cost n h+clocks n t ≤ (t.length+1)*(4+96*n)+4
    rw [Nat.succ_mul]
    have one:=price n h
    omega

end
end Hierarchy.DescentExteriorReplay

end OAI
