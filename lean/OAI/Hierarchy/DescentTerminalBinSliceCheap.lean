import OAI.Hierarchy.DescentTerminalBinReaddress
import OAI.Hierarchy.ProtocolRAMStackSlice

namespace OAI
/-! # The paid bin readdressing on the bounded-cost scalar RAM -/

namespace Hierarchy.DescentTerminalBinSliceCheap
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure ProtocolRAM DescentTerminalBinReaddress
open scoped Fin.CommRing BigOperators

variable {bits c K W q piece : ℕ}

/-- Consecutive offsets for the rows of the single immutable slice table. -/
def pointers (bits c d : ℕ) : Vector (Word bits) (2^c) :=
  Vector.ofFn (fun a=>((a.val*2^d : ℕ):Word bits))

def program (bits out len : ℕ) (gate payload pointer table : Bank) :=
  scan bits out len (sliceLookup gate payload pointer table)

def Inputs (gate payload pointer table : Bank) (addr : Address c W q)
    (ctl : Fin K→Tagged.Row c) (x : Fin K→Payload W q piece) (mem : Memory bits) : Prop :=
  (∀i : Fin (K*W),mem (gate.base+3*i.val)=((controls ctl i).val:Word bits)) ∧
  (∀i : Fin (K*W),mem (payload.base+i.val)=((chunks x i).val:Word bits)) ∧
  (∀a : Fin (2^c),mem (pointer.base+a.val)=(pointers bits c (sliceWidth W q piece))[a.val]'a.isLt) ∧
  (∀(a : Tagged.Row c) (b : Word (sliceWidth W q piece)),mem (table.base+(a.val*2^(sliceWidth W q piece)+b.val))=
    entry bits piece addr a b)

/-- The gate bank begins at the menu field in the first physical triple.
The scan reads row `i` at offset `i + (i + i)` and uses the menu's stored
pointer to locate its row in the slice table. -/
theorem spec (out : ℕ) (gate payload pointer table : Bank) (addr : Address c W q)
    (ctl : Fin K→Tagged.Row c) (x : Fin K→Payload W q piece)
    (hg : gate.Fits bits out) (hx : payload.Fits bits out)
    (hp : pointer.Fits bits out) (ht : table.Fits bits out)
    (gs : 3*(K*W) ≤ gate.size) (xs : K*W ≤ payload.size) (ps : 2^c ≤ pointer.size)
    (ts : 2^c*2^(sliceWidth W q piece) ≤ table.size) (room : out+K*W<2^bits) :
    (program bits out (K*W) gate payload pointer table).Spec (Inputs gate payload pointer table addr ctl x)
      (fun m dst=>dst=fillSegment out (K*W) (ProtocolStackLookup.outputWord out (controls ctl)
        (chunks x) (entry bits piece addr)) m) (4+66*(K*W)) ∧
      CheapCode (program bits out (K*W) gate payload pointer table) := by
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  have fit : (sliceLookup gate payload pointer table).Fits bits out := by
    simp only [sliceLookup,Expr.Fits,hg,hx,hp,ht,and_self]
  have ticks : 4+(K*W)*(2*(sliceLookup gate payload pointer table).work+4)=4+66*(K*W) := by
    rw [sliceLookup_work]
    omega
  intro P R T M pc reg pub exit installed data cfg m start h
  obtain ⟨t,htick,z,dst,adv,stop,eqn⟩ :=
    @scan_exec bits out (K*W) (sliceLookup gate payload pointer table) m fit room
      P R T M pc reg pub exit installed data cfg m start rfl
  rw [ticks] at htick
  refine ⟨t,htick,z,dst,adv,stop,eqn.trans ?_⟩
  funext a
  by_cases atRow : out ≤ a ∧ a<out+K*W
  · have valid : a-out<K*W := by omega
    let i : Fin (K*W) := ⟨a-out,valid⟩
    have sub : (a:Word bits)-(out:Word bits)=(i.val:Word bits) :=
      (Nat.cast_sub (R:=Word bits) atRow.1).symm
    simp only [image,fillSegment,ite_eq_left atRow,ProtocolStackLookup.outputWord,dite_eq_left valid,sub]
    exact sliceLookup_eval gate payload pointer table out hg hx hp ht gs xs ps ts (controls ctl) (chunks x)
      (entry bits piece addr) m h.1 h.2.1
      (fun a => by simpa only [pointers,Vector.getElem_ofFn] using h.2.2.1 a) h.2.2.2 i
  · simp [image,fillSegment,atRow]

theorem charge {S : ℕ} (fit : c+q*(W*piece) ≤ bits/2) (count : Fin S→ℕ) :
    2^c+2^c*2^(sliceWidth W q piece)+(4+66*(DescentTerminalBinPack.bins W count*W)) ≤
      2*2^(bits/2)+4+66*(2*(∑i,count i)+W) := by
  have lut := shared_words fit
  have ptrs : 2^c ≤ 2^(bits/2) := Nat.pow_le_pow_right (by decide) (by omega)
  have rows := DescentTerminalBinPack.paid W count
  unfold DescentTerminalBinPack.purchased at rows
  omega

end Hierarchy.DescentTerminalBinSliceCheap

end OAI
