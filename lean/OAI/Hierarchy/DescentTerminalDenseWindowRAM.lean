import OAI.Hierarchy.DescentTerminalDenseWindow
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # One cheap lookup per packed port row of a genuine ordered group -/

namespace Hierarchy.DescentTerminalDenseWindowRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM
open PhysicalProcedure ProtocolRAM DescentTerminalDenseWindow
open scoped BigOperators Fin.CommRing
noncomputable section

/-- The raw pointer is in units of entire short rows. A radix-offset
lookup concatenates the two payload words while preserving the CPU's
bounded-cost opcode restriction. The control, the first-address and the
two advice-offset tables each use one field. -/
def row (indices control raw menuStart highField table : Bank) : Expr :=
  let base := Expr.lookup indices .row
  let lo := Expr.lookup raw base
  let hi := Expr.lookup raw (.op .add base (.lit 1))
  .lookup table (.op .add (.lookup menuStart (.lookup control .row))
    (.op .add (.lookup highField lo) hi))

theorem row_work (i c r m h t : Bank) : (row i c r m h t).work=50 := rfl

def program (bits out n : ℕ) (i c r m h t : Bank) := scan bits out n (row i c r m h t)

variable {bits q p n : ℕ}
def radix (q p : ℕ) := 2^(q*p)
def offsets (bits a stride : ℕ) : Vector (Word bits) a := Vector.ofFn (fun i=>((i.val*stride : ℕ):Word bits))

def Inputs (indices control raw menuStart highField table : Bank) (firstIndex : Fin n→ℕ)
    (fmt : Fin n→Format q p) (data : ℕ→Word (q*p)) (mem : Memory bits) : Prop :=
  (∀i : Fin n,mem (indices.base+i.val)=(firstIndex i:Word bits)) ∧
  (∀i : Fin n,mem (control.base+i.val)=((formatIndex q p (fmt i)).val:Word bits)) ∧
  (∀r<raw.size,mem (raw.base+r)=((data r).val:Word bits)) ∧
  (∀v : Fin (Menus q p),mem (menuStart.base+v.val)=(offsets bits (Menus q p) (radix q p*radix q p))[v.val]) ∧
  (∀u : Word (q*p),mem (highField.base+u.val)=(offsets bits (radix q p) (radix q p))[u.val]) ∧
  ∀(v : Fin (Menus q p)) (lo hi : Word (q*p)),
    mem (table.base+(v.val*(radix q p*radix q p)+(lo.val*radix q p+hi.val)))=entry bits q p v lo hi

private theorem bank_nat (b : Bank) (mem : Memory bits) (a out : ℕ) (valid : a<b.size) (fit : b.Fits bits out) :
    b.read mem (a:Word bits)=mem (b.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (valid.trans fit.2.1),Nat.mod_eq_of_lt valid]

theorem row_eval {out : ℕ} (ib cb raw ptr sh tab : Bank)
    (fits : ∀b∈[ib,cb,raw,ptr,sh,tab],b.Fits bits out)
    (indices : n ≤ ib.size) (ctl : n ≤ cb.size)
    (menuRoom : Menus q p ≤ ptr.size) (shiftRoom : radix q p ≤ sh.size)
    (tableRoom : Menus q p*(radix q p*radix q p) ≤ tab.size)
    (idx : Fin n→ℕ) (valid : ∀i,idx i+1<raw.size) (fmt : Fin n→Format q p)
    (data : ℕ→Word (q*p)) (m : Memory bits) (input : Inputs ib cb raw ptr sh tab idx fmt data m) (i : Fin n) :
    (row ib cb raw ptr sh tab).eval m (i.val:Word bits)=entry bits q p
      (formatIndex q p (fmt i)) (data (idx i)) (data (idx i+1)) := by
  obtain ⟨ix,co,rawCol,offsetsCol,shiftCol,tableCol⟩ := input
  let v := formatIndex q p (fmt i)
  let a := data (idx i)
  let b := data (idx i+1)
  have ab : a.val*radix q p+b.val<radix q p*radix q p := by
    have ha : a.val+1≤radix q p := a.isLt
    have bound := Nat.mul_le_mul_right (radix q p) ha
    rw [Nat.succ_mul] at bound
    have hb : b.val<radix q p := b.isLt
    exact (Nat.add_lt_add_left hb _).trans_le bound
  have keyRoom : v.val*(radix q p*radix q p)+(a.val*radix q p+b.val)<tab.size := by
    have bound := Nat.mul_le_mul_right (radix q p*radix q p) v.isLt
    rw [Nat.succ_mul] at bound
    omega
  simp only [row,Expr.eval,RowOp.opcode,BinaryOp.eval]
  rw [bank_nat cb _ _ out (i.isLt.trans_le ctl) (fits _ (by simp)),co,
    bank_nat ptr _ _ out (v.isLt.trans_le menuRoom) (fits _ (by simp)),offsetsCol,
    bank_nat ib _ _ out (i.isLt.trans_le indices) (fits _ (by simp)),ix,
    bank_nat raw _ _ out (by have := valid i;omega) (fits _ (by simp)),rawCol _ (by have := valid i;omega),
    bank_nat sh _ _ out (a.isLt.trans_le shiftRoom) (fits _ (by simp)),shiftCol]
  have nextAddress : (idx i : Word bits)+((1:ℕ):Word bits)=((idx i+1:ℕ):Word bits) :=
    (Nat.cast_add (R:=Word bits) (idx i) 1).symm
  rw [nextAddress,bank_nat raw _ _ out (valid i) (fits _ (by simp)),
    rawCol _ (valid i)]
  simp only [offsets,Vector.getElem_ofFn]
  rw [←Nat.cast_add,←Nat.cast_add,bank_nat tab _ _ out keyRoom (fits _ (by simp)),tableCol]

def file {n q p bits : ℕ} (out : ℕ) (idx : Fin n→ℕ) (fmt : Fin n→Format q p)
    (data : ℕ→Word (q*p)) (addr : ℕ) : Word bits := if h : addr-out<n then
  let i : Fin n := ⟨addr-out,h⟩
  entry bits q p (formatIndex q p (fmt i)) (data (idx i)) (data (idx i+1)) else 0

theorem output_bit (out : ℕ) (idx : Fin n→ℕ) (fmt : Fin n→Format q p) (data : ℕ→Word (q*p))
    (m : Memory bits) (i : Fin n) (j : Fin (q*p)) (fit : q*p ≤ bits) :
    wordBits bits (fillSegment out n (file out idx fmt data) m (out+i.val)) (j.castLE fit)=
      wordBits (q*p) (word (fmt i) (data (idx i)) (data (idx i+1))) j := by
  simp [fillSegment,file,show out+i.val<out+n by omega,i.isLt,entry_bits]

theorem spec (out : ℕ) (ib cb raw ptr sh tab : Bank)
    (fits : ∀b∈[ib,cb,raw,ptr,sh,tab],b.Fits bits out)
    (indices : n ≤ ib.size) (ctl : n ≤ cb.size)
    (menuRoom : Menus q p ≤ ptr.size) (shiftRoom : radix q p ≤ sh.size)
    (tableRoom : Menus q p*(radix q p*radix q p) ≤ tab.size)
    (idx : Fin n→ℕ) (valid : ∀i,idx i+1<raw.size) (fmt : Fin n→Format q p)
    (data : ℕ→Word (q*p)) (stop : out+n<2^bits) :
    (program bits out n ib cb raw ptr sh tab).Spec (Inputs ib cb raw ptr sh tab idx fmt data)
      (fun m after=>after=fillSegment out n (file out idx fmt data) m)
      (4+104*n) ∧ CheapCode (program bits out n ib cb raw ptr sh tab) := by
  refine ⟨?_,scan_cheap bits out n (row ib cb raw ptr sh tab)⟩
  have ef : (row ib cb raw ptr sh tab).Fits bits out := by
    simp only [row,Expr.Fits,fits ib (by simp),fits cb (by simp),fits raw (by simp),
      fits ptr (by simp),fits sh (by simp),fits tab (by simp),and_self]
  intro P R K M pc reg pub exit installed publicSlots cfg m start input
  obtain ⟨t,ht,z,dst,adv,finish,eqn⟩ := scan_exec out n (row ib cb raw ptr sh tab) m ef stop
    M pc reg pub exit installed publicSlots cfg m start rfl
  refine ⟨t,by simpa [row_work,Nat.mul_comm] using ht,z,dst,adv,finish,eqn.trans ?_⟩
  funext a
  by_cases h : out ≤ a ∧ a<out+n
  · have live : a-out<n := by omega
    let i : Fin n := ⟨a-out,live⟩
    have sub : (a:Word bits)-(out:Word bits)=(i.val:Word bits) := (Nat.cast_sub (R:=Word bits) h.1).symm
    simp only [image,fillSegment,ite_eq_left h,file,dite_eq_left live]
    rw [sub]
    exact row_eval ib cb raw ptr sh tab fits indices ctl menuRoom shiftRoom tableRoom idx valid fmt data m input i
  · simp [image,fillSegment,h]

/-- Both pointer ROMs and the complete table are paid once across the
entire branch. The number of machine scans is the number of physical
rows, irrespective of q and of the lengths read. -/
theorem charge {bits q p physical : ℕ} (room : formatBits q p+2*(q*p) ≤ bits/2) :
    Menus q p+radix q p+Menus q p*(radix q p*radix q p)+(4+104*physical) ≤
      3*2^(bits/2)+4+104*physical := by
  have main := table_room room
  have ctl := (format_room q p).trans (Nat.pow_le_pow_right (by decide) (show formatBits q p ≤ bits/2 by omega))
  have raw : 2^(q*p) ≤ 2^(bits/2) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold radix
  omega

end
end Hierarchy.DescentTerminalDenseWindowRAM

end OAI
