import OAI.Hierarchy.ProtocolRAMControl
import OAI.Hierarchy.ProtocolRAMScalarCounts

namespace OAI
/-! # Short-key slice lookup following the actual adaptive descriptor program -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

/-- The gate bank starts at column two of the first emitted gate triple.
The pointer bank has one word per menu, giving the offset of its table row.
It avoids general multiplication in the scalar-table lookup CPU. -/
def sliceLookup (gate payload pointer table : Bank) : Expr :=
  .lookup table (.op .add (.lookup pointer (.lookup gate
    (.op .add .row (.op .add .row .row)))) (.lookup payload .row))

theorem sliceLookup_work (gate payload pointer table : Bank) :
    (sliceLookup gate payload pointer table).work=31 := rfl

variable {w n menus radix : ℕ}

private theorem bank_nat (b : Bank) (mem : Memory w) (a : ℕ) (idx : a<b.size) (room : b.size<2^w) :
    b.read mem (a:Word w)=mem (b.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (idx.trans room),Nat.mod_eq_of_lt idx]

theorem sliceLookup_eval (gate payload pointer table : Bank) (out : ℕ)
    (gateFit : gate.Fits w out) (payloadFit : payload.Fits w out)
    (ptrFit : pointer.Fits w out) (tableFit : table.Fits w out)
    (gates : 3*n≤gate.size) (payloads : n≤payload.size)
    (ptrs : menus≤pointer.size) (entries : menus*radix≤table.size)
    (menu : Fin n → Fin menus) (chunk : Fin n → Fin radix) (entry : Fin menus → Fin radix → Word w)
    (mem : Memory w)
    (gateCol : ∀ i:Fin n, mem (gate.base+3*i.val)=((menu i).val:Word w))
    (chunkCol : ∀ i:Fin n, mem (payload.base+i.val)=((chunk i).val:Word w))
    (starts : ∀ a:Fin menus, mem (pointer.base+a.val)=((a.val*radix:ℕ):Word w))
    (values : ∀ (a:Fin menus) (b:Fin radix), mem (table.base+(a.val*radix+b.val))=entry a b)
    (i : Fin n) :
    (sliceLookup gate payload pointer table).eval mem (i.val:Word w)=entry (menu i) (chunk i) := by
  have ptr := Nat.mul_le_mul_right radix (menu i).isLt
  rw [Nat.succ_mul] at ptr
  have index : (menu i).val*radix+(chunk i).val<table.size := by have := (chunk i).isLt; omega
  simp only [sliceLookup,Expr.eval,RowOp.opcode,BinaryOp.eval]
  rw [←Nat.cast_add,←Nat.cast_add,show i.val+(i.val+i.val)=3*i.val by omega,
    bank_nat gate mem _ (by have := i.isLt; omega) gateFit.2.1,gateCol,
    bank_nat pointer mem _ ((menu i).isLt.trans_le ptrs) ptrFit.2.1,starts,
    bank_nat payload mem _ (i.isLt.trans_le payloads) payloadFit.2.1,chunkCol,←Nat.cast_add,
    bank_nat table mem _ index tableFit.2.1,values]

theorem final_gate (src dst : ℕ) (owners gate : Bank) (phases : List Pass)
    (fields : Fin 7 → Expr) (mem : Memory w) (gateBase : gate.base=dst+6*n+2) (i : Fin n) :
    finalMemory src dst n owners phases fields mem (gate.base+3*i.val)=
      ((reportedRows phases fields mem i).menu:Word w) := by
  rw [gateBase,show dst+6*n+2+3*i.val=dst+6*n+3*i.val+2 by omega]
  exact (ProtocolRAMEmit.emitted_read dst (reportedRows phases fields mem)
    ((report src n owners fields).apply (result phases mem)) i (2:Fin 3)).2.2

set_option maxRecDepth 8192 in
theorem request_histogram_cheap (w src base bins n : ℕ) :
    CheapCode ((ProtocolRAMScalarCounts.clear w base bins).seq
      (ProtocolRAMScalarCounts.counting w src base n)) := by
  apply cheap_seq (scan_cheap w base bins (.lit 0))
  intro P R K pc reg pub exit i
  change Fin 13 at i
  fin_cases i <;> exact True.intro

/-- The descriptor prefix and forward slice scan share the cheap CPU
alphabet. The added tape is one offset per menu and one common lookup table. -/
theorem controller_slice {src dst out : ℕ} (owners : Bank) (phases : List Pass) (fields : Fin 7 → Expr)
    (mem : Memory w) (fits : ∀ p∈phases,p.Fits w) (wide : 3<w)
    (dir : Owners owners n (result phases mem)) (packedFit : (packed owners fields).Fits w src)
    (input : src+8*n<2^w) (output : dst+9*n<2^w) (apart : src+8*n≤dst ∨ dst+9*n≤ src)
    (gate payload pointer table : Bank) (lookupFit : (sliceLookup gate payload pointer table).Fits w out)
    (room : out+n<2^w) :
    let cpu := (controller w src dst n owners phases fields).seq
      (scan w out n (sliceLookup gate payload pointer table))
    cpu.Exec mem (image out n (sliceLookup gate payload pointer table)
      (finalMemory src dst n owners phases fields mem))
      ((clock phases+(report src n owners fields).clock+(27+117*n))+(4+66*n)) ∧ CheapCode cpu := by
  let e := sliceLookup gate payload pointer table
  let mid := finalMemory src dst n owners phases fields mem
  let ctl := controller w src dst n owners phases fields
  constructor
  · have ticks : 4+n*(2*e.work+4)=4+66*n := by
      dsimp only [e]
      rw [sliceLookup_work]
      omega
    have step : (scan w out n e).Exec mid (image out n e mid) (4+66*n) := by
      rw [←ticks]
      exact @scan_exec w out n e mid lookupFit room
    exact @Procedure.Exec.then w ctl (scan w out n e) mem mid (image out n e mid) _ _
      (@controller_exec w src dst n owners phases fields mem fits wide dir packedFit input output apart)
      (@step)
  · exact @cheap_seq w ctl (scan w out n e) (@controller_cheap w src dst n owners phases fields)
      (@scan_cheap w out n e)

end Hierarchy.ProtocolRAM

end OAI
