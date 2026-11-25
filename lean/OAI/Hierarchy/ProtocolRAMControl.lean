import OAI.Hierarchy.ProtocolRAMPacked
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProtocolRAMAddEmit

namespace OAI
/-! # Reporting the endpoints and current local gate choice of a native run -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

variable {w n q d : ℕ}

/-- Interpret the finite descriptor fields in the memory left by the actual earlier
passes. Every field is thereby a word-sized natural number. -/
def rowAt (fields : Fin 7 → Expr) (m : Memory w) (r : Word w) : ProtocolRAMEmit.Row :=
  let col (j : Fin 7) := ((fields j).eval m r).val
  ⟨col 0,col 1,col 2,col 3,col 4,col 5,col 6⟩

theorem rowAt_field (fields : Fin 7 → Expr) (m : Memory w) (r : Word w) (j : Fin 7) :
    (rowAt fields m r).field j = ((fields j).eval m r).val := by
  fin_cases j <;> rfl

def controller (w src dst n : ℕ) (owners : Bank) (phases : List Pass) (fields : Fin 7 → Expr) : Procedure w :=
  ((program w phases).seq ((report src n owners fields).procedure w)).seq
    (ProtocolRAMAddEmit.emit w src dst n)

def reportedRows (phases : List Pass) (fields : Fin 7 → Expr) (m : Memory w) :
    Fin n → ProtocolRAMEmit.Row :=
  fun i => rowAt fields (result phases m) (i.val:Word w)

/-- The shared occurrence number is the actual ordinal on the term's record tape.
In particular, equal geometric endpoints do not identify two distinct occurrences. -/
theorem reported_id (phases : List Pass) (link : Link) (b : Batch q d) (tab : Fin q → Expr)
    (m : Memory w) (i : Fin n) (fits : link.idBase+n ≤ 2^w) :
    (reportedRows phases (link.fields b tab) m i).link = link.idBase+i.val := by
  change (RowOp.add.opcode.eval (link.idBase:Word w) (i.val:Word w)).val = _
  have hi := i.isLt
  simp only [RowOp.opcode,BinaryOp.eval,←Nat.cast_add,Fin.val_cast_of_lt (show link.idBase+i.val<2^w by omega)]

theorem reported_id_injective (phases : List Pass) (link : Link) (b : Batch q d) (tab : Fin q → Expr)
    (m : Memory w) (fits : link.idBase+n ≤ 2^w) :
    Function.Injective (fun i : Fin n => (reportedRows phases (link.fields b tab) m i).link) := by
  intro i j eqn
  change (reportedRows phases (link.fields b tab) m i).link =
    (reportedRows phases (link.fields b tab) m j).link at eqn
  rw [reported_id phases link b tab m i fits,reported_id phases link b tab m j fits] at eqn
  exact Fin.ext (by omega)

theorem reported_width_bound (phases : List Pass) (link : Link) (b : Batch q d) (tab : Fin q → Expr)
    (m : Memory w) (i : Fin n) (qFit : q≤2^w) (copiesFit : b.copies<2^w)
    (sumFit : q*b.copies<2^w) :
    (reportedRows phases (link.fields b tab) m i).width ≤ b.maxWidth*b.copies :=
  b.wire_bound (result phases m) (i.val:Word w) tab qFit copiesFit sumFit

theorem reported_width_capacity (phases : List Pass) (link : Link) (b : Batch q d)
    (tab : Fin q → Expr) (m : Memory w) (i : Fin n) (payload batchFactor : ℕ)
    (quota : b.copies≤batchFactor*payload) (qFit : q≤2^w) (copiesFit : b.copies<2^w)
    (sumFit : q*b.copies<2^w) :
    (reportedRows phases (link.fields b tab) m i).width ≤ (b.maxWidth*batchFactor)*payload :=
  (reported_width_bound phases link b tab m i qFit copiesFit sumFit).trans (by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ quota)

/-- For the phase's prescribed J=floor(payload/(K*packetWidth)), the number of
transport units per physical row is bounded by the fixed catalogue coefficient. -/
theorem reported_floor_width (phases : List Pass) (link : Link) (template : Batch q d) (tab : Fin q → Expr)
    (m : Memory w) (i : Fin n) (K packetWidth payload : ℕ) (qFit : q≤2^w)
    (copiesFit : payload/(K*packetWidth)<2^w) (sumFit : q*(payload/(K*packetWidth))<2^w) :
    let b := {template with copies := payload/(K*packetWidth)}
    (reportedRows phases (link.fields b tab) m i).width ≤ template.maxWidth*payload := by
  let b := {template with copies := payload/(K*packetWidth)}
  exact (reported_width_bound phases link b tab m i qFit copiesFit sumFit).trans <|
    Nat.mul_le_mul_left template.maxWidth (Nat.div_le_self _ _)

def finalMemory (src dst n : ℕ) (owners : Bank) (phases : List Pass) (fields : Fin 7 → Expr)
    (m : Memory w) : Memory w :=
  ProtocolRAMEmit.emitted dst (reportedRows (n:=n) phases fields m)
    ((report src n owners fields).apply (result phases m))

/-- The complete native prefix runs directly from the supplied initial memory. The
three output tables are its genuine terminal memory image, including dormant rows. -/
theorem controller_exec (src dst n : ℕ) (owners : Bank) (phases : List Pass) (fields : Fin 7 → Expr)
    (m : Memory w) (fits : ∀ p ∈ phases, p.Fits w) (wide : 3<w)
    (dir : Owners owners n (result phases m)) (inputFits : (packed owners fields).Fits w src) (srcFit : src+8*n<2^w)
    (dstFit : dst+9*n<2^w) (apart : src+8*n≤dst ∨ dst+9*n≤ src) :
    (controller w src dst n owners phases fields).Exec m (finalMemory src dst n owners phases fields m)
      ((clock phases + (report src n owners fields).clock) + (27+117*n)) := by
  let m' := result phases m
  let words := (report src n owners fields).apply m'
  let records := reportedRows (n:=n) phases fields m
  have original : (program w phases).Exec m m' (clock phases) := program_exec phases m fits
  have compiled : ((report src n owners fields).procedure w).Exec m' words (report src n owners fields).clock :=
    scan_exec src (8*n) (packed owners fields) m' inputFits srcFit
  have source : ProtocolRAMAddEmit.Packed src records words := by
    intro i j
    rw [show words (src+8*i.val+j.val) = (fields j).eval m' (i.val:Word w) from
      report_read src n owners fields m' i j wide srcFit dir]
    simp [records,reportedRows,rowAt_field,m']
  apply Procedure.Exec.then (Procedure.Exec.then original compiled)
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact ProtocolRAMAddEmit.emit_exec src dst records words source srcFit dstFit apart
    M pc reg pub exit rom data cfg start entry same

/-- The fixed row directory is installed once as advice, before execution of any
phase. The capacity, location and one word per entry give its entire representation. -/
theorem owners_after {w : ℕ} (phases : List Pass) (owners : Bank) (n : ℕ) (m : Memory w)
    (room : 8*n<2^w) (capacity : 8*n≤owners.size)
    (immutable : ∀ p∈phases, owners.base+owners.size ≤ p.out) :
    Owners owners n (result phases (ownerAdvice owners n m)) := by
  intro i j
  have positive : 0<owners.size := Nat.two_pow_pos owners.bits
  have addr := Nat.mod_lt (((8*i.val+j.val : ℕ):Word w).val) positive
  change result phases (ownerAdvice owners n m)
    (owners.base+(((8*i.val+j.val:ℕ):Word w).val)%owners.size) = _
  rw [result_below phases _ _ (by
    intro p hp
    have safe := immutable p hp
    exact (Nat.add_lt_add_left addr owners.base).trans_le safe)]
  exact ownerAdvice_correct owners n m room capacity i j

private theorem fieldLoop_cheap {A : Procedure w} (cheap : ProtocolRAMFieldLoop.CheapCode A) :
    CheapCode A := by
  intro P R K pc reg pub exit i
  exact ProtocolRAMAddEmit.cheapCPU _ (cheap pc reg pub exit i)

section
attribute [local irreducible] CheapCode

/-- The opcode restriction covers the instructions actually installed in the CPU,
including the descriptor expression compiler and all nine final gather passes. -/
theorem controller_cheap (w src dst n : ℕ) (owners : Bank) (phases : List Pass)
    (fields : Fin 7 → Expr) : CheapCode (controller w src dst n owners phases fields) := by
  unfold controller
  let reportCode := scan w src (8*n) (packed owners fields)
  let emitCode := ProtocolRAMAddEmit.emit w src dst n
  exact @cheap_seq w ((program w phases).seq reportCode) emitCode
    (@cheap_seq w (program w phases) reportCode (@program_cheap w phases)
      (@scan_cheap w src (8*n) (packed owners fields)))
    (@fieldLoop_cheap w emitCode (@ProtocolRAMAddEmit.emit_cheap w src dst n))

end


end Hierarchy.ProtocolRAM

end OAI
