import OAI.Computability.VPVNP.CompressorRegisterSetupClock
import OAI.Computability.VPVNP.PairSimulationReverseSlices
import OAI.Computability.VPVNP.PairSimulationSliceReads
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-!
# Native copying of all intervals of a resident operand

Each fixed local interval has a read-only pointer calculation, the three-word
slice header and a private copy loop. The direction selects which of the two
stored offsets belongs to the input. The instruction table is fixed before
the widths, descriptor addresses, or branch bits are supplied.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ResidentColumn

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open scoped Fin.CommRing
open private reads_append from OAI.Computability.VPVNP.CompressorFormulaFootprint

/-- A physical copy uses three dynamic pointers and a statically known orientation. -/
structure Setup where
  /-- Expression that computes the base address of the source interval in private memory. -/
  source : Expr
  /-- Expression that computes the destination buffer's base address before the header supplies
  its offset. -/
  destination : Expr
  /-- Expression that locates the first word of the external three-word slice header. -/
  frame : Expr
  /-- When true, apply the first stored offset to the destination and the second to the source.
  When false, apply them in source–destination order. -/
  reverse : Bool

/-- Initialize the six header registers in order with the source base, zero, destination base,
unit increment, zero and frame address. -/
def Setup.operands (s : Setup) : Fin 6 → Expr :=
  ![s.source, .lit 0, s.destination, .lit 1, .lit 0, s.frame]

/-- One resident copy interval, described by its two private buffer bases, its external header
address, the offset in each buffer and the bits to transfer. -/
structure Row where
  /-- Private buffer base to which the source offset is added before reading the first bit. -/
  source : ℕ
  /-- Base of the private buffer into which the row's bits are copied. -/
  destination : ℕ
  /-- External address of this row's offset pair, followed by its length word at `frame + 2`. -/
  frame : ℕ
  /-- Number of private cells from the source base to the first bit of this slice. -/
  sourceOffset : ℕ
  /-- Number of private cells from the destination base to the start of the copied slice. -/
  targetOffset : ℕ
  /-- Payload in increasing address order. Its length is the number of private cells to copy. -/
  bits : List Bool

/-- Store the row's payload one bit per private cell, starting at `destination + targetOffset`. -/
def Row.write {w : ℕ} (row : Row) (priv : Word w → Word w) :=
  PrivateFields.storeBits (row.destination + row.targetOffset) row.bits priv

/-- The private source cells starting at `source + sourceOffset` contain the word encodings of
the row's bits in order. -/
def Row.reads {w : ℕ} (row : Row) (priv : Word w → Word w) : Prop :=
  ∀ i : Fin row.bits.length, priv ((row.source + row.sourceOffset + i.val : ℕ) : Word w) =
    PrivateFields.bitValue w row.bits[i.val]

variable {N w p r k : ℕ}

/-- The setup expressions evaluate to the row's three pointers and the external header fits the
address space and records the payload length. For a nonempty slice, its two offset words
agree with the setup's orientation. -/
structure Row.Recorded (row : Row) (s : Setup) (pub : Fin 5 → Word w)
    (state : Word w) (mem : Memory w) : Prop where
  source : s.source.eval pub state mem = (row.source : Word w)
  destination : s.destination.eval pub state mem = (row.destination : Word w)
  frame : s.frame.eval pub state mem = (row.frame : Word w)
  frameFit : row.frame + 2 < 2 ^ w
  length : (mem (row.frame + 2)).val = row.bits.length
  offsets : 0 < row.bits.length → (mem row.frame).val =
      (if s.reverse then row.targetOffset else row.sourceOffset) ∧
    (mem (row.frame + 1)).val = (if s.reverse then row.sourceOffset else row.targetOffset)

/-- The physical read addresses needed by one compiled setup and its slice header. -/
structure Row.ReadSafe (row : Row) (setup : Setup) (allowed : ℕ → Prop)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) : Prop where
  loads : ∀ j, (setup.operands j).ReadsFrom allowed pub state mem
  frame : ∀ j : Fin 3, allowed (row.frame + j.val)

private theorem readSafe_true (row : Row) (setup : Setup)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) :
    row.ReadSafe setup (fun _ ↦ True) pub state mem := by
  have all (e : Expr) : e.ReadsFrom (fun _ ↦ True) pub state mem := by
    induction e with
    | lit | publicWord | state => trivial
    | load _ h => exact ⟨h, trivial⟩
    | binary _ _ _ h₁ h₂ => exact ⟨h₁, h₂⟩
  exact ⟨fun j ↦ all _, fun _ ↦ trivial⟩

private theorem frame_reads (row : Row) (setup : Setup) (allowed : ℕ → Prop)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
    (safe : row.ReadSafe setup allowed pub state mem) (fit : row.frame + 2 < 2 ^ w) :
    SourceTransport.Reads allowed (PrivateSlices.frameEvents mem row.frame row.bits) := by
  apply PrivateSlices.frameEvents_reads
  · rw [show (row.frame : Word w).val = row.frame from Nat.mod_eq_of_lt (by omega)]
    exact safe.frame 0
  · rw [← Nat.cast_add_one, show ((row.frame + 1 : ℕ) : Word w).val = row.frame + 1 from
      Nat.mod_eq_of_lt (by omega)]
    exact safe.frame 1
  · rw [← Nat.cast_add_one, ← Nat.cast_add_one,
      show ((row.frame + 1 + 1 : ℕ) : Word w).val = row.frame + 1 + 1 from Nat.mod_eq_of_lt fit]
    exact safe.frame 2

/-- The pivot separates source and destination buffers. Each nonempty source interval ends at
or before the pivot, the destination starts at or above it, and each nonempty destination
interval ends strictly below the word modulus. -/
structure Row.Fits (row : Row) (w pivot : ℕ) : Prop where
  old : 0 < row.bits.length → row.source + row.sourceOffset + row.bits.length ≤ pivot
  new : pivot ≤ row.destination
  room : 0 < row.bits.length → row.destination + row.targetOffset + row.bits.length < 2 ^ w

private theorem reads_write (x y : Row) (pivot : ℕ) (hx : x.Fits w pivot)
    (hy : y.Fits w pivot) (priv : Word w → Word w) (read : y.reads priv) :
    y.reads (x.write priv) := by
  intro j
  by_cases h : x.bits.length = 0
  · have nil := List.length_eq_zero_iff.mp h
    simpa [Row.write, nil, PrivateFields.storeBits] using read j
  have fit := hx.room (Nat.pos_of_ne_zero h)
  have old := hy.old (Nat.zero_lt_of_lt j.isLt)
  have addr := hx.new
  have hv : ((y.source + y.sourceOffset + j.val : ℕ) : Word w).val =
      y.source + y.sourceOffset + j.val := Nat.mod_eq_of_lt (by have := j.isLt; omega)
  rw [Row.write, PrivateFields.storeBits_outside _ _ _ _ fit.le (Or.inl (by rw [hv]; omega))]
  exact read j

variable (S : Fin N → Setup)

/-- Number of compiled instructions that evaluate the six setup operands for row `i`. -/
def setCount (i : Fin N) := (RegisterSetup.lines (S i).operands).length

/-- Instruction labels indexed by row, with separate ranges for its variable-length setup,
eleven header instructions and seven private copy instructions. -/
abbrev Label := (i : Fin N) × (Fin (setCount S i) ⊕ Fin 11 ⊕ Fin 7)

/-- Program counter for setup line `j` of row `i`, falling through to the first header
instruction once the setup lines are exhausted. -/
def setPC (loc : Label S → Fin p) (i : Fin N) (j : ℕ) : Fin p :=
  if h : j < setCount S i then loc ⟨i, .inl ⟨j, h⟩⟩ else loc ⟨i, .inr (.inl 0)⟩

/-- Relocate an index in row `i`'s eleven-instruction slice header to its machine program
counter. -/
def headPC (loc : Label S → Fin p) (i : Fin N) (j : Fin 11) := loc ⟨i, .inr (.inl j)⟩
/-- Locate one of the seven instructions of the private bit-copy loop for row `i`. -/
def copyPC (loc : Label S → Fin p) (i : Fin N) (j : Fin 7) := loc ⟨i, .inr (.inr j)⟩

/-- Entry counter for the row with ordinal `n`, or the supplied return counter once all rows
have been visited. -/
def start (loc : Label S → Fin p) (ret : Fin p) (n : ℕ) :=
  if h : n < N then setPC S loc ⟨n, h⟩ 0 else ret

variable (vm : ∀ i, Fin (RegisterSetup.regCount (S i).operands) ↪ Fin r) (inputs : Fin 6 → Fin r)

/-- Embed the six output registers of row `i`'s compiled setup into the enclosing machine
register file for use by the header and copy loop. -/
def reg (i : Fin N) : Fin 6 ↪ Fin r :=
  (⟨RegisterSetup.output (S i).operands, fun _ _ h ↦
    Fin.ext (congrArg (Fin.val (n := RegisterSetup.regCount (S i).operands)) h)⟩ :
    Fin 6 ↪ Fin _).trans (vm i)

/-- Decode a column label into a setup, oriented header or copy-loop instruction. Finishing a
slice transfers control to the following row or to the return counter. -/
def instruction (loc : Label S → Fin p) (ret : Fin p) : Label S → Instr w p r k
  | ⟨i, .inl j⟩ => RegisterSetup.instruction (vm i) inputs
      (RegisterSetup.lines (S i).operands)[j.val] (setPC S loc i (j.val + 1))
  | ⟨i, .inr (.inl j)⟩ => if (S i).reverse then
      ReverseSlices.instruction (headPC S loc i) (reg S vm i) (copyPC S loc i 0)
        (start S loc ret (i.val + 1)) j
    else PrivateSlices.instruction (headPC S loc i) (reg S vm i) (copyPC S loc i 0)
        (start S loc ret (i.val + 1)) j
  | ⟨i, .inr (.inr j)⟩ => PrivateFields.instruction .copy (copyPC S loc i)
      (PrivateSlices.copyRegs (reg S vm i)) (start S loc ret (i.val + 1)) j

theorem resize_instruction (loc : Label S → Fin p) (ret : Fin p) (l : Label S) :
    (instruction (w := 2) (k := k) S vm inputs loc ret l).resize w =
      instruction S vm inputs loc ret l := by
  rcases l with ⟨i, j | j | j⟩
  · exact RegisterSetup.resize_instruction ..
  · cases h : (S i).reverse <;> fin_cases j <;> simp [instruction, h, ReverseSlices.instruction,
      PrivateSlices.instruction, Instr.resize]
  · fin_cases j <;> rfl

variable {S vm inputs} (M : Machine w p r k) (loc : Label S → Fin p) (ret : Fin p)
variable (code : ∀ l, M.code (loc l) = instruction S vm inputs loc ret l)
variable (safe : ∀ i u j, vm i u ≠ inputs j)

/-- The complete trace of one gather frame, with arbitrary compiler registers normalized to zero. -/
def frameTrace (s : Setup) (row : Row) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) :=
  (RowRecipe.evaluate pub state m (RegisterSetup.lines s.operands) (fun _ ↦ 0)).1 ++
    PrivateSlices.frameEvents m row.frame row.bits

/-- The trace of a fixed row list in numerical visit order. -/
def trace (S : Fin N → Setup) (row : Fin N → Row) (is : List (Fin N))
    (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) :=
  is.flatMap fun i ↦ frameTrace (S i) (row i) pub state m

include code safe in
private theorem one (row : Row) (i : Fin N) (cfg : Config w p r) (m : Memory w)
    (pub : Fin 5 → Word w) (state : Word w)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state) (entry : cfg.pc = setPC S loc i 0)
    (recorded : row.Recorded (S i) pub state m) (pivot : ℕ) (fits : row.Fits w pivot)
    (read : row.reads cfg.privateMem) (allowed : ℕ → Prop)
    (sites : row.ReadSafe (S i) allowed pub state m) :
    ∃ events out, out.pc = start S loc ret (i.val + 1) ∧ out.privateMem = row.write cfg.privateMem ∧
      out.persistent = cfg.persistent ∧ (∀ j, out.reg (inputs j) = cfg.reg (inputs j)) ∧
      (∀ j, (∀ u, j ≠ vm i u) → out.reg j = cfg.reg j) ∧
      events.length ≤ setCount S i + 12 + 5 * row.bits.length ∧
      countProbes events ≤ (∑ j, ((S i).operands j).loads) + 3 ∧ choiceBits events = [] ∧
      SourceTransport.Reads allowed events ∧ events = frameTrace (S i) row pub state m ∧
      ∀ fuel more, execute M.program (fuel + events.length) cfg m more =
        (execute M.program fuel out m more).map (fun rep ↦ ⟨events ++ rep.events, rep.result⟩) := by
  let f := (S i).operands
  have link : RegisterSetup.Linked (vm i) inputs M (setPC S loc i) (RegisterSetup.lines f) := by
    intro j
    have hj : j.val < setCount S i := j.isLt
    rw [show setPC S loc i j.val = loc ⟨i, .inl j⟩ by rw [setPC, dite_eq_left hj]; rfl]
    exact code ⟨i, .inl j⟩
  let rs := fun j ↦ cfg.reg (vm i j)
  let ev := (RowRecipe.evaluate pub state m (RegisterSetup.lines f) rs).1
  have raw := RegisterSetup.execute_setup_raw f inputs (vm i) M m _ link (safe i) cfg entry
  dsimp only at raw
  rw [show (fun j : Fin 5 ↦ cfg.reg (inputs j.castSucc)) = pub from funext hp, hs] at raw
  obtain ⟨d, len, count, det, atHead, mem, pers, vals, unchanged, run⟩ := raw
  have loads := RegisterSetup.lines_reads f allowed pub state m sites.loads rs
  have startHead : d.pc = headPC S loc i 0 := by
    change d.pc = setPC S loc i (setCount S i) at atHead
    rw [atHead, setPC, dite_eq_right (Nat.lt_irrefl _)]
    rfl
  have h₀ : d.reg (reg S vm i 0) = (row.source : Word w) := (vals 0).trans recorded.source
  have h₂ : d.reg (reg S vm i 2) = (row.destination : Word w) := (vals 2).trans recorded.destination
  have h₃ : d.reg (reg S vm i 3) = 1 := vals 3
  have h₅ : d.reg (reg S vm i 5) = (row.frame : Word w) := (vals 5).trans recorded.frame
  have header : if (S i).reverse then ReverseSlices.Linked M (headPC S loc i) (reg S vm i)
        (copyPC S loc i 0) (start S loc ret (i.val + 1))
      else PrivateSlices.Linked M (headPC S loc i) (reg S vm i)
        (copyPC S loc i 0) (start S loc ret (i.val + 1)) := by
    split <;> rename_i h <;> intro j <;>
      simpa only [headPC, instruction, h, Bool.false_eq_true, ite_true, ite_false] using
        code ⟨i, .inr (.inl j)⟩
  have copy : PrivateFields.Linked M .copy (copyPC S loc i) (PrivateSlices.copyRegs (reg S vm i))
      (start S loc ret (i.val + 1)) := fun j ↦ code ⟨i, .inr (.inr j)⟩
  obtain ⟨hlen, offs⟩ := ReverseSlices.oriented_frame_words (S i).reverse m (row.frame : Word w)
    row.frame _ _ row.bits.length rfl recorded.frameFit recorded.length recorded.offsets
  have offsets : 0 < row.bits.length →
      (if (S i).reverse then m ((row.frame : Word w) + 1).val else m (row.frame : Word w).val).val =
        row.sourceOffset ∧ (if (S i).reverse then m (row.frame : Word w).val
        else m ((row.frame : Word w) + 1).val).val = row.targetOffset := by
    cases rev : (S i).reverse <;>
      simpa only [rev, Bool.false_eq_true, ite_false, ite_true] using offs
  obtain ⟨out, stop, persistent, memory, kept, step, work, probes⟩ :=
    ReverseSlices.execute_stored_frame (S i).reverse header copy d startHead h₃ m _ h₅
      row.source row.destination row.sourceOffset row.targetOffset h₀ h₂ row.bits hlen offsets
      (fun h ↦ ⟨by have := fits.old h; have := fits.new; have := fits.room h; omega, fits.room h⟩)
      (fun h ↦ Or.inr (by have := fits.old h; have := fits.new; omega)) (mem ▸ read)
  let fe := PrivateSlices.frameEvents m row.frame row.bits
  have keep (j : Fin r) (h : ∀ u, j ≠ vm i u) : out.reg j = cfg.reg j :=
    (kept j (h _) (h _) (h _) (h _)).trans (unchanged j h)
  refine ⟨ev ++ fe, out, stop, ?_, persistent.trans pers,
    fun j ↦ keep _ (fun u ↦ (safe i u j).symm), keep, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [memory, mem, Row.write]
  · rw [List.length_append, len]
    change setCount S i + fe.length ≤ _
    change fe.length = _ at work
    split at work <;> omega
  · rw [countProbes_append, count]
    change countProbes fe = _ at probes
    apply Nat.add_le_add_left (m := 3)
    split at probes <;> omega
  · rw [PrimedInputRAM.Flow.choiceBits_append, det, List.nil_append]
    unfold fe PrivateSlices.frameEvents
    rw [PrimedInputRAM.Flow.choiceBits_append]
    have hh : choiceBits (PrivateSlices.headerEvents m (row.frame : Word w)) = [] := by
      by_cases hz : m ((row.frame : Word w) + 1 + 1).val = 0 <;>
        simp [PrivateSlices.headerEvents, hz, choiceBits]
    rw [hh, List.nil_append]
    split <;> simp [choiceBits, PrivateFields.events_bits]
  · exact reads_append loads (frame_reads row (S i) allowed pub state m sites recorded.frameFit)
  · exact congrArg (· ++ fe) (RegisterSetup.events_eq f pub state m rs)
  · intro fuel more
    rw [List.length_append, show fuel + (ev.length + fe.length) =
      (fuel + fe.length) + ev.length by omega, run, step]
    simp only [Option.map_map, Function.comp_def, List.append_assoc]
    rfl

/-- Bounds of the generated setup and copy instructions for one visit. -/
def work (S : Fin N → Setup) (row : Fin N → Row) (i : Fin N) :=
  setCount S i + 12 + 5 * (row i).bits.length

/-- Per-row upper bound on external probes, counting all loads in the setup expressions and up
to three reads of the slice header. -/
def probes (S : Fin N → Setup) (i : Fin N) := (∑ j, ((S i).operands j).loads) + 3

/-- The actual private-memory result of a sequence of slice copies. -/
def writes (row : Fin N → Row) (is : List (Fin N)) (mem : Word w → Word w) :=
  is.foldl (fun old i ↦ (row i).write old) mem

/-- Execution contract for a row list. The trace reaches the return counter with the prescribed
private writes, preserves persistent state and registers outside the visited scratch banks,
consumes no choices, and satisfies the summed time and probe bounds. -/
structure Result (S : Fin N → Setup)
    (vm : ∀ i, Fin (RegisterSetup.regCount (S i).operands) ↪ Fin r)
    (M : Machine w p r k) (ret : Fin p) (row : Fin N → Row) (is : List (Fin N))
    (m : Memory w) (cfg out : Config w p r) (events : List (Event w)) : Prop where
  pc : out.pc = ret
  memory : out.privateMem = writes row is cfg.privateMem
  persistent : out.persistent = cfg.persistent
  regs : ∀ j, (∀ i ∈ is, ∀ u, j ≠ vm i u) → out.reg j = cfg.reg j
  ticks : events.length ≤ (is.map (work S row)).sum
  reads : countProbes events ≤ (is.map (probes S)).sum
  choices : choiceBits events = []
  execute : ∀ fuel more, BurstRAM.execute M.program (fuel + events.length) cfg m more =
    (BurstRAM.execute M.program fuel out m more).map (fun rep ↦ ⟨events ++ rep.events, rep.result⟩)

variable (row : Fin N → Row) (m : Memory w) (pub : Fin 5 → Word w) (state : Word w)
variable (recorded : ∀ i, (row i).Recorded (S i) pub state m)
variable (pivot : ℕ) (fits : ∀ i, (row i).Fits w pivot)

variable (allowed : ℕ → Prop)
variable (sites : ∀ i, (row i).ReadSafe (S i) allowed pub state m)

include code safe recorded fits sites in
private theorem scan_list (is : List (Fin N)) (off : ℕ) (endEq : off + is.length = N)
    (order : ∀ j : Fin is.length, is[j.val].val = off + j.val)
    (cfg : Config w p r) (entry : cfg.pc = start S loc ret off)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    (source : ∀ i, (row i).reads cfg.privateMem) :
    ∃ events out, Result S vm M ret row is m cfg out events ∧
      SourceTransport.Reads allowed events ∧ events = trace S row is pub state m := by
  induction is generalizing cfg off with
  | nil =>
    have endAt : off = N := by simpa only [List.length_nil, Nat.add_zero] using endEq
    refine ⟨[], cfg, ?_, by simp [SourceTransport.Reads], rfl⟩
    exact ⟨by simpa [start, endAt] using entry, rfl, rfl, fun _ _ ↦ rfl, le_rfl, le_rfl, rfl,
      by simp⟩
  | cons i is ih =>
    have hi : i.val = off := by simpa using order ⟨0, by simp⟩
    subst off
    have startAt : cfg.pc = setPC S loc i 0 := by
      rw [entry, start, dite_eq_left i.isLt]
    obtain ⟨es, d, pc, mem, keep, args, regs, time, count, det, esReads, esEq, step⟩ :=
      one M loc ret code safe (row i) i cfg m pub state hp hs startAt (recorded i) pivot
        (fits i) (source i) allowed (sites i)
    have next (j : Fin is.length) : is[j.val].val = i.val + 1 + j.val := by
      have h := order ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      change is[j.val].val = i.val + (j.val + 1) at h
      omega
    have safeReads (j : Fin N) : (row j).reads d.privateMem := by
      rw [mem]
      exact reads_write _ _ pivot (fits i) (fits j) cfg.privateMem (source j)
    obtain ⟨tail, out, done, tailReads, tailEq⟩ := ih (i.val + 1)
      (by simp only [List.length_cons] at endEq; omega) next d pc
      (fun j ↦ (args _).trans (hp j)) ((args _).trans hs) safeReads
    refine ⟨es ++ tail, out, ⟨done.pc, ?_, done.persistent.trans keep, ?_, ?_, ?_, ?_, ?_⟩,
      reads_append esReads tailReads, congrArg₂ List.append esEq tailEq⟩
    · rw [done.memory, mem]
      rfl
    · intro j h
      exact (done.regs j (fun v hv ↦ h v (List.mem_cons_of_mem _ hv))).trans
        (regs j (h i List.mem_cons_self))
    · simp only [List.length_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add time done.ticks
    · rw [countProbes_append, List.map_cons, List.sum_cons]
      exact Nat.add_le_add count done.reads
    · rw [PrimedInputRAM.Flow.choiceBits_append, det, done.choices, List.nil_append]
    · intro fuel more
      rw [List.length_append, show fuel + (es.length + tail.length) =
        (fuel + tail.length) + es.length by omega, step, done.execute]
      simp [Option.map_map, Function.comp_def, List.append_assoc]

include code safe recorded fits sites in
/-- Every successful execution of the column realizes the prescribed trace. -/
theorem native_exact (cfg : Config w p r) (entry : cfg.pc = start S loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    (source : ∀ i, (row i).reads cfg.privateMem) :
    let es := trace S row (List.finRange N) pub state m
    ∃ out, Result S vm M ret row (List.finRange N) m cfg out es ∧
      SourceTransport.Reads allowed es := by
  intro es
  obtain ⟨events, out, run, reads, eqv⟩ := scan_list M loc ret code safe row m pub state
    recorded pivot fits allowed sites
    (List.finRange N) 0 (by simp) (fun j ↦ by simp) cfg entry hp hs source
  rw [eqv] at run reads
  exact ⟨out, run, reads⟩

include code safe recorded fits sites in
/-- The finite column code copies every recorded interval in physical row order,
consumes no branch choices and preserves every register outside its scratch bank. -/
theorem native_reads (cfg : Config w p r) (entry : cfg.pc = start S loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    (source : ∀ i, (row i).reads cfg.privateMem) :
    ∃ events out, Result S vm M ret row (List.finRange N) m cfg out events ∧
      SourceTransport.Reads allowed events := by
  obtain ⟨out, run, reads⟩ := native_exact M loc ret code safe row m pub state recorded pivot
    fits allowed sites cfg entry hp hs source
  exact ⟨_, out, run, reads⟩

include code safe recorded fits in
/-- The finite column code copies every recorded interval in physical row order,
consumes no branch choices and preserves every register outside its scratch bank. -/
theorem native (cfg : Config w p r) (entry : cfg.pc = start S loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    (source : ∀ i, (row i).reads cfg.privateMem) :
    ∃ events out, Result S vm M ret row (List.finRange N) m cfg out events := by
  obtain ⟨events, out, result, _⟩ := native_reads M loc ret code safe row m pub state recorded
    pivot fits (fun _ ↦ True) (fun i ↦ readSafe_true _ _ _ _ _) cfg entry hp hs source
  exact ⟨events, out, result⟩

end PairSimulation.ResidentColumn

end VPVNP
end Computability
end OAI
