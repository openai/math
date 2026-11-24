import OAI.Computability.VPVNP.CompressorRecordsOnline
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.CompressorRecordsLevelFields
import OAI.Computability.VPVNP.LiveAuxiliaryHeaders

/-!
# Compiling a finite block of native scans

Each phase contains its worker and exactly the expressions for that worker's
public bank. The phase's position in the program determines the tag written
by its planner. The initial sequence and one complete block determine the
instruction table. The number of repeated blocks enters through the runtime
row count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockPlanner

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe PrimedStackRAM Schedule
open scoped Fin.CommRing

/-- One scheduled scan, pairing its worker with expressions for the initial cursor, exclusive
stopping cursor, and public operands. -/
structure Visit where
  /-- The native pass selected for this scan and the arity of its operand bank. -/
  worker : Schedule.Pass
  /-- Expression giving the state word passed to the worker at the start of the scan. -/
  initial : Expr
  /-- Expression giving the exclusive end cursor at which this worker's scan finishes. -/
  stop : Expr
  /-- An operand expression for each public input of the selected worker. -/
  params : Fin worker.params → Expr

/-- Combine a native pass with the cursor and operand expressions from a phase of matching
arity. -/
def Visit.ofPhase (P : Schedule.Pass) (phase : PhaseRecipe.Phase P.params) : Visit :=
  ⟨P,phase.initial,phase.stop,phase.params⟩

/-- Build a scheduled visit for a straight-line stack-RAM worker, with its result register,
cursor bounds, and public operands. -/
def ops {r k : ℕ} (code : List (PrimedStackRAM.Op r k)) (out : Fin r) (initial stop : Expr)
    (params : Fin k → Expr) : Visit :=
  ⟨⟨_,_,_,PrimedStackRAM.template code out⟩,initial,stop,params⟩

/-- Move a verified scratch column to the next level's published incidence directory. -/
def copy (count source dest : Expr) : Visit :=
  ops LiveAuxiliaryHeaders.copyWord 7 (.lit 0) count ![.lit 0,source,dest]

private def put : List (PrimedStackRAM.Op 4 2) :=
  [.stateWord 0,.publicWord 1 0,.publicWord 2 1,.write 1 2,.constant 3 1,.binary .add 0 0 3]

/-- Publish a single fixed subdivision or header field in the current level. -/
def publish (dest value : Expr) : Visit := ops put 0 (.lit 0) (.lit 1) ![dest,value]

theorem publish_native {w : ℕ} (dest value : Expr) (pub : Fin 2 → Word w) (s : Word w)
    (m : Memory w) :
    let M := ((publish dest value).worker.table.instantiate w pub).program
    let es := [.tick,.tick,.tick,.write (pub 0) (pub 1),.tick,.tick]
    execute M 7 (M.start s) m [] = some ⟨es,some (s+1)⟩ ∧
      after m es = writeMemory m (pub 0) (pub 1) ∧ countProbes es = 1 ∧ choiceBits es = [] := by
  refine ⟨?_,rfl,rfl,rfl⟩
  change execute ((PrimedStackRAM.template put 0).instantiate w pub).program (1+put.length)
    ⟨((PrimedStackRAM.template put 0).instantiate w pub).entry,s,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template,run_eq_trace]
  rfl

/-- The finite visits needed to run the initial scans once and a block of scans repeatedly,
with the level advance per block. -/
structure Script where
  /-- Number of descriptor levels advanced by each complete repetition of the block. -/
  levelsPerBlock : ℕ
  /-- The visits executed once before the first repeated block. -/
  initial : List Visit
  /-- The ordered visits that make up one repetition of the scheduled block. -/
  block : List Visit

namespace Script

variable (A : Script)

/-- Number of visit positions in the initial sequence followed by one block. -/
abbrev size := A.initial.length+A.block.length

/-- Look up a visit in the concatenated indexing of initial phases and block phases. -/
def visit (j : Fin A.size) : Visit :=
  Fin.addCases (fun i ↦ A.initial[i.val]) (fun i ↦ A.block[i.val]) j

/-- The native worker at each of the script's visit positions. -/
def catalog : Schedule.Catalog A.size := fun j ↦ (A.visit j).worker

/-- Each occurrence gets its own finite worker label, even when several
occurrences run the same native table on different operands. -/
def phase (j : Fin A.size) : PhaseRecipe.Phase (Schedule.arity A.catalog) :=
  Phase.ofParams (params_le_arity A.catalog j) j.succ.val (A.visit j).initial (A.visit j).stop
    (A.visit j).params

/-- Compile the visit recipes and block level advance into the online scheduler's
configuration. -/
def plan : Schedule.Online.Config A.catalog A.initial.length A.block.length where
  levelsPerBlock := A.levelsPerBlock
  recipes j := ⟨(A.phase j).registerCount,(A.phase j).recipe⟩

/-- Instantiate the online scheduler for this script on the supplied workspace ports. -/
def program {w : ℕ} (ports : Schedule.Ports w) := Schedule.Online.program A.plan ports

theorem phase_tag (j : Fin A.size) : (A.phase j).tag = j.succ.val := rfl
theorem phase_initial (j : Fin A.size) : (A.phase j).initial = (A.visit j).initial := rfl
theorem phase_stop (j : Fin A.size) : (A.phase j).stop = (A.visit j).stop := rfl

theorem phase_param (j : Fin A.size) (i : Fin (A.visit j).worker.params) :
    (A.phase j).params (i.castLE (params_le_arity A.catalog j)) = (A.visit j).params i := by
  simp only [phase,Phase.ofParams]
  split_ifs with h
  · rfl
  · exact False.elim (h i.isLt)

theorem initial_visit (j : Fin A.initial.length) : A.visit (j.castAdd A.block.length) =
    A.initial[j.val] :=
  Fin.addCases_left ..

theorem block_visit (j : Fin A.block.length) : A.visit (j.natAdd A.initial.length) =
    A.block[j.val] :=
  Fin.addCases_right ..

theorem calendar_total (t : ℕ) : (Schedule.Online.calendar A.plan).total t =
    A.initial.length+t*A.block.length := by
  simp [Schedule.Online.calendar, Schedule.LevelCalendar.recipeCalendar,
    Schedule.LevelCalendar.Calendar.total]

theorem block_phase (t : ℕ) (j : Fin A.block.length) :
    (Schedule.Online.calendar A.plan).phase (A.initial.length+t*A.block.length+j.val) =
      (j.natAdd A.initial.length).val ∧
    (Schedule.Online.calendar A.plan).level (A.initial.length+t*A.block.length+j.val) = t := by
  let K := Schedule.Online.calendar A.plan
  have hb : K.block.length = A.block.length :=
    by simp [K,Schedule.Online.calendar,Schedule.LevelCalendar.recipeCalendar]
  have hi : K.initial.length = A.initial.length :=
    by simp [K,Schedule.Online.calendar,Schedule.LevelCalendar.recipeCalendar]
  simpa only [hb,hi,Fin.val_cast,Fin.val_natAdd] using K.block_phase t (j.cast hb.symm)

end Script

/-- Runtime cursor parameters are produced before the first calendar visit.
They occupy eight persistent scalar cells in the initial level. This bank
survives subsequent launches that overwrite the active frame. -/
def cursor (frame : Expr) : Visit :=
  let src (i : ℕ) := Expr.load (frame.add (.lit i))
  let count := (((src 3).mul (src 4)).mul (src 5)).mul (src 2)
  let col (c : Fin 6) := (src 7).add ((Expr.lit c.val).mul count)
  ⟨Schedule.cursorPass,.lit 0,count,Fin.append (fun j : Fin 5 ↦ src (j.val+2)) col⟩

theorem cursor_parameters {w b l a width start : ℕ} (frame : Expr) (pub : Fin 5 → Word w)
    (state : Word w)
    (m : Memory w) (base : Word w) (he : frame.eval pub state m = base)
    (stored : ∀ j : Fin 6, m (base+((j.val+2 : ℕ) : Word w)).val =
      ![(2^a : Word w),((b+l : ℕ) : Word w),(2^b : Word w),(2^l : Word w),(width : Word w),(start
        : Word w)] j) :
    (cursor frame).stop.eval pub state m = ((CursorRAM.rowCount b l a : ℕ) : Word w) ∧
      (fun j ↦ ((cursor frame).params j).eval pub state m) = CursorRAM.publicWords w b l a width
        start := by
  let src (i : ℕ) := m (base+(i : Word w)).val
  have read (j : Fin 6) : src (j.val+2) =
      ![(2^a : Word w),((b+l : ℕ) : Word w),(2^b : Word w),(2^l : Word w),(width : Word w),(start
        : Word w)] j :=
    stored j
  have n : (src 3 * src 4 * src 5 * src 2) = ((CursorRAM.rowCount b l a : ℕ) : Word w) := by
    rw [show src 3 = _ from read 1,show src 4 = _ from read 2,show src 5 =
      _ from read 3,show src 2 = _ from read 0]
    simp [CursorRAM.rowCount]
  constructor
  · simpa only [cursor,Expr.mul,Expr.eval,Expr.add,BinaryOp.eval,he] using n
  · apply funext
    intro (j : Fin (5+6))
    cases j using Fin.addCases with
    | left i =>
      have hpub : CursorRAM.publicWords w b l a width start (i.castAdd 6) =
          ![(2^a : Word w),((b+l : ℕ) : Word w),(2^b : Word w),(2^l : Word w),(width : Word
            w),(start : Word w)] i.castSucc := by
        fin_cases i <;> simp [CursorRAM.publicWords,CursorRAM.encode]
      simp only [cursor,Fin.append_left,Expr.eval,Expr.add,BinaryOp.eval,he,hpub]
      exact read i.castSucc
    | right c =>
      have hstart : src 7 = (start : Word w) := read 5
      have hpub : CursorRAM.publicWords w b l a width start (c.natAdd 5) =
          (start : Word w)+(c.val : Word w)*((CursorRAM.rowCount b l a : ℕ) : Word w) := by
        fin_cases c <;> simp [CursorRAM.publicWords,CursorRAM.encode]
      simp only [cursor,Fin.append_right,Expr.eval,Expr.add,Expr.mul,BinaryOp.eval,he,hpub]
      change src 7 + (c.val : Word w)*(src 3*src 4*src 5*src 2) = _
      rw [hstart,n]

end CompressorRecords.BlockPlanner

end VPVNP
end Computability
end OAI
