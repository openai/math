import OAI.Computability.VPVNP.LiveProgram
import OAI.Computability.VPVNP.LivePairStageTag
import OAI.Computability.VPVNP.CompressorRecordsOnlineWorkspace
import OAI.Computability.VPVNP.CompressorDescriptorCursorFrame
import OAI.Computability.VPVNP.CompressorHistoryArenaBase

/-!
# The eleven-operand compressed pair instruction table

The group enters at cursor zero with the histogram and auxiliary shadow already
prepared. The pair computes the online calendar size from `n`, publishes the
cursor geometry, derives and saves its actual level stride, and arms the online
calendar. The online program then invokes its planners and workers. On its
accepting exit the final field and vertex evaluator starts at cursor zero.
An accepting exit there returns to the live exponent checker.

The catalog, calendar recipes and final evaluator are finite instruction
tables selected before the input length. All mutable tags, pointers, widths
and entries are recovered or computed at runtime from the actual pair ABI.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule
open scoped Fin.CommRing

/-- Index of one of the ten components in the compressed pair, ordered from calendar
initialization through online compression to terminal evaluation. -/
abbrev Stage := Fin 10

namespace Stage
/-- First stage, which computes the online calendar’s row count from the live input length and
fixed block-count ratio. -/
abbrev calendarRows : Stage := 0
/-- Bootstrap stage that prepares the cursor-parameter inputs in the workspace frame. -/
abbrev cursorFrame : Stage := 1
/-- Load the prepared frame and publish the computed cursor parameters in level zero. -/
abbrev cursorGeometry : Stage := 2
/-- Copy the saved cursor parameters back to the active workspace frame for the stride
calculation. -/
abbrev copyGeometry : Stage := 3
/-- Compute and save the runtime address stride between successive descriptor levels. -/
abbrev stride : Stage := 4
/-- Install the history arena base at the end of the descriptor allocation, together with the
level count and input length. -/
abbrev arenaBase : Stage := 5
/-- Install the scheduler’s six workspace pointers and reset its tag and ordinal. -/
abbrev pointers : Stage := 6
/-- Set the inner scheduler tag to the calendar entry before online compression begins. -/
abbrev calendarStart : Stage := 7
/-- Run the online calendar, planners, and workers that construct the compressed descriptor
history. -/
abbrev online : Stage := 8
/-- Run the final field and vertex evaluator on the compressed history. -/
abbrev terminal : Stage := 9
end Stage

/-- Fixed geometric parameters used by the native descriptor bootstrap.
The ratio is the numerator and denominator of the block-count exponent. -/
structure Bootstrap where
  /-- Fixed dimensions of the descriptor directory, level headers, incidence columns, and slot
  tables. -/
  shape : DescriptorSpace.Shape
  /-- Initial degree exponent used to set up the descriptor cursor parameters. -/
  degreeBits : ℕ
  /-- Number of lane bits per compression block supplied to the initial cursor calculation. -/
  lanesPerBlock : ℕ
  /-- Fixed step count of the block schedule used to compute the descriptor allocation and
  traversal limits. -/
  steps : ℕ
  /-- Numerator of the block-count exponent used by the calendar’s row-count calculation. -/
  numerator : ℕ
  /-- Denominator of the block-count exponent used by the calendar’s row-count calculation. -/
  denominator : ℕ

private def pack {p r : ℕ} (T : Template p r 11) : PairTable := ⟨p,r,T⟩

variable {d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
variable (finalTable : PairTable)

/-- Ten native pair tables in execution order, comprising eight bootstrap stages, the online
scheduler, and the supplied terminal evaluator. -/
def stages : Stage → PairTable :=
  ![pack (CalendarRows.table (OnlineWorkspace.rowsSpec initial phases b.numerator b.denominator)),
    pack (LiveOneShot.oneShot (DescriptorParameters.table b.shape b.degreeBits initial phases b.lanesPerBlock)),
    pack (LiveOneShot.oneShot DescriptorParameters.loader),
    pack (LiveOneShot.oneShot (DescriptorParameters.copyTable b.shape)),
    pack (OnlineWorkspace.strideTable b.shape),
    pack (LiveOneShot.oneShot (HistoryArenaBase.table b.shape initial phases b.steps)),
    pack (Workspace.initTable (arity C)),
    pack (Workspace.calendarStart d),
    pack (OnlineWorkspace.table plan),
    finalTable]

/-- Successor of a completed pair stage in execution order, with no successor after terminal
evaluation. -/
def next (s : Stage) : Option Stage :=
  if h : s.val+1 < 10 then some ⟨s.val+1,h⟩ else none

/-- Maximum register count among the ten native pair tables, used as their common register-bank
size. -/
def regs := Finset.univ.sup fun i => (stages b plan finalTable i).regs

private def includeRegister (R : Stage → ℕ) (i : Stage) : Fin (R i) ↪ Fin (Finset.univ.sup R) :=
  ⟨fun x => x.castLE (Finset.le_sup (Finset.mem_univ i)), fun _ _ e =>
    Fin.ext (congrArg (fun j : Fin (Finset.univ.sup R) => j.val) e)⟩

/-- Include a component’s registers into the common pair register bank at the same register
indices. -/
def embedding (i : Stage) : Fin (stages b plan finalTable i).regs ↪ Fin (regs b plan finalTable) :=
  includeRegister (fun j => (stages b plan finalTable j).regs) i

/-- Widen the selected native pair template to the common register bank while retaining its
eleven public operand indices. -/
def components (i : Stage) : Template (stages b plan finalTable i).pcs (regs b plan finalTable) 11 :=
  LiveStageLink.widen (stages b plan finalTable i).table (embedding b plan finalTable i) id

/-- Single fixed native body, with the same eleven public words as the pair
row in the outer live program. -/
def pairTable : PairTable :=
  pack (PairTag.compile (LiveStageLink.linked (components b plan finalTable) next))

variable {w : ℕ} (pub : Fin 11 → Word w)

/-- Burst RAM program obtained by instantiating the linked compressed-pair table with the
supplied word width and eleven public words. -/
abbrev program := ((pairTable b plan finalTable).table.instantiate w pub).program
/-- Burst RAM program of the selected native component before register widening and stage
linking. -/
abbrev original (i : Stage) := ((stages b plan finalTable i).table.instantiate w pub).program

/-- Wrap a native component report with five ticks to calculate the pair tag address, the tag
dispatch, and any transfer to the next component. -/
def report (i : Stage) (rep : Report w) := LiveStageLink.prependLog (List.replicate 5 .tick)
  (LiveStageLink.linkedReport next (PairTag.address pub) i rep)

/-- The outer pair linker uses the otherwise unused tail-state word. The
physical auxiliary shadow, and even its final site, are independent of this tag. -/
theorem tag_address (c : Constants) (g : Geometry) (lit : LiteralPrefix) :
    PairTag.address (Pieces.word g lit ∘ StageOperands.pair c) = Pieces.word g lit (.geometry (Layout.oldState c)) := by
  change ((Fin.ofNat (2^g.w) ((Layout.counter c).eval g) : Word g.w) +
    Fin.ofNat (2^g.w) (c.grammarLabels.eval g)) + Fin.ofNat (2^g.w) c.motifLabels =
    Fin.ofNat (2^g.w) (((Layout.counter c).eval g) + (c.grammarLabels.eval g+c.motifLabels))
  change (((Layout.counter c).eval g : ℕ) : Word g.w) + ((c.grammarLabels.eval g : ℕ) : Word g.w) + (c.motifLabels : Word g.w) =
    (((Layout.counter c).eval g + (c.grammarLabels.eval g + c.motifLabels) : ℕ) : Word g.w)
  simp [add_assoc]

/-- Five ticks to compute the tag address, followed by the native stage
scan, source execution and, when applicable, a single tag transfer write. -/
theorem execute_stage (i : Stage) (fit : 10 ≤ 2^w) (f cap : ℕ) (room : f+30 ≤ cap)
    (st : Word w) (m : Memory w) (tag : m (PairTag.address pub).val = LiveStageLink.tagWord w i)
    (bs : List Bool) (rep : Report w) (source : execute (original b plan finalTable pub i) f
      ((original b plan finalTable pub i).start st) m bs = some rep) :
    execute (program b plan finalTable pub) cap ((program b plan finalTable pub).start st) m bs = some (report pub i rep) := by
  let T := components b plan finalTable
  let L := LiveStageLink.linked T next
  have comp : execute ((T i).instantiate w pub).program f (((T i).instantiate w pub).program.start st) m bs = some rep :=
    (LiveStageLink.execute_widen_start (stages b plan finalTable i).table (embedding b plan finalTable i) id pub f st m bs).trans source
  have run := LiveStageLink.execute_linked_of_stage T next pub (PairTag.address pub) i fit (by omega : f+2*10+5 ≤ cap-5) st m tag bs rep comp
  have outer := PairTag.execute_start L pub (cap-5) st m bs
  change execute (program b plan finalTable pub) (cap-5+5) ((program b plan finalTable pub).start st) m bs =
    (execute (LiveStageLink.machine T next pub (PairTag.address pub)).program (cap-5)
      ((LiveStageLink.machine T next pub (PairTag.address pub)).program.start st) m bs).map _ at outer
  rw [show cap-5+5 = cap by omega,run] at outer
  exact outer

/-- Accounting of every deterministic pair-level link action. -/
theorem report_effect (i : Stage) (rep : Report w) (m : Memory w) :
    choiceBits (report pub i rep).events = choiceBits rep.events ∧
    (report pub i rep).probes = rep.probes + 1 + (if rep.result = none ∧ (next i).isSome then 1 else 0) ∧
    (report pub i rep).events.length ≤ rep.events.length + 30 ∧
    after m (report pub i rep).events = match rep.result, next i with
      | none, some j => writeMemory (after m rep.events) (PairTag.address pub) (LiveStageLink.tagWord w j)
      | _, _ => after m rep.events := by
  have a := LiveStageLink.linkedReport_choiceBits next (PairTag.address pub) i rep
  have b := LiveStageLink.linkedReport_probes next (PairTag.address pub) i rep
  have l := LiveStageLink.linkedReport_length_le next (PairTag.address pub) i rep
  have e := LiveStageLink.linkedReport_after next (PairTag.address pub) i rep m
  refine ⟨a,b,?_,?_⟩
  · simp only [report,LiveStageLink.prependLog,List.length_append,List.length_replicate]
    omega
  · change after m (List.replicate 5 .tick ++ _) = _
    rw [after,List.foldl_append,show (List.replicate 5 .tick).foldl update m = m by rfl]
    cases hs : rep.result <;> cases hn : next i <;> simpa only [hs,hn,after] using e

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
