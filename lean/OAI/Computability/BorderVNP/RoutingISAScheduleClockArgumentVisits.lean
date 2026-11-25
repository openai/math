import OAI.Computability.BorderVNP.RoutingISAScheduleClockSparseCalls
import OAI.Computability.BorderVNP.RoutingISAScheduleClockSparse
import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

/-! # Chronological clock of the arguments stage after report emission

The sparse public directory, owned task producer, and three consecutive
argument writers run on successive physical memories. Their combined
charge also includes the word lengths published for the following private
calls, whether or not those calls eventually succeed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CellSparse CompactMachine
open private bounded_cost from OAI.Computability.BorderVNP.RoutingISAScheduleClockRuns

variable {w : ℕ}

/-- The two consecutive public array layouts read by the fragment emitter
and stable bucket after the reports have been placed. -/
structure FragmentDirectoryInput (pub : Arg → Word w) (m : Memory w) where
  /-- The three input scans and their common output bank. -/
  layout : FragmentRows.Layout
  /-- The stable per-cell bucketing arrays. -/
  bucket : FragmentBucket.Layout
  /-- Address of the indirect scalar control table. -/
  control : ℕ
  /-- Actual frame words consumed by the emitter. -/
  loaded : layout=FragmentRows.Layout.fromFrame (readings pub 0) (readings m)
  /-- All source intervals and quadruple destinations fit. -/
  fit : layout.Fits w (readings m)
  /-- The stable sort reads the emitter's output base. -/
  base : bucket.quads=layout.quads
  /-- Its row count is precisely the number of emitted quadruples. -/
  rows : bucket.rows=(layout.stream (readings m)).length
  /-- Both programs use the same number of cell bins. -/
  cells : bucket.cells=layout.cells
  /-- The occupied sort inputs and output bins are disjoint. -/
  room : bucket.Fits w
  /-- The stable sort's inputs are loaded from the post-emission memory. -/
  header : bucket.Header (readings pub 0) control (layout.image (readings m))
  /-- The frame operand for the indirect control address fits. -/
  frame : readings pub 0+92 < 2^w
  /-- Every scalar input to the bucket pass fits. -/
  controlRoom : control+33 < 2^w

/-- Source rows and physical reservations for the supplemental, exterior
and typed passes. The compressed word memory is their intermediate native
image, before the last initializer. -/
structure SparseCallInput (pub : Arg → Word w) (m : Memory w) where
  /-- Seven-word task table. -/
  table : ℕ
  /-- Four-word supplemental controls. -/
  controls : ℕ
  /-- Number of tasks owned by this processor. -/
  count : ℕ
  /-- Input length determining the private burst cap. -/
  n : ℕ
  /-- The supplemental section of each compact row. -/
  merge : ℕ → CellPacket.Supplement.Batch.Cell
  /-- Addressable root frame and indirect supplemental pointer. -/
  frame : (pub 0).val+92 < 2^w
  /-- Indirect control row pointer fits. -/
  pointer : readings m ((pub 0).val+92)+11 < 2^w
  /-- The compact task count comes from the published owner scan. -/
  length : readings m ((pub 0).val+90)=count
  /-- The root frame addresses the original task table. -/
  base : readings m ((pub 0).val+89)=table
  /-- The indirect control table addresses the supplemental rows. -/
  indirect : readings m (readings m ((pub 0).val+92)+11)=controls
  /-- Seven words per owned task. -/
  taskRoom : table+7*count ≤ 2^w
  /-- Four control words per owned task. -/
  controlRoom : controls+4*count ≤ 2^w
  /-- The initial supplemental descriptor, sidecar counts and live sources. -/
  source : ∀ i < count, CellPacket.Supplement.Batch.Stored (merge i) table controls i m ∧
    CellPacket.Supplement.Batch.Room (merge i) w
  /-- Earlier supplemental writes preserve every later supplemental source. -/
  apart : ∀ i < count, ∀ j < i, ∀ a ∈ (merge i).sources table controls i, (merge j).Outside a
  /-- Address and length of the occupied sparse tables. -/
  layout : SparseExterior.Layout
  /-- Actual occupied spans and report tails. -/
  owned : ℕ → SparseExterior.Owned
  /-- The sparse writer shares the processor's root frame. -/
  root : (pub 0).val=layout.frame
  /-- Its last indirect scalar operand fits. -/
  header : layout.control+36 < 2^w
  /-- The real task and bucket pointers survive the preceding descriptor pass. -/
  loaded : layout.Loaded (readings (CellPacket.Supplement.Batch.written m merge count))
  /-- The addressed live bits, report tail and destinations satisfy the sparse writer. -/
  initial : ∀ i < layout.count, (owned i).Initial layout i (CellPacket.Supplement.Batch.written m merge count)
  /-- Earlier sparse writes preserve every later sparse source. -/
  independent : ∀ i < layout.count, ∀ j < i, ∀ a, (owned i).Source layout i a → (owned j).Outside layout j a
  /-- Real word memory after writing the encoded exterior and updating the pointers. -/
  compressed : Memory w
  /-- Exact native postimage of the two preceding passes. -/
  image : readings compressed=SparseExterior.written layout owned (readings (CellPacket.Supplement.Batch.written m merge count))
    layout.count
  /-- Typed task contents in the resulting physical memory. -/
  tasks : ℕ → TypedBatch.Task
  /-- Compact physical arguments named by the published call directory. -/
  cells : ℕ → CellInput
  /-- The final initializer reads these compacted sources and publishes their bursts. -/
  typed : TypedDirectoryInput pub compressed table count n tasks cells

private abbrev fragmentProgram : Code := .seq FragmentRows.program FragmentBucket.program
private abbrev sparseProgram : Code := .block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]

/-- The three successive native returns that comprise the actual arguments stage. -/
abbrev ArgumentVisits (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :=
  Σ first : Returns fragmentProgram pub mac s m,
  Σ second : Returns TypedTaskBuilder.program pub mac first.val.2.1 first.val.2.2,
    Returns sparseProgram pub mac second.val.2.1 second.val.2.2

/-- Every actual return splits at the emitter/bucket and typed task producer boundaries. -/
noncomputable def argumentVisitsEquiv (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :
    ArgumentVisits pub mac s m ≃ Returns SignedPrep.arguments pub mac s m := by
  let a := [FragmentRows.program,FragmentBucket.program]
  let b := [TypedTaskBuilder.program,CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]
  exact (Equiv.sigmaCongrRight fun f : Returns fragmentProgram pub mac s m =>
    seqReturnEquiv TypedTaskBuilder.program sparseProgram pub mac f.val.2.1 f.val.2.2).trans
    ((seqReturnEquiv (.block a) (.block b) pub mac s m).trans
      (Equiv.subtypeEquivRight fun _ => (Runs.block_append_iff (a:=a) (b:=b) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)).symm))

/-- Concatenation of the native events and the actual final bank and memory. -/
theorem argumentVisitsEquiv_val (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (v : ArgumentVisits pub mac s m) : (argumentVisitsEquiv pub mac s m v).val=
      (v.1.val.1++(v.2.1.val.1++v.2.2.val.1),v.2.2.val.2) := rfl

/-- The complete native argument return fits its three real loop allowances
and already pays for the private probes in its resulting call directory. -/
theorem arguments_source_charge {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m}
    (x : Returns SignedPrep.arguments pub mac s m) (fr : FragmentDirectoryInput pub m) :
    let parts := (argumentVisitsEquiv pub mac s m).symm x
    ∀ (b : TypedTaskBuilder.Layout), (pub 0).val=b.frame → b.Fields (readings parts.1.val.2.2) →
      b.Room (readings parts.1.val.2.2) w → ∀ src : SparseCallInput pub parts.2.1.val.2.2,
      traceCost x.val.1+privateDirectoryTicks pub x.val.2.2 ≤ fragmentDirectoryTicks fr.layout (readings m)+
        (TypedTaskBuilder.setup.slots+b.cells*(TypedTaskBuilder.body.slots+1)+2)+
        sparseCallTicks src.layout src.owned src.tasks (Frame.ofMemory pub src.compressed) x.val.2.2 src.count := by
  intro parts b fp fields room src
  have fragment := fragmentDirectory_return (fragmentDirectory_run pub mac s m fr.layout fr.bucket fr.control fr.loaded fr.fit
    fr.base fr.rows fr.cells fr.room fr.header fr.frame fr.controlRoom) parts.1.property
  have builder := bounded_cost parts.2.1.property (by decide) (TypedTaskBuilder.program_run pub mac parts.1.val.2.1
    parts.1.val.2.2 b fp fields room)
  have tail := sparse_preparedDirectory_charge src.merge src.frame src.pointer src.length src.base src.indirect src.taskRoom
    src.controlRoom src.source src.apart src.layout src.owned src.tasks src.cells src.root src.header src.loaded src.initial
    src.independent src.compressed src.image src.typed parts.2.2.property
  have same := argumentVisitsEquiv_val pub mac s m parts
  rw [show argumentVisitsEquiv pub mac s m parts=x from Equiv.apply_symm_apply ..] at same
  rw [same]
  simp only [Transmission.cost_append]
  omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
