import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoom
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepArguments

/-! # Retaining the parsed subtotal array through real cell argument preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots
open BorderVNP.Cube
open DiagonalTallyCellReports DiagonalTallyAllocation FiniteEvaluator CellPacket.Supplement.Batch

variable {w reserve axes groups cap width : ℕ} (l : Layout) (A : StartupArena)
variable (p : PositiveFields reserve axes groups cap l.cube.teams l.dim width)
variable (pub : Arg → Word w) (team : ℕ) (frame : (pub 0).val=A.frame)
variable (size : A.header=PositiveFields.width reserve axes groups cap l.cube.teams l.dim width)
local notation "raw" => rawAddress A reserve axes groups cap
local notation "seed" => HeaderSeed l p pub raw team

include frame size

/-- The four physical open stages retain the parsed tally from the output of the
owned vertex scan. Their only earlier write is the count of the compact cell list. -/
theorem HeaderSeed.afterControls (H : OpenSuffix.Inputs) {mac : TeamOpcode.Macros w 8} {r m es t mt}
    (old : seed m) (ready : OpenSuffix.Ready H (pub 0).val (readings m) w)
    (run : Runs pub mac OpenSuffix.code r m es t mt)
    (host : let h := HostScatter.Layout.fromFrame (pub 0).val (readings m)
      ∀ i < h.count,∀ side,h.Owned (readings m) i side → A.next ≤ h.dest (readings m) i side)
    (tables : OpenSuffix.AfterDeck H A.next) : seed mt := by
  apply old.transfer
  intro x hx
  obtain ⟨lower,_,next⟩ := rawAddress_room l A size
  rw [frame] at hx
  exact ReaderKept.afterControls_word H ready run A.next x ((seedRead_before_pins l A size hx).trans_le next)
    (frame ▸ headerSeedRead_other hx lower (j:=90) (by decide) (by decide)) host tables

/-- Realized dynamic cell reports retain the common subtotal words and boot
addresses while they publish the new sparse descriptor count. -/
theorem HeaderSeed.afterReports {banks : CellBanks.Layout} {layout : ReportLayout} {cs : List (ReportCell layout)}
    {q : ReportCursor} {m mt : Memory w} (old : seed m) (alloc : ReportAllocation l.before l.after banks layout cs q)
    (image : readings mt=applyWrites (readings m) (prepareWrites cs q)) (head : layout.frame=A.frame)
    (placed : A.next ≤ banks.bankStart) : seed mt := by
  apply old.transfer
  intro x hx
  obtain ⟨lower,_,next⟩ := rawAddress_room l A size
  rw [frame] at hx
  exact ReaderKept.afterReports_word alloc image x ((seedRead_before_pins l A size hx).trans_le (next.trans placed))
    (head ▸ headerSeedRead_other hx lower (j:=35) (by decide) (by decide))

/-- The complete executed argument preparation and private calls retain the
signed boot words and the originally transmitted claim. No report address is
inferred from the sparse exterior subsequently passed to the private cell. -/
theorem HeaderSeed.afterArguments {before emitted bucketed tasksAt encoded : Memory w} (old : seed before)
    (frags : FragmentRows.Layout) (b : FragmentBucket.Layout) {tag : Fin b.rows → Fin b.cells}
    {payload : Fin b.rows → Fin 3 → ℕ} {afterEmit afterBucket : Bank w}
    (emit : readings emitted=frags.image (readings before))
    (bucket : FragmentBucket.Result b tag payload (.ofWords afterEmit emitted) (.ofWords afterBucket bucketed))
    (fragments : A.next ≤ frags.control ∧ A.next ≤ frags.quads ∧ A.next ≤ b.pairs ∧ A.next ≤ b.triples ∧ A.next ≤ b.cursors)
    {Site : Type} (rows : CellControlRows.Layout) (packet : ℕ → CellPacket.Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (room : rows.toLayout.Room (readings bucketed) w)
    (taskImage : readings tasksAt=rows.toLayout.published (readings bucketed))
    (span : ∀ c < rows.cells, readings bucketed (rows.sorted+rows.padded+(rows.stops+c))-
      readings bucketed (rows.sorted+rows.padded+c)-1=3*((packet c).parts.length+3))
    (head : rows.frame=A.frame)
    (tasks : A.next ≤ rows.calls ∧ A.next ≤ rows.tasks ∧ A.next ≤ rows.sorted ∧ A.next ≤ rows.merged)
    (ext : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned)
    (exterior : A.next ≤ ext.compact ∧ A.next ≤ ext.tasks ∧ A.next ≤ ext.counts)
    (typed : ℕ → TypedBatch.Task) (ar : rows.toLayout.Arenas (readings bucketed) w typed)
    {mac : TeamOpcode.Macros w 8} :
    let expanded := produced rows (readings bucketed) packet geom extra
    let count := rows.before (readings bucketed) rows.cells
    let patched := written tasksAt (fun i => (expanded i).cell) count
    readings encoded=SparseExterior.written ext owned (readings patched) ext.count →
      ∀ {s es t final}, Runs pub mac callOwnedCells s (TypedBatch.written encoded typed count) es t final →
        seed final := by
  intro expanded count patched compact s es t final calls
  apply old.transfer
  intro x hx
  rw [frame] at hx
  obtain ⟨lower,_,next⟩ := rawAddress_room l A size
  have low := (seedRead_before_pins l A size hx).trans_le next
  have apart := headerSeedRead_other hx lower (j:=90) (by decide) (by decide)
  exact (ReaderKept.afterTypedCalls_word rows.toLayout (readings bucketed) ar calls x (low.trans_le tasks.1)).trans
    ((ReaderKept.afterSparse_word ext owned compact A.next x low exterior).trans
      ((ReaderKept.afterSupplement_word rows bucketed tasksAt packet geom extra room taskImage span A.next x low
        (head ▸ apart) tasks).trans (ReaderKept.afterFragments_word frags b emit bucket A.next x low fragments)))

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
