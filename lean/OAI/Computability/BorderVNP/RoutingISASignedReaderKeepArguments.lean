import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepFragments

/-! # Every true argument-building stage of the signed machine preserves the residue reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ReaderKept

open VPVNP.BurstRAM TeamContraction.ProcessorSlots DiagonalTallyCellReports
open CellPacket.Supplement.Batch

/-- From the report return to the end of all private calls. The intermediate
states are the native fragment and bucket output, compact task publication,
supplemental patch, sparse exterior encoding and typed serialization. -/
theorem afterArguments {w : ℕ} (A : StartupArena) (entries pins : ℕ)
    {boot pinMem before emitted bucketed tasksAt encoded : Memory w}
    (old : ReaderKept A entries pins boot pinMem before)
    (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (frags : FragmentRows.Layout) (b : FragmentBucket.Layout) {tag : Fin b.rows → Fin b.cells}
    {payload : Fin b.rows → Fin 3 → ℕ} {afterEmit afterBucket : Bank w}
    (emit : readings emitted=frags.image (readings before))
    (bucket : FragmentBucket.Result b tag payload (.ofWords afterEmit emitted) (.ofWords afterBucket bucketed))
    (placedFragments : A.next ≤ frags.control ∧ A.next ≤ frags.quads ∧ A.next ≤ b.pairs ∧
      A.next ≤ b.triples ∧ A.next ≤ b.cursors)
    {Site : Type} (rows : CellControlRows.Layout) (p : ℕ → CellPacket.Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (fit : rows.toLayout.Room (readings bucketed) w)
    (taskImage : readings tasksAt=rows.toLayout.published (readings bucketed))
    (span : ∀ c < rows.cells, readings bucketed (rows.sorted+rows.padded+(rows.stops+c))-
      readings bucketed (rows.sorted+rows.padded+c)-1=3*((p c).parts.length+3))
    (frame : rows.frame=A.frame)
    (placedTasks : A.next ≤ rows.calls ∧ A.next ≤ rows.tasks ∧ A.next ≤ rows.sorted ∧ A.next ≤ rows.merged)
    (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned)
    (placedExterior : A.next ≤ l.compact ∧ A.next ≤ l.tasks ∧ A.next ≤ l.counts)
    (typed : ℕ → TypedBatch.Task) (arena : rows.toLayout.Arenas (readings bucketed) w typed)
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} :
    let expanded := produced rows (readings bucketed) p geom extra
    let count := rows.before (readings bucketed) rows.cells
    let patched := written tasksAt (fun i => (expanded i).cell) count
    readings encoded=SparseExterior.written l owned (readings patched) l.count →
      ∀ {s es t final}, Runs pub mac callOwnedCells s (TypedBatch.written encoded typed count) es t final →
        ReaderKept A entries pins boot pinMem final := by
  intro expanded count patched sparse s es t final calls
  have bucketKeep := afterFragments frags b emit bucket old packet index placedFragments
  have supKeep := afterSupplement rows bucketed tasksAt p geom extra fit taskImage span bucketKeep frame packet index placedTasks
  have exteriorKeep := afterSparse l owned sparse supKeep packet index placedExterior
  exact afterTypedCalls rows.toLayout (readings bucketed) arena calls exteriorKeep packet index placedTasks.1

end RoutingISA.ReaderKept

end BorderVNP
end Computability
end OAI
