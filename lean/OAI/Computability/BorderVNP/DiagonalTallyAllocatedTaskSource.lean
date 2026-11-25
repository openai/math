import OAI.Computability.BorderVNP.DiagonalTallyPrivateCallSource
import OAI.Computability.BorderVNP.CellPacketSupplementalProducerRows
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # Persistent report operands through the actual signed-task allocation and calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports DiagonalTallyMaterialize
open CellPacket.Supplement.Batch TypedTaskBuilder

/-- The actual zero and one literal addresses are the first two words after the last
host bank. Both precede every pre-task header, counter and supplement. -/
theorem Layout.literal_bounds (a : Layout) :
    a.cube.cellBank+a.cube.cells*a.cube.cellStride=a.cube.stop ∧ a.cube.stop+1<a.before.start := by
  refine ⟨rfl,?_⟩
  apply lt_of_lt_of_le _ a.constants_le_before
  simp only [CubeConstants.arenaEnd,CubeConstants.idBase]
  omega

/-- The three-word global calls and seven-word compact tasks begin above the merged
counters. The last burst window ends exactly at the post-task partition. -/
theorem Layout.task_bounds (a : Layout) (team frame offsets control : ℕ) :
    let task := a.tasks team frame offsets control
    a.before.merged ≤ task.calls ∧ a.before.merged ≤ task.tasks ∧
      task.bursts+task.burstStride*task.cells=a.after.start ∧ task.frame=frame := by
  have e : a.before.merged ≤ a.before.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four]; omega
  exact ⟨e,e.trans (Nat.le_add_right ..),rfl,rfl⟩

/-- The native producer's exclusive descriptor endpoint is the actual sorted stop
marker. Its four reserved triples start exactly twelve words earlier, and the
merged-count output is indexed by the same global cell as the true task row. -/
theorem produced_addresses {Site : Type} {w : ℕ} (rows : CellControlRows.Layout)
    (mem : ℕ → ℕ) (p : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (room : rows.toLayout.Room mem w) {i : ℕ} (hi : i < rows.before mem rows.cells)
    (span : ∀ c < rows.cells, mem (rows.sorted+rows.padded+(rows.stops+c))-mem (rows.sorted+rows.padded+c)-1 =
      3*((p c).parts.length+3)) :
    let c := globalCell rows.toLayout mem i
    let o := produced rows mem p geom extra i
    o.layout.merged=rows.merged+c ∧ o.layout.tail+12=rows.sorted+mem (rows.sorted+rows.padded+(rows.stops+c)) ∧
      o.layout.tail+12 < rows.sorted+rows.padded ∧ rows.sorted ≤ o.layout.tail := by
  intro c o
  have cn : c < rows.cells := (global_spec rows.toLayout mem hi).1
  have len := span c cn
  have atLeast : 1 ≤ (p c).parts.length := by simp [CellPacket.Placed.parts,CellSparse.Packet.Source.plan]
  have rank := (room.ranks c cn).2
  change mem (rows.sorted+rows.padded+(rows.stops+c)) < rows.padded at rank
  change rows.merged+c=rows.merged+c ∧
    rows.sorted+mem (rows.sorted+rows.padded+(rows.stops+c))-12+12=_ ∧
    rows.sorted+mem (rows.sorted+rows.padded+(rows.stops+c))-12+12<_ ∧
    rows.sorted ≤ rows.sorted+mem (rows.sorted+rows.padded+(rows.stops+c))-12
  omega

/-- The concrete producer's merged-count word and all twelve patched descriptor
words are outside the persistent cell operands. Frame 14 and 15 also survive both
prepasses, so the subsequent signed call run uses its real, bounded global directory. -/
theorem Layout.supplied_after_calls {w : ℕ} {Site : Type} (a : Layout) (team frame offsets control : ℕ)
    (banks : CellBanks.Layout) (rows : CellControlRows.Layout) (l : ReportLayout) (cs : List (ReportCell l)) (q : ReportCursor)
    (alloc : ReportAllocation a.before a.after banks l cs q) (taskLayout : rows.toLayout=a.tasks team frame offsets control)
    (reportFrame : l.frame=frame) (reportZero : l.zeroAddr=a.cube.stop)
    (bankStart : banks.bankStart=a.cube.cellBank) (bankCount : banks.cells=a.cube.cells)
    (bankStride : banks.stride=a.cube.cellStride) (merged : rows.merged=a.before.merged)
    (sortedLo : rows.frame+16 ≤ rows.sorted) (sortedHi : rows.sorted+rows.padded ≤ banks.bankStart)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (fp : (pub 0).val=rows.frame)
    (m m₁ : Memory w) (p : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (room : rows.toLayout.Room (readings m) w) (fields : rows.toLayout.Fields (readings m))
    (published : readings m₁=rows.toLayout.published (readings m))
    (span : ∀ c < rows.cells, readings m (rows.sorted+rows.padded+(rows.stops+c))-readings m (rows.sorted+rows.padded+c)-1 =
      3*((p c).parts.length+3))
    (old : supplied m (cellEnd cs q) q.descriptors (cellOperands cs q)) :
    let owned := produced rows (readings m) p geom extra
    let count := rows.before (readings m) rows.cells
    let patched := written m₁ (fun i => (owned i).cell) count
    let mt := TypedBatch.written patched (fun i => (owned i).typed) count
    rows.toLayout.Arenas (readings m) w (fun i => (owned i).typed) →
      ∀ {s es t mf}, Runs pub mac callOwnedCells s mt es t mf →
        supplied mf (cellEnd cs q) q.descriptors (cellOperands cs q) := by
  intro owned count patched mt ar s es t mf run
  have bounds := a.task_bounds team frame offsets control
  rw [←taskLayout] at bounds
  have frameEq : rows.frame=l.frame := bounds.2.2.2.trans reportFrame.symm
  have cellEq : rows.cells=a.cube.cells := by
    rw [taskLayout]
    rfl
  have below := a.literal_bounds
  have oldLo : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr := by
    rw [reportZero,bankStart,bankCount,bankStride,below.1]
  have oldHi : l.zeroAddr<a.before.start := by rw [reportZero]; omega
  have head := alloc.frameBefore
  have bank := alloc.bankBefore
  have lower : a.before.start ≤ a.before.merged := by
    simp only [BeforeTasks.merged,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]; omega
  have mergedEnd : a.before.merged+a.before.bound.cells ≤ a.before.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four]; omega
  have post := alloc.preBefore
  have bankCells := alloc.bankCells
  have addresses (i : ℕ) (hi : i < count) := produced_addresses rows (readings m) p geom extra room hi span
  have fix (j : ℕ) (hj : j<16) : mt ((pub 0).val+j)=m₁ ((pub 0).val+j) := by
    let z := (pub 0).val+j
    have limit : z<rows.calls := by have h := room.outputs.1; change rows.frame+112 ≤ rows.calls at h; dsimp [z]; omega
    have scr : z<rows.scratch := by have h := ar.calls; change rows.calls+3*rows.cells ≤ rows.scratch at h; omega
    have hp : patched z=m₁ z := preserve m₁ _ (i:=0) (Nat.zero_le count) z (fun k _ hk => by
      obtain ⟨mrg,_,_,tail⟩ := addresses k hk
      change z≠(owned k).layout.merged ∧ (z<(owned k).layout.tail ∨ (owned k).layout.tail+12 ≤ z)
      change (owned k).layout.merged=rows.merged+_ at mrg
      change rows.sorted ≤ (owned k).layout.tail at tail
      rw [merged] at mrg
      dsimp only [z]
      omega)
    have ht : mt z=patched z := TypedBatch.preserve patched _ (i:=0) (Nat.zero_le count) z
      (fun k _ hk => TypedTaskBuilder.below rows.toLayout (readings m) ar hk scr (.inl limit))
    exact ht.trans hp
  have frameAfter : CellDispatch.Frame.ofMemory pub mt=CellDispatch.Frame.ofMemory pub m₁ := by
    simp only [CellDispatch.Frame.ofMemory,show mt (pub 0).val=m₁ (pub 0).val from fix 0 (by decide),
      fix 14 (by decide),fix 15 (by decide)]
  have actual := dispatch_frame rows.toLayout (readings m) pub m₁ fp fields room published
  have fr := room.frame
  have callRoom := room.calls
  refine alloc.supplied_after_calls pub mac m m₁ rows.toLayout owned oldLo oldHi old published ar
    bounds.1 bounds.2.1 bounds.2.2.1.le frameEq ?_ (by rw [fp]; omega) ?_ run
  · intro i hi
    obtain ⟨eqn,_,cap,_⟩ := addresses i hi
    have hc := (global_spec rows.toLayout (readings m) hi).1
    change globalCell rows.toLayout (readings m) i < rows.cells at hc
    change (owned i).layout.merged=rows.merged+globalCell rows.toLayout (readings m) i at eqn
    rw [merged] at eqn
    exact ⟨by omega,by omega,cap.le.trans sortedHi⟩
  · change (CellDispatch.Frame.ofMemory pub mt).base+3*(CellDispatch.Frame.ofMemory pub mt).count ≤ 2^w
    rw [frameAfter,actual]
    exact callRoom.le

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
