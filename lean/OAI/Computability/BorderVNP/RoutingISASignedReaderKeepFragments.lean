import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepPackets
import OAI.Computability.BorderVNP.FragmentRowsBucketProgram

/-! # Reader operands through the emitted fragments and stable cell buckets -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ReaderKept

open VPVNP.BurstRAM TeamContraction.ProcessorSlots DiagonalTallyAllocation

/-- Both the live-fragment writer and the stable cell bucketer retain every physical word below their output arrays. -/
theorem afterFragments_word {w : ℕ} {before middle after : Memory w}
    (l : FragmentRows.Layout) (b : FragmentBucket.Layout) {tag : Fin b.rows → Fin b.cells}
    {p : Fin b.rows → Fin 3 → ℕ} {s t : Bank w}
    (first : readings middle=l.image (readings before))
    (second : FragmentBucket.Result b tag p (.ofWords s middle) (.ofWords t after))
    (floor x : ℕ) (low : x<floor)
    (reserved : floor ≤ l.control ∧ floor ≤ l.quads ∧ floor ≤ b.pairs ∧ floor ≤ b.triples ∧ floor ≤ b.cursors) :
    after x=before x := by
  apply Fin.ext
  change readings after x=readings before x
  have across : readings after x=readings middle x := second.other x (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
  rw [across,first,FragmentRows.Layout.image,Function.update_of_ne (by omega : x≠l.control+29),
    Packing.BottomReports.Writer.write_outside _ _ _ _ (.inl (by omega))]

/-- The real fragment emitter updates only quadruples and control-directory slot 29.
The following stable bucketer writes only its three reserved arrays. -/
theorem afterFragments {w : ℕ} {A : StartupArena} {entries pins : ℕ} {boot pinMem before middle after : Memory w}
    (l : FragmentRows.Layout) (b : FragmentBucket.Layout) {tag : Fin b.rows → Fin b.cells}
    {p : Fin b.rows → Fin 3 → ℕ} {s t : Bank w}
    (first : readings middle=l.image (readings before))
    (second : FragmentBucket.Result b tag p (.ofWords s middle) (.ofWords t after))
    (old : ReaderKept A entries pins boot pinMem before)
    (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (reserved : A.next ≤ l.control ∧ A.next ≤ l.quads ∧ A.next ≤ b.pairs ∧ A.next ≤ b.triples ∧ A.next ≤ b.cursors) :
    ReaderKept A entries pins boot pinMem after := by
  apply old.advance
  intro x hx
  exact afterFragments_word l b first second A.next x (hx.below packet index) reserved

end RoutingISA.ReaderKept

namespace RoutingISA.SignedTaskArena

open TeamContraction.ProcessorSlots DiagonalTallyAllocation

/-- Scalar lower bounds of all later actual write regions, derived from the
single geometry placement above the physical pin arrays. The indirect geometry
controls and the sorted descriptor table have their own addressed placements. -/
theorem Layout.reader_bounds (a : Layout) (A : StartupArena) (team frame offsets control : ℕ)
    (placement : A.next ≤ a.cube.header.header) :
    let t := a.tasks team frame offsets control
    A.next ≤ a.cube.cellBank ∧ A.next ≤ a.cube.stop ∧ A.next ≤ a.fragments.quads ∧
    A.next ≤ a.fragments.pairs ∧ A.next ≤ a.fragments.triples ∧ A.next ≤ a.fragments.cursors ∧
    A.next ≤ a.fragments.external ∧ A.next ≤ a.fragments.counts ∧ A.next ≤ a.before.start ∧
    A.next ≤ a.before.merged ∧ A.next ≤ t.calls ∧ A.next ≤ t.tasks ∧ A.next ≤ a.after.start := by
  intro t
  have upper := a.cube.group_order
  have bounds := a.cube.writer_order
  have pc : a.cube.pairBase ≤ a.cube.cellBank := Nat.le_add_right ..
  have cc : a.cube.cellBank ≤ a.cube.stop := Nat.le_add_right ..
  have fg : a.cube.stop ≤ a.fragments.start := by
    change a.cube.stop ≤ CubeConstants.arenaEnd a.cube.stop a.id
    unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  have orderF : a.fragments.start ≤ a.fragments.quads ∧ a.fragments.quads ≤ a.fragments.pairs ∧
      a.fragments.pairs ≤ a.fragments.triples ∧ a.fragments.triples ≤ a.fragments.cursors ∧
      a.fragments.cursors ≤ a.fragments.external ∧ a.fragments.external ≤ a.fragments.counts :=
    ⟨le_rfl,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..,Nat.le_add_right ..⟩
  have countEnd : a.fragments.counts ≤ a.before.start := by
    change a.fragments.counts ≤ a.fragments.counts+a.fragments.cells+1; omega
  have mb : a.before.start ≤ a.before.merged := by
    unfold BeforeTasks.merged BeforeTasks.counters BeforeTasks.supplement BeforeTasks.tailWidths; omega
  obtain ⟨calls,tasks,endAt,_⟩ := a.task_bounds team frame offsets control
  change a.before.merged ≤ t.calls at calls
  change a.before.merged ≤ t.tasks at tasks
  have ac : t.calls ≤ a.after.start := by
    change a.before.limit ≤ a.before.limit+3*a.cube.cells+7*a.cube.cells+
      a.p.scratchStride*a.cube.cells+a.p.burstStride*a.cube.cells
    omega
  omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
