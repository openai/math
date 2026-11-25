import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepInputs
import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun

/-! # The row and gate operands through owned rows, sparse exterior and typed calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.ReaderKept

open VPVNP.BurstRAM TeamContraction.ProcessorSlots BorderVNP.Cube BorderVNP.Cube.Tally
open BorderVNP.Cube.TeamRows BorderVNP.Cube.Padding.Banks BorderVNP.FiniteEvaluator
open CellPacket.Supplement.Batch

variable {w : ℕ} {A : StartupArena} {entries pins : ℕ} {boot pinMem : Memory w}

/-- The fixed cube installer and genuine owned traversal retain every earlier word apart from the physical vertex count. -/
theorem afterOwned_word (a : CubeArena.Layout) (f : DiagonalTallyPacketEmit.Frame)
    (id : TableEntry a.n a.b a.h a.K a.s → ℕ) {before installed final : Memory w}
    (image : readings installed=CubeConstants.image (CubeConstants.inArena f a.stop a.n a.b a.h a.K a.s)
      (CubeConstants.idBase a.stop a.n a.b a.h a.K a.s) id (readings before))
    {l : TeamRowPrepare.Layout} {blocks : ℕ} {data : Data a.n l.d blocks a.b a.h a.K a.s}
    {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
    {rows : Sym2 (Fin l.d) → Fin (a.n+1) → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r es t} (P : PhysicalSetup data owner power base stop actual claimed rows pub installed)
    (run : Runs pub mac (ownedGroups a.n a.b a.h a.K a.s) r installed es t final)
    (x : ℕ) (low : x<actual ∧ x<a.stop) (ne : x≠l.frame+46) : final x=before x := by
  rw [CubeTriple.native_return_low P run x low.1 ne]
  apply Fin.ext
  change readings installed x=readings before x
  rw [image,a.constants_before f id (readings before) low.2]

/-- The genuine constant installer and an arbitrary returning owned traversal leave
the reader's ordinary controls and both pin arrays in place. The owned traversal
writes its result count at frame 46. -/
theorem afterOwned (a : CubeArena.Layout) (f : DiagonalTallyPacketEmit.Frame)
    (id : TableEntry a.n a.b a.h a.K a.s → ℕ) {before installed final : Memory w}
    (image : readings installed=CubeConstants.image (CubeConstants.inArena f a.stop a.n a.b a.h a.K a.s)
      (CubeConstants.idBase a.stop a.n a.b a.h a.K a.s) id (readings before))
    {l : TeamRowPrepare.Layout} {blocks : ℕ} {data : Data a.n l.d blocks a.b a.h a.K a.s}
    {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
    {rows : Sym2 (Fin l.d) → Fin (a.n+1) → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {r es t} (P : PhysicalSetup data owner power base stop actual claimed rows pub installed)
    (run : Runs pub mac (ownedGroups a.n a.b a.h a.K a.s) r installed es t final)
    (old : ReaderKept A entries pins boot pinMem before) (frame : l.frame=A.frame)
    (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (bounds : A.next ≤ actual ∧ A.next ≤ a.stop) : ReaderKept A entries pins boot pinMem final := by
  apply old.advance
  intro x hx
  have low := hx.below packet index
  exact afterOwned_word a f id image P run x ⟨low.trans_le bounds.1,low.trans_le bounds.2⟩
    (frame ▸ hx.ne_field (k:=46) (by decide) (by decide))

/-- The native task-row publisher and supplemental descriptor splice retain all lower words except the owned-cell count. -/
theorem afterSupplement_word {Site : Type} (rows : CellControlRows.Layout) (m m₁ : Memory w)
    (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (room : rows.toLayout.Room (readings m) w) (image : readings m₁=rows.toLayout.published (readings m))
    (span : ∀ c < rows.cells, readings m (rows.sorted+rows.padded+(rows.stops+c))-readings m (rows.sorted+rows.padded+c)-1 =
      3*((placed c).parts.length+3))
    (floor x : ℕ) (lo : x<floor) (ne : x≠rows.frame+90)
    (reserved : floor ≤ rows.calls ∧ floor ≤ rows.tasks ∧ floor ≤ rows.sorted ∧ floor ≤ rows.merged) :
    let owned := produced rows (readings m) placed geom extra
    let count := rows.before (readings m) rows.cells
    written m₁ (fun i => (owned i).cell) count x=m x := by
  intro owned count
  apply (preserve m₁ _ (i:=0) (Nat.zero_le count) x ?_).trans
  · apply Fin.ext
    change readings m₁ x=readings m x
    rw [image,task_published_outside _ _ x]
    change ¬((rows.tasks ≤ x ∧ x < rows.tasks+7*rows.cells) ∨
      (∃ c < rows.cells, x=rows.calls+3*c) ∨ x=rows.frame+90)
    rintro (⟨h,_⟩ | ⟨c,_,eq⟩ | eq) <;> omega
  · intro i _ hi
    obtain ⟨merged,_,_,tail⟩ := SignedTaskArena.produced_addresses rows (readings m) placed geom extra room hi span
    change x≠(owned i).layout.merged ∧ (x<(owned i).layout.tail ∨ (owned i).layout.tail+12 ≤ x)
    change (owned i).layout.merged=rows.merged+_ at merged
    change rows.sorted ≤ (owned i).layout.tail at tail
    omega

/-- The owned-row header and supplemental splice preserve the earlier advice and
indexes before exterior compression. They only alter high task, merged-count
and sorted descriptor tables, plus frame field 90. -/
theorem afterSupplement {Site : Type} (rows : CellControlRows.Layout) (m m₁ : Memory w)
    (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (room : rows.toLayout.Room (readings m) w) (image : readings m₁=rows.toLayout.published (readings m))
    (span : ∀ c < rows.cells, readings m (rows.sorted+rows.padded+(rows.stops+c))-readings m (rows.sorted+rows.padded+c)-1 =
      3*((placed c).parts.length+3))
    (old : ReaderKept A entries pins boot pinMem m) (frame : rows.frame=A.frame)
    (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (reserved : A.next ≤ rows.calls ∧ A.next ≤ rows.tasks ∧ A.next ≤ rows.sorted ∧ A.next ≤ rows.merged) :
    let owned := produced rows (readings m) placed geom extra
    let count := rows.before (readings m) rows.cells
    ReaderKept A entries pins boot pinMem (written m₁ (fun i => (owned i).cell) count) := by
  intro owned count
  apply old.advance
  intro x hx
  exact afterSupplement_word rows m m₁ placed geom extra room image span A.next x (hx.below packet index)
    (frame ▸ hx.ne_field (k:=90) (by decide) (by decide)) reserved

/-- All words below the sparse exterior compressor’s three output banks survive its exact write image. -/
theorem afterSparse_word (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned) {m mt : Memory w}
    (image : readings mt=SparseExterior.written l owned (readings m) l.count)
    (floor x : ℕ) (low : x<floor) (room : floor ≤ l.compact ∧ floor ≤ l.tasks ∧ floor ≤ l.counts) : mt x=m x := by
  apply Fin.ext
  change readings mt x=readings m x
  rw [image]
  apply SparseExterior.written_preserve l owned (readings m) (i:=0) (Nat.zero_le l.count) x
  intro i _ _
  simp only [SparseExterior.Owned.Outside,SparseExterior.Owned.dest]
  exact ⟨Or.inl (by omega),by omega,by omega,by omega⟩

/-- The real sparse exterior compressor only writes inside the per-cell byte
banks, two high task columns and the per-cell counts. -/
theorem afterSparse (l : SparseExterior.Layout) (owned : ℕ → SparseExterior.Owned) {m mt : Memory w}
    (image : readings mt=SparseExterior.written l owned (readings m) l.count)
    (old : ReaderKept A entries pins boot pinMem m)
    (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (room : A.next ≤ l.compact ∧ A.next ≤ l.tasks ∧ A.next ≤ l.counts) : ReaderKept A entries pins boot pinMem mt := by
  apply old.advance
  intro x hx
  exact afterSparse_word l owned image A.next x (hx.below packet index) room

/-- The true typed argument writer and every private call retain each addressed word below the call directory. -/
theorem afterTypedCalls_word (l : TypedTaskBuilder.Layout) (oldTable : ℕ → ℕ) {tasks : ℕ → TypedBatch.Task}
    (ar : l.Arenas oldTable w tasks) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {m : Memory w}
    {s es t mf} (called : Runs pub mac callOwnedCells s (TypedBatch.written m tasks (l.before oldTable l.cells)) es t mf)
    (x : ℕ) (low : x<l.calls) : mf x=m x := by
  rw [CellDispatch.memory_after_owned_calls called]
  apply TypedBatch.preserve m tasks (i:=0) (Nat.zero_le _) x
  intro i _ hi
  exact TypedTaskBuilder.below l oldTable ar hi (by have := ar.calls; omega) (Or.inl low)

/-- Both the typed field packer and all possible private-call returns preserve
the lower words. This applies to the newly compressed exterior tasks as well. -/
theorem afterTypedCalls (l : TypedTaskBuilder.Layout) (oldTable : ℕ → ℕ) {tasks : ℕ → TypedBatch.Task}
    (ar : l.Arenas oldTable w tasks) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {m : Memory w}
    {s es t mf} (called : Runs pub mac callOwnedCells s (TypedBatch.written m tasks (l.before oldTable l.cells)) es t mf)
    (old : ReaderKept A entries pins boot pinMem m) (packet : entries*w ≤ A.copied) (index : pins ≤ A.count)
    (room : A.next ≤ l.calls) : ReaderKept A entries pins boot pinMem mf := by
  apply old.advance
  intro x hx
  exact afterTypedCalls_word l oldTable ar called x ((hx.below packet index).trans_le room)

end RoutingISA.ReaderKept

end BorderVNP
end Computability
end OAI
