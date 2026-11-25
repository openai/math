import OAI.Computability.BorderVNP.CellSparseExteriorSupplementalSources

/-! # The source sections used before exterior compression

The supplemental writer reads the original counts and patches four chunk
descriptors. Its successor reads the chunk sources together with the true
occupied exterior spans. The possibly vacant logical exterior lanes need
no physical content for the descriptor and chunk readback proved here.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellPacket CellSparse CellSparse.Packet CellPacket.Supplement CellPacket.Supplement.Batch

/-- View of the original placement restricted to the geometric and private
chunk sections, before the exterior writer publishes its separate encoding. -/
def chunkPlacement {Site : Type} (p : Placed Site) : Placed Site := {p with external := []}

/-- The actual seven-word task, four control words, geometry section and
returned sidecar counts give every scalar read by the supplemental writer. -/
theorem merge_stored {Site : Type} {w table controls i : ℕ} (o : Owned Site) (m : Memory w)
    (task : o.typed.Stored m table i)
    (control : WordsAt (readings m) (controls+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords])
    (tailBase : readings m (o.layout.tail+1)=o.geometry)
    (tailLength : readings m (o.layout.tail+2)=1+(o.placed.rows.flatMap record).length+o.layout.reportWords)
    (privateCount : readings m o.layout.counters=o.extra.length)
    (privateWords : readings m (o.layout.counters+1)=(o.extra.flatMap record).length)
    (endPrefix : o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length=o.layout.tail)
    (geometry : WordsAt (readings m) o.geometry (fieldList record o.placed.rows++fieldList vector o.placed.reports)) :
    Stored o.cell table controls i m := by
  have h := geometry ⟨0,by simp [fieldList]⟩
  refine ⟨tailEnd_of_taskRow m o.placed o.layout o.geometry o.callRow o.extra endPrefix task,
    control ⟨0,by simp⟩,control ⟨1,by simp⟩,control ⟨2,by simp⟩,control ⟨3,by simp⟩,
    tailBase,tailLength,?_,privateCount,privateWords⟩
  simpa [fieldList,Owned.cell,measured] using h

/-- Original scalar and section words at one actual owned supplemental row. -/
structure MergeFields {w : ℕ} {Site : Type} (o : Owned Site) (table controls i : ℕ) (m : Memory w) : Prop where
  /-- The original seven-word task header as published by the owner scan. -/
  task : o.typed.Stored m table i
  /-- Four indirect controls of this same original row. -/
  control : WordsAt (readings m) (controls+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords]
  /-- Base of the original record and report geometry. -/
  tailBase : readings m (o.layout.tail+1)=o.geometry
  /-- Length of the original unmerged geometric tail section. -/
  tailLength : readings m (o.layout.tail+2)=1+(o.placed.rows.flatMap record).length+o.layout.reportWords
  /-- Sidecar scanner's actual record count. -/
  privateCount : readings m o.layout.counters=o.extra.length
  /-- Sidecar scanner's actual scalar-word count. -/
  privateWords : readings m (o.layout.counters+1)=(o.extra.flatMap record).length
  /-- The control's report word count comes from its geometric report fields. -/
  reports : o.layout.reportWords=(fieldList vector o.placed.reports).length
  /-- The first supplemental descriptor follows the original opaque chunks. -/
  prefixEnd : o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length=o.layout.tail
  /-- All four original chunk-source sections, including the real private boxes. -/
  original : Original (chunkPlacement o.placed) o.layout o.geometry o.extra m
  /-- Scalar arithmetic of the fixed merge row fits. -/
  room : Room o.cell w
  /-- This cell's merged count lives outside its four rewritten descriptors. -/
  separate : o.layout.merged<o.layout.tail ∨ o.layout.tail+12≤o.layout.merged

/-- Chronological separation of the actual original and patched sections and
the seven-word task table. Only descriptor and chunk addresses occur. -/
structure MergeRanges {Site : Type} (owned : ℕ → Owned Site) (count table controls : ℕ) : Prop where
  /-- The ten scalar operands of each later merge row survive earlier patches. -/
  scanReads : ∀ i < count, ∀ j < i, ∀ a ∈ (owned i).cell.sources table controls i, (owned j).cell.Outside a
  /-- The original chunks stay readable through their own merge iteration. -/
  originals : ∀ i < count, ∀ k ≤ i, ∀ a, originalSource (chunkPlacement (owned i).placed)
    (owned i).layout (owned i).geometry (owned i).extra a → (owned k).cell.Outside a
  /-- Once the four descriptors are patched, later rows leave the initializer's
  descriptors and actual chunks intact. -/
  patched : ∀ i < count, ∀ k, i<k → k<count → ∀ a,
    (⟨Supplement.task (owned i).layout (chunkPlacement (owned i).placed) (owned i).geometry (owned i).extra,
      (owned i).callRow⟩ : TypedBatch.Task).SourceAt table i a → (owned k).cell.Outside a
  /-- Every seven-word task header survives the whole merge. -/
  taskRows : ∀ i < count, ∀ k < count, ∀ j < 7, (owned k).cell.Outside (table+7*i+j)

/-- Decode every original scalar from the physical merge source. -/
theorem MergeFields.scalar {w table controls i : ℕ} {Site : Type} {o : Owned Site} {m : Memory w}
    (h : MergeFields o table controls i m) : Stored o.cell table controls i m :=
  merge_stored o m h.task h.control h.tailBase h.tailLength h.privateCount h.privateWords h.prefixEnd h.original.geom

/-- Actual geometric and original opaque sources at the next sparse writer's
typed row after all the supplemental patches. -/
theorem MergeRanges.sources {w table controls count : ℕ} {Site : Type} {owned : ℕ → Owned Site}
    (ranges : MergeRanges owned count table controls) (m : Memory w)
    (fields : ∀ i < count, MergeFields (owned i) table controls i m) (i : ℕ) (hi : i<count) :
    let t := (owned i).typed
    let mt := written m (fun j => (owned j).cell) count
    t.Stored mt table i ∧ WordsAt (readings mt) t.cell.descriptorBase (CellPacket.descriptors t.cell.chunks) ∧
      ∀ c ∈ t.cell.chunks, c.Stored (readings mt) := by
  let h := fields i hi
  exact patchedMetadata m owned i hi h.task h.scalar h.room h.reports h.prefixEnd h.original h.separate
    (ranges.originals i hi) (ranges.patched i hi) (ranges.taskRows i hi)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
