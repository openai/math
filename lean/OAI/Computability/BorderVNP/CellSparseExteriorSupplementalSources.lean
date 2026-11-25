import OAI.Computability.BorderVNP.CellPacketSupplementalPrepare

/-! # Original chunk sources on the memory between the supplemental and exterior passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM CellSparse CellSparse.Packet

variable {w count tasks controls : ℕ} {Site : Type}

/-- The source placement restricted to the packet metadata read by the supplemental pass. -/
def Owned.metadata (o : Owned Site) : Placed Site := { o.placed with external := [] }

/-- The original descriptor prefix, original-site bodies, geometry and supplemental
records supply all the metadata reads before an exterior buffer is encoded. -/
theorem metadataOriginal (o : Owned Site) (m : Memory w)
    (rows : WordsAt (readings m) o.placed.descriptorBase (CellPacket.descriptors (prefixChunks o.placed)))
    (boxes : ∀ c ∈ prefixChunks o.placed, c.Stored (readings m))
    (geom : WordsAt (readings m) o.geometry (fieldList record o.placed.rows++fieldList vector o.placed.reports))
    (supp : WordsAt (readings m) o.layout.supplement (o.extra.flatMap record)) :
    Original o.metadata o.layout o.geometry o.extra m := by
  refine ⟨rows,boxes,geom,supp,?_⟩
  intro j hj
  exact False.elim (Nat.not_lt_zero j hj)

/-- The real seven-word row survives the supplemental stores. Its full patched
descriptor stream and original-site sources are readable before the sparse pass
publishes the encoded exterior and its two replacement operands. -/
theorem patchedMetadata (m : Memory w) (owned : ℕ → Owned Site) (i : ℕ) (hi : i<count) :
    let o := owned i
    let cells := fun j => (owned j).cell
    let patched := written m cells count
    o.typed.Stored m tasks i →
    Stored o.cell tasks controls i m → Room o.cell w →
    o.layout.reportWords=(fieldList vector o.placed.reports).length →
    o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length=o.layout.tail →
    Original o.metadata o.layout o.geometry o.extra m →
    (o.layout.merged < o.layout.tail ∨ o.layout.tail+12 ≤ o.layout.merged) →
    (∀ k ≤ i, ∀ a, originalSource o.metadata o.layout o.geometry o.extra a → (cells k).Outside a) →
    (∀ k, i < k → k < count → ∀ a,
      (⟨Supplement.task o.layout o.metadata o.geometry o.extra,o.callRow⟩ : TypedBatch.Task).SourceAt tasks i a →
      (cells k).Outside a) →
    (∀ k < count, ∀ j < 7, (cells k).Outside (tasks+7*i+j)) →
    o.typed.Stored patched tasks i ∧
      WordsAt (readings patched) o.typed.cell.descriptorBase (CellPacket.descriptors o.typed.cell.chunks) ∧
      ∀ c ∈ o.typed.cell.chunks, c.Stored (readings patched) := by
  intro o cells patched row scalars room report prefixEnd original self early later taskRows
  have source := typed_stored m cells hi o.metadata o.geometry o.callRow o.extra rfl report prefixEnd
    scalars room original self early later
  exact ⟨task_row m cells o.typed row taskRows,source.descriptors,source.chunks⟩

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI
