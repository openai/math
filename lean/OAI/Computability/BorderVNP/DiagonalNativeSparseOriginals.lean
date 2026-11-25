import OAI.Computability.BorderVNP.DiagonalNativeSparseProtection
import OAI.Computability.BorderVNP.CellPacketSupplementalPrepare

/-! # Genuine descriptor and private-body sources remain outside the RLE stores -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellPacket CellSparse CellSparse.Packet

/-- The original task's descriptor prefix, opaque boxes, geometry rows and reported
count words lie in the low source region. The patched merged count and supplemental
records live between the fragment output and the call table. These bounds prove the
entire read-footprint condition of the physical sparse serializer. -/
theorem supplemental_inputRegion {Site : Type} (a : SignedTaskArena.Layout) (count : ℕ)
    (o : Supplement.Batch.Owned Site)
    (prefixEnd : o.placed.descriptorBase+(CellPacket.descriptors (Supplement.prefixChunks o.placed)).length=o.layout.tail)
    (tailEnd : o.layout.tail+12 ≤ a.fragments.external)
    (inputs : ∀ c ∈ Supplement.prefixChunks o.placed, c.endSource ≤ a.fragments.external)
    (geometry : o.geometry+1+(o.placed.rows.flatMap record).length+(fieldList vector o.placed.reports).length ≤ a.fragments.external)
    (merged : a.fragments.limit ≤ o.layout.merged ∧ o.layout.merged+1 ≤ a.before.limit)
    (supplement : a.fragments.limit ≤ o.layout.supplement ∧ o.layout.supplement+(o.extra.flatMap record).length ≤ a.before.limit)
    {addr : ℕ} (source : TypedSources o.typed addr) : inputRegion a count addr := by
  have calls : a.before.limit ≤ (a.tasks 0 0 0 0).tasks := Nat.le_add_right _ _
  rcases source with ⟨_,hi⟩ | ⟨c,member,lo,hi⟩
  · change addr < o.placed.descriptorBase+3*(Supplement.prefixChunks o.placed++Supplement.tailChunks o.layout o.placed o.geometry o.extra).length at hi
    rw [CellPacket.descriptors_length] at prefixEnd
    rw [List.length_append,show (Supplement.tailChunks o.layout o.placed o.geometry o.extra).length=4 from rfl,Nat.mul_add] at hi
    exact Or.inl (by omega)
  · change c ∈ Supplement.prefixChunks o.placed++Supplement.tailChunks o.layout o.placed o.geometry o.extra at member
    rcases List.mem_append.mp member with first | last
    · exact Or.inl (hi.trans_le (inputs c first))
    · simp only [Supplement.tailChunks,List.mem_cons,List.not_mem_nil,or_false] at last
      rcases last with rfl | rfl | rfl | rfl <;> simp only [Chunk.base,Chunk.endSource,List.length_cons,List.length_nil] at lo hi
      · exact Or.inr (Or.inl ⟨merged.1.trans lo,hi.trans_le (merged.2.trans calls)⟩)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨supplement.1.trans lo,hi.trans_le (supplement.2.trans calls)⟩)
      · exact Or.inl (by omega)

/-- Distinct compact global-cell ordinals and the actual original-site windows imply
every independent typed task pointer, descriptor and data chunk survives publication. -/
theorem protected_supplemented {Site : Type} (a : SignedTaskArena.Layout) (frame ctl count : ℕ)
    (owned : ℕ → Owned) (old : ℕ → Supplement.Batch.Owned Site)
    (global : ∀ i < count, (owned i).global < a.fragments.cells)
    (width : ∀ i < count, (owned i).field.bytes.length ≤ a.fragments.stride)
    (distinct : Function.Injective (fun i : Fin count => (owned i.val).global))
    (placed : ∀ i < count, let o := old i
      o.placed.descriptorBase+(CellPacket.descriptors (Supplement.prefixChunks o.placed)).length=o.layout.tail ∧
      o.layout.tail+12 ≤ a.fragments.external ∧
      (∀ c ∈ Supplement.prefixChunks o.placed, c.endSource ≤ a.fragments.external) ∧
      o.geometry+1+(o.placed.rows.flatMap record).length+(fieldList vector o.placed.reports).length ≤ a.fragments.external ∧
      (a.fragments.limit ≤ o.layout.merged ∧ o.layout.merged+1 ≤ a.before.limit) ∧
      (a.fragments.limit ≤ o.layout.supplement ∧ o.layout.supplement+(o.extra.flatMap record).length ≤ a.before.limit)) :
    Protected (batchLayout a frame ctl count) owned (fun i => (old i).typed) := by
  apply protected_from_arena a frame ctl count owned _ global width distinct
  intro i hi addr reads
  obtain ⟨first,last,boxes,geometry,merged,extra⟩ := placed i hi
  exact supplemental_inputRegion a count (old i) first last boxes geometry merged extra reads

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
