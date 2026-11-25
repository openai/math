import OAI.Computability.BorderVNP.CubeScatterSharedArenaLayout
import OAI.Computability.BorderVNP.CubeScatterWriterSources

/-! # Inputs of the native shared writer in the actual data writer's output RAM -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.TeamContraction
open Transmission DiagonalResidueRAM
open private public_image_word from OAI.Computability.BorderVNP.CubeScatterWriterSources

/-- The scheduled team and declaration metadata survive all preceding directory
writes. The data writer publishes its real row count at frame 13 and retains the
physical record pointer at frame 12. These are precisely the shared emitter's fields. -/
theorem Layout.shared_fields (a : Layout) {w : ℕ} (pub : Arg → Word w)
    (team axis : ℕ) (owner : Fin a.header.d → ℕ) (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ)
    (m₀ m₁ m₂ : Memory w) (cells : CellBanks.Layout) (pairs : PairDirectory.Layout)
    (seed : a.ScannerWords (pub 0).val team axis owner (readings pub) (readings m₀) rows)
    (cellWords : readings m₁ = cells.written (readings m₀) cells.cells)
    (pairWords : PairDirectory.Image pairs (readings m₁) pairs.count (readings m₂))
    (frameLow : (pub 0).val+112 ≤ a.header.header)
    (cellDir : cells.dest = a.hostDirectory) (pairDir : pairs.table = a.pairDirectory) :
    let data := DataWriter.layout (readings pub) (readings m₂)
    data.output = a.records → data.count < 2^w →
      (a.sharedRows (pub 0).val axis data.count).Fields (readings (DataWriter.publish data pub m₂)) := by
  intro data output count
  let frame := (pub 0).val
  let m := DataWriter.publish data pub m₂
  have header : a.header.header+13 ≤ a.header.packetBase := by unfold CubeHeaderInstall.Inputs.packetBase; omega
  have packetHigh : a.header.packetBase ≤ a.packetEnd := Nat.le_add_right _ _
  have vert : a.vertexBase ≤ a.publicBase := Nat.le_add_right _ _
  obtain ⟨scratch,single,_,_,_,_⟩ := a.separated
  obtain ⟨power,owners,_⟩ := a.source_order
  have ownerDir : a.ownerBase+a.header.d = a.pairDirectory := rfl
  have high : a.header.header+13 ≤ a.pairDirectory := by omega
  have recs : a.pairDirectory ≤ a.records := by unfold Layout.records Layout.hostDirectory; omega
  have lower (j : ℕ) (hj : j < a.pairDirectory) (other : j ≠ frame+13) : readings m j = readings m₀ j :=
    public_image_word a (readings m₀) pub cells pairs data m₁ m₂ cellWords pairWords cellDir pairDir output j hj other
  have primary (i : ℕ) (hi : i < 112) (ne : i ≠ 13) : readings m (frame+i) = readings m₀ (frame+i) := by
    apply lower _ _ (by omega)
    change frame+112 ≤ _ at frameLow; omega
  have secondary (i : ℕ) (hi : i < 13) : readings m (a.header.header+i) = readings m₀ (a.header.header+i) := by
    change frame+112 ≤ _ at frameLow
    exact lower _ (by omega) (by omega)
  have base : readings m (frame+12) = a.records := by
    have eq : m (frame+12) = m₂ (frame+12) := by
      unfold m DataWriter.publish
      rw [Function.update_of_ne (show frame+12 ≠ frame+13 by omega)]
      apply Packing.Directory.ISA.putWords_outside
      apply Or.inl
      rw [output]; change frame+112 ≤ _ at frameLow; omega
    exact (congrArg Fin.val eq).trans output
  have num : readings m (frame+13) = data.count := by
    change (m (frame+13)).val = _
    dsimp only [m,DataWriter.publish,frame]
    rw [Function.update_self]; exact word_val _ _ count
  refine ⟨⟨base,num⟩,⟨?_,?_⟩,?_,?_,⟨?_,?_⟩,⟨?_,?_,?_⟩⟩
  · exact (primary 59 (by decide) (by decide)).trans seed.setup.d
  · exact (primary 60 (by decide) (by decide)).trans seed.setup.axes
  · exact (primary 63 (by decide) (by decide)).trans seed.setup.header
  · exact (primary 77 (by decide) (by decide)).trans seed.ownersBase
  · exact (primary 85 (by decide) (by decide)).trans seed.views
  · exact (primary 86 (by decide) (by decide)).trans seed.spacing
  · exact (secondary 1 (by decide)).trans seed.claimed
  · exact (secondary 5 (by decide)).trans seed.chosen
  · exact (secondary 6 (by decide)).trans seed.selectorCount

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
