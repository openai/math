import OAI.Computability.BorderVNP.CellPacketGeometryTaskMarkers
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomDirectories
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportAllocation

/-! # Physical inverse descriptor ranks at the two task markers

The second sort writes a permutation of the descriptor rows. A task reads
the inverse permutation at its two raw marker ordinals, including for an
empty cell. The report tape can change the data in the receiving banks and
the number in the frame, while these inverse words lie in the earlier
geometry output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena.GeometryDirectories

/-- The ordinal and readback conditions for the two marker columns used by
the actual task builder. -/
structure MarkerBounds (g : GeometryDirectories) (cells : ℕ) (mem : ℕ → ℕ) : Prop where
  markers : cells ≤ g.stops ∧ g.stops+cells ≤ g.padded
  ranks : ∀ c < cells, mem (g.sorted+g.padded+c) < g.padded ∧
    mem (g.sorted+g.padded+(g.stops+c)) < g.padded

/-- Readback of just the inverse array transports the physical bounds.
The consuming bank may use a prefix of the geometry's cells. -/
theorem MarkerBounds.retained {g : GeometryDirectories} {cells count : ℕ} {src dst : ℕ → ℕ}
    (b : g.MarkerBounds cells src) (size : count ≤ cells)
    (keep : ∀ a, g.sorted+g.padded ≤ a → a < g.sorted+2*g.padded → dst a=src a) :
    g.MarkerBounds count dst := by
  obtain ⟨lo,hi⟩ := b.markers
  refine ⟨⟨by omega,by omega⟩,fun c hc => ?_⟩
  rw [keep _ (by omega) (by omega),keep _ (by omega) (by omega)]
  exact b.ranks c (hc.trans_le size)

end RoutingISA.SignedTaskArena.GeometryDirectories

namespace CellPacketGeometry

open ParseBatchSort VPVNP.VerifierNetwork RoutingISA.SignedTaskArena
variable {σ E : Type} [Fintype σ] [Fintype E] {k w : ℕ}

namespace LiveWords

variable {s C q : ℕ} {I Orig : Type} [Fintype I]

/-- The canonical site-major template supplies the marker caps and both
inverse rank bounds of the published physical directory. -/
theorem Template.publishedTaskRanks (T : Template E I Orig s C) (up : Frame σ (Base s k w E I))
    (anchors : Frame σ (Fin s × Fin q)) (baseOwner : Fin s → Fin C) (pin : Orig → T.Fields)
    (pad : s < 2^q) (dest H control preceding bundleBits : ℕ) (x : σ → Bool)
    (wide : 2^T.chunkDepth ≤ 2^w) (mem : ℕ → ℕ)
    (output : ∀ i : Fin (Total T.publicDepth T.chunkDepth), mem (dest+i.val) =
      value (fun j => (T.orderedFrame up anchors baseOwner pin pad dest H).eval x (.inl (i,j)))) :
    (GeometryDirectories.published dest T.publicDepth T.chunkDepth C T.chunkLabels.length
      control preceding bundleBits).MarkerBounds C mem := by
  obtain ⟨caps,ranks⟩ := T.descriptorMarkerRanks up anchors baseOwner pin pad dest H x wide mem output
  exact ⟨caps,ranks⟩

end LiveWords
end CellPacketGeometry

namespace DiagonalTallyCellReports

open RoutingISA RoutingISA.SignedTaskArena DiagonalTallyAllocation VPVNP.BurstRAM

variable {pre : BeforeTasks} {post : AfterTasks} {banks : CellBanks.Layout} {l : ReportLayout}
    {cs : List (ReportCell l)} {q : ReportCursor}

/-- Every word in the inverse descriptor range below the receiving arena
survives the literal list of report writes. -/
theorem ReportAllocation.prepare_geometry_word (alloc : ReportAllocation pre post banks l cs q)
    (mem : ℕ → ℕ) (a : ℕ) (low : a < banks.bankStart) (frame : a ≠ l.frame+35) :
    applyWrites mem (prepareWrites cs q) a = mem a := by
  rw [←prepareWrites_image,Function.update_of_ne frame,cellWrites_image]
  exact writes_outside _ _ _ fun z hz => .inl (low.trans_le (alloc.aboveBankStart z hz))

/-- Every actual report return, with its own decoded tape and initial RAM,
keeps the two geometry marker bounds for all cells visited by the task builder. -/
theorem ReportAllocation.reportReturn_markerBounds {w description cells count : ℕ}
    {pub : Arg → Word w} {mem : Memory w} (alloc : ReportAllocation pre post banks l cs q)
    (seed : PreparedReportInput pub mem cs q description) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (tape : ReportTape cs) (g : GeometryDirectories)
    (ranks : g.MarkerBounds cells (readings mem)) (size : count ≤ cells)
    (frame : l.frame+35 < g.sorted+g.padded) (below : g.sorted+2*g.padded ≤ banks.bankStart) :
    g.MarkerBounds count (readings (reportReturnEquiv seed mac s tape).val.2.2) := by
  have out := (reportReturnEquiv_spec seed mac s tape).2.2
  rw [prepareWrites_image] at out
  apply ranks.retained size
  intro a lo hi
  rw [out]
  exact (alloc.tape _ _).prepare_geometry_word _ a (hi.trans_le below) (by omega)

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
