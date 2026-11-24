import OAI.Computability.VPVNP.CompressorCurrentGraph
import OAI.Computability.VPVNP.CompressorBlockStartupPrefix

/-!
# The current graph after the four initial block packets

The true startup supplies the number of positions. The two publishers, the
cursor scan and the role store leave the six scalar words, both head banks,
and the six incidence columns of the initial cursor state. The same fields
are available in the linked interval's post-memory at data addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockStartupPrefix.Resident

open BurstRAM Compression DescriptorSpace BlockHeaderRun CurrentGraph CursorNetwork
open scoped Fin.CommRing

variable {w a b l width n : ℕ} {L : Layout} {base : Word w} {m : Memory w}
    {X : State a l} (h : Resident L a b l width n base m X)

include h

private theorem base_count : Fintype.card X.Base = (b+l)*2^b := by
  have eqn := h.rows
  change Fintype.card X.Base * 2^l * 2^a = (b+l)*2^b * 2^l * 2^a at eqn
  exact Nat.mul_right_cancel (Nat.two_pow_pos l) (Nat.mul_right_cancel (Nat.two_pow_pos a) eqn)

/-- The raw worker reports leave the initial graph in the exact representation
used by the subsequent selected compression steps. -/
theorem current : Current L 0 X n (BlockInitialPackets.post L a b l width m) := by
  have cnt := present_counts h.scalars
  refine ⟨(h.base_count.symm ▸ h.scalars), ?_, h.rows.symm ▸ h.incidence,
    ⟨⟨_,_,_,cnt,h.positions⟩,h.arena,h.levels,h.length⟩⟩
  exact ⟨h.rows.symm ▸ h.incidenceHeads,h.tableHeads⟩

/-- The linked interval preserves the cursor frame and the role word as
well as the complete graph at its first compression boundary. -/
theorem current_live (live : Memory w)
    (agree : SourceTransport.Agree (levelStart L 0 ≤ ·) (BlockInitialPackets.post L a b l width m) live)
    (nonempty : 0 < L.levels) (fields : 14 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w) :
    Current L 0 X n live ∧ Frame.data (header w L 0+6) live =
      CursorRAM.ScheduleInit.inputs (CursorRAM.encode w (directoryBase L)) (CursorRAM.encode w 1) b l a width
        (incidenceStart L 0) ∧ live (levelStart L 0+27) = 0 := by
  obtain ⟨inc,scalars,frame,heads,tables,role,arena,levels,length⟩ := h.live live agree nonempty fields fit
  refine ⟨⟨h.base_count.symm ▸ scalars, ?_, h.rows.symm ▸ inc, ?_⟩,frame,role⟩
  · exact ⟨h.rows.symm ▸ heads,tables⟩
  · exact ⟨⟨_,_,_,present_counts scalars,h.positions⟩,arena,levels,length⟩

end CompressorRecords.BlockStartupPrefix.Resident

namespace CompressorRecords.CurrentGraph

open BurstRAM Compression DescriptorSpace CursorNetwork BlockHeaderRun
open scoped Fin.CommRing

/-- Construct the genuine initial source walk and its graph directly from
the startup post-memory, including the zero-block case. -/
theorem initial {w a b l pad : ℕ} {T : Type} [Fintype T] (L : Layout) (n : ℕ) (base : Word w)
    (m : Memory w) (hD : 1 < b+l) (hd : 2+pad = 2^a) (bits : T → ℕ)
    (ready : BlockHeaderStartup.Ready L a b l (∑ t, bits t) n base m) (fields : 30 ≤ L.shape.scalarFields)
    (fit : endAddress L < 2^w) (room : incidenceStart L 0+6*CursorRAM.rowCount b l a ≤ 2^w)
    (width : (∑ t, bits t) < 2^w) :
    let W := ∑ t, bits t
    let X := cursorState (cursorCoordinateLabels b l) hD hd bits
    SourceWalk (BlockInitialPackets.Source L a (Workspace.ports L.shape.arity base).data (header w L 0))
      (BlockInitialPackets.order L a) m (BlockInitialPackets.logs L a b l W m) ∧
      Current L 0 X n (BlockInitialPackets.post L a b l W m) := by
  have h := BlockStartupPrefix.resident L n base m hD hd bits ready fields fit room width
  exact ⟨h.walk,h.current⟩

end CompressorRecords.CurrentGraph

end VPVNP
end Computability
end OAI
