import OAI.Hierarchy.DescentTerminalPlacedLiteral
import OAI.Hierarchy.DescentTerminalRowArenaSortHigh

namespace OAI
/-! # The allocator columns survive the sort, sparse event publication and incoming flights -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalRowArena DescentTerminalEmitter DescentTerminalVertexFields
noncomputable section
variable {w blocks:ℕ} (S:Shape) (I:Input) (base:ℕ) (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
local notation "orig" => takeOff S I base
local notation "μ" => Suffix.events S L F
local notation "η" => Suffix.positioned S L

theorem named_preserves (m:Memory w) (ready:DescentTerminalEmitter.Room S.terminal (L).emit w)
    {x:ℕ} (before:x<orig) : named S.terminal (L).emit m x=m x := by
  have pos:=after_start S I base O (a:=x) (by change x<orig+_;omega)
  have key:BeforeKey S.terminal (L).emit x:=by constructor <;> change x<orig+_ <;> omega
  have whole:=printed_before S.terminal (L).emit m ready key pos
  have late:=leaf_early S.terminal (L).emit (routed S.terminal (L).emit m) ready pos.later.leaves pos.later.scalar
  have names:=route_early (L).emit.route S.terminal.rows (named S.terminal (L).emit m) pos.later.progress pos.later.gates
  exact names.symm.trans (late.symm.trans whole)

theorem formatted_preserves (m:Memory w) (ready:DescentTerminalEmitter.Room S.terminal (L).emit w)
    {x:ℕ} (before:x<orig) : formatted S.terminal (L).emit m x=m x := by
  have pos:=after_start S I base O (a:=x) (by change x<orig+_;omega)
  have namedOut:=named_preserves S I base O m ready before
  exact (DescentTerminalChipRuntime.image_low _ _ _ _ pos.later.names).symm.trans namedOut

/-- At the end of both endpoint passes and the sparse directory publication,
all earlier mutable row and offset bands still contain their computed values. -/
theorem events_before_sort (m:Memory w) (low:Earlier S I base F w) (room:endAddress S I base<2^w)
    {x:ℕ} (before:x<(A).atBand 14) : μ m x=η m x := by
  have bounds:=stages S I base
  have firstEnd:(A).finish≤pageEnd S I base:=bounds.1
  have fit:(A).finish<2^w:=(firstEnd.trans (bounds.2.1.trans
    (bounds.2.2.1.trans (bounds.2.2.2.1.trans bounds.2.2.2.2)))).trans_lt room
  have geometry:=(A).sort_room low.old fit
  have front:x<(A).finish:=before.trans_le ((A).band_mono (by decide : 14≤22))
  have payload:x<(page A).base:=front
  have event:x<(events A S.terminal.pool).base:=front.trans_le (Nat.le_add_right ..)
  have dest:(L).emit.leaf.event.base=(events A S.terminal.pool).base:=by
    change (inputs S I base 40).base=_;simp [inputs]
  have output:x<DescentTerminalPacketSlotRAM.out (A).order (A).packets (A).sites:=by
    have less := before.trans_le ((A).band_mono (by decide : 14≤17))
    change x<(A).atBand 17+_+_
    omega
  have directory_base : (L).directory.texture.base = (page A).base := rfl
  unfold Suffix.events DescentTerminalEmitter.issued Suffix.pages maskedMem
  simp only [ProtocolRAM.image,fillSegment,dest,directory_base,not_le.mpr event,not_le.mpr payload,false_and,ite_false]
  unfold Suffix.sockets
  change DescentTerminalPacketSlotRAM.after (A).order (A).packets (A).sites _ x = _
  rw [DescentTerminalPacketSlotRAM.retained _ _ _ _ _ (.inl output)]
  unfold DescentTerminalExteriorPackets.sorted
  refine (ProtocolRAMEndpointSort.frame _ geometry.fits _ _ x
      (.inl (before.trans_le ((A).band_mono (by decide : 14≤15))))
      (.inl (before.trans_le ((A).band_mono (by decide : 14≤16))))
      (.inl (before.trans_le ((A).band_mono (by decide : 14≤17))))).trans ?_
  exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl before)

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
