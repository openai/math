import OAI.Hierarchy.DescentTerminalPlacedHeaderRoom
import OAI.Hierarchy.DescentTerminalHeaderSourceWords

namespace OAI
/-! # Strong input fit for the two authentic draft scatters -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalRowArena
open DescentTerminalPaidHeaderEvents DescentTerminalHeaderDraft DescentTerminalHeaderScatter
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {blocks w : ℕ} (S : DescentTerminalCompiledPrefix.Shape) (I : Input) (base : ℕ)
    (s : Fixed) (O : Output) (F : DescentTerminalVertexFields.MaskedShelf blocks)
local notation "E_" => emitter S I base
local notation "f_" => fixed s S I base

theorem native_room (prior : Uses s O I.sources) (old : Earlier S I base F w)
    (room : endAddress S I base<2^w) (fmt : Bool) :
    let h := if fmt then (E_).formats else (E_).indices
    let t := wires f_ O (fieldBank (bodyPlane S I base).header fmt)
        (fieldBank (publicHeader S I base) fmt)
    S.terminal.rows<h.output.size ∧
      (stage (DescentTerminalScatterChip.dest t h.output.base (h.output.base+S.terminal.rows))
        (DescentTerminalScatterChip.datum t (if fmt then 0 else S.terminal.plane.rawRows+2))
        (f_).lane).Fits w h.output.base := by
  have issued := readable S I base F old room fmt
  cases fmt <;> simpa only [Bool.false_eq_true,ite_false,ite_true,emitter,Allocation.layout,
      Allocation.header,operands s O S I base prior,fieldBank,wires] using issued

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
