import OAI.Hierarchy.DescentTerminalHomeProgram
import OAI.Hierarchy.DescentTerminalPositionPrice
import OAI.Hierarchy.DescentTerminalEmitterPrice

namespace OAI
/-! # Timing the complete measured terminal procedure on its literal row capacities -/

namespace Hierarchy.DescentTerminalCompiledPrefix
open DescentTerminalVertexFields DescentTerminalEmitter
noncomputable section
namespace Suffix

theorem slots_price (S : DescentTerminalCompiledPrefix.Shape) (L : DescentTerminalCompiledPrefix.Layout) :
    slotsTime S L ≤ 1200*(S.sites+S.terminal.rows+S.packets+1) := by
  have plan:=DescentTerminalRowPlan.tariff L.row S.sites S.terminal.rows
  have sort:=DescentTerminalExteriorPackets.ticks L.homes S.sites S.packets
  unfold slotsTime
  rw [DescentTerminalSiteOffsets.time_eq]
  omega

theorem price (S : DescentTerminalCompiledPrefix.Shape) (L : DescentTerminalCompiledPrefix.Layout) (blocks : ℕ) :
    time S L blocks≤(4+(S.sites+1)*(26+234*blocks))+
      1200*(S.sites+S.terminal.rows+S.packets+1)+4400*volume S.terminal L.emit := by
  have wiring:=slots_price S L
  have emit:=DescentTerminalEmitter.clocks S.terminal L.emit
  have pool:S.terminal.pool+1≤volume S.terminal L.emit:=by unfold DescentTerminalEmitter.volume;omega
  unfold time
  rw [DescentTerminalVertexFields.gather_cost]
  omega

end Suffix

/-- One common paid row bank, allocated once from the worst selected graph.
Each real width-header row can appear at its two endpoints. The doubled
dense source includes the two guard words and the physical dyadic rounding. -/
structure RowCap (S : DescentTerminalCompiledPrefix.Shape) (L : DescentTerminalCompiledPrefix.Layout)
    (paid : ℕ) : Prop where
  packed : S.terminal.pool≤paid
  routes : S.terminal.rows≤paid
  cells : S.terminal.leaves≤paid
  raw : L.emit.plane.raw.size≤2*(paid+S.packets+4)
  external : S.terminal.plane.publicRows≤S.packets+2
  widths : S.terminal.plane.headerRows≤paid+1
  idx : L.emit.indices.count≤paid
  fmt : L.emit.formats.count≤paid
  idxEnds : L.emit.indices.events≤2*paid
  fmtEnds : L.emit.formats.events≤2*paid

theorem RowCap.price {S : DescentTerminalCompiledPrefix.Shape} {L : DescentTerminalCompiledPrefix.Layout} {paid : ℕ}
    (rows : RowCap S L paid) (blocks : ℕ) :
    Suffix.time S L blocks≤(4+(S.sites+1)*(26+234*blocks))+
      65536*(S.sites+S.packets+paid+1) := by
  have before:=Suffix.price S L blocks
  have bounds:=rows
  rcases bounds with ⟨a,b,c,d,e,f,g,h,i,j⟩
  unfold DescentTerminalEmitter.volume at before
  change _≤_ + _ + 4400*(1+S.packets+_+_+_+_+_+_+_+_+_+_) at before
  omega

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
