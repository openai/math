import OAI.Hierarchy.DescentTerminalPlacedHeaderColumns

namespace OAI
/-! # Address bounds at the beginning of a physical header overwrite -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitter DescentTerminalRowArena
open DescentTerminalHeaderScatter ThreeFlat.RAM PhysicalProcedure DescriptorExpr
noncomputable section
set_option quotPrecheck false
variable {blocks w : ℕ} (S : DescentTerminalCompiledPrefix.Shape) (I : Input) (base : ℕ)
    (F : DescentTerminalVertexFields.MaskedShelf blocks)
local notation "planeS" => S.terminal.plane
local notation "origin" => takeOff S I base
local notation "flightEnd" => DescentTerminalDataPlane.Arena.finish planeS origin
local notation "A" => rowArena S I base
theorem inputs_before (old : Earlier S I base F w) (j : Fin 43) :
    (inputs S I base j).base+(inputs S I base j).size ≤ flightEnd := by
  obtain ⟨pages,templates,flights,issue,paid⟩:=stages S I base
  unfold inputs
  split
  · have enough:=(A).stride_min
    have hfin:(A).start+2≤(A).finish:=by change _≤(A).start+22*(A).stride;have:=S.sites_pos;change 2*S.sites+_+_+1<(A).stride at enough;omega
    exact hfin.trans (pages.trans (templates.trans flights))
  split
  · change DescentTerminalDataPlane.Arena.headerBase planeS origin+2*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
      DescentTerminalDataPlane.Arena.headerBase planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
  split
  · change DescentTerminalDataPlane.Arena.second planeS origin+2*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
      DescentTerminalDataPlane.Arena.second planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
  split
  · change DescentTerminalDataPlane.Arena.headerBase planeS origin+3*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
      DescentTerminalDataPlane.Arena.headerBase planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
  split
  · change DescentTerminalDataPlane.Arena.second planeS origin+3*DescentTerminalDataPlane.Arena.size (planeS).headerRows+DescentTerminalDataPlane.Arena.size (planeS).headerRows≤
      DescentTerminalDataPlane.Arena.second planeS origin+4*DescentTerminalDataPlane.Arena.size (planeS).headerRows;omega
  split
  · exact templates.trans flights
  exact (DescentTerminalEmitter.Compact.sources_below _ _ old.originals j).trans flights

private theorem scatter_inside {bits : ℕ} (sh : DescentTerminalEmitter.Shape) (i f begin_ : ℕ)
    (cols : Allocation.Sources) (below : ∀j,(cols j).base+(cols j).size≤begin_)
    (top : Allocation.endAt sh i f begin_<2^bits) (fmt : Bool) (shift blank : ℕ) :
    let h := Allocation.header sh i f begin_ cols fmt shift blank
    sh.rows<h.output.size ∧
      (stage (DescentTerminalScatterChip.dest h.tapes h.output.base h.sink)
        (DescentTerminalScatterChip.datum h.tapes h.shift) h.tapes.lane).Fits bits h.output.base := by
  have big:=Allocation.reserve_fit sh i f
  unfold Allocation.reserve at big
  cases fmt
  all_goals constructor
  all_goals first
    | change sh.rows<Allocation.slab sh i f; omega
    | simp only [Allocation.header,Allocation.legs,DescentTerminalScatterChip.dest,
        DescentTerminalScatterChip.target,DescentTerminalScatterChip.datum,DescentTerminalScatterChip.source,
        DescentTerminalScatterChip.group,DescentTerminalScatterChip.event,DescentTerminalScatterChip.chunk,
        DescentTerminalScatterChip.live,stage,Expr.Fits,Bool.false_eq_true,ite_false,ite_true]
      repeat' first | apply Allocation.input_fits sh i f begin_ cols below top | constructor

theorem readable (old : Earlier S I base F w) (room : endAddress S I base<2^w) (fmt : Bool) :
    let h := if fmt then (emitter S I base).formats else (emitter S I base).indices
    S.terminal.rows<h.output.size ∧
      (stage (DescentTerminalScatterChip.dest h.tapes h.output.base h.sink)
        (DescentTerminalScatterChip.datum h.tapes h.shift) h.tapes.lane).Fits w h.output.base := by
  have top := (stages S I base).2.2.2.2.trans_lt room
  cases fmt
  · exact scatter_inside S.terminal I.indexEvents I.formatEvents flightEnd _ (inputs_before S I base F old)
      top false (S.terminal.plane.rawRows+2) 0
  · exact scatter_inside S.terminal I.indexEvents I.formatEvents flightEnd _ (inputs_before S I base F old)
      top true 0 I.blank

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan.HeaderColumns

end OAI
