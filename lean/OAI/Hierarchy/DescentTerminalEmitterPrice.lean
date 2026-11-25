import OAI.Hierarchy.DescentTerminalEmitter

namespace OAI
/-! # One native tariff for the fixed program that issues all four terminal banks -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescentTerminalHeaderScatter
open scoped Classical Fin.CommRing
noncomputable section
def volume (S : Shape) (L : Layout) :=
  1+S.plane.exteriors*2^(S.plane.headBits+S.plane.restBits)+S.plane.publicRows+L.plane.raw.size+
  S.plane.headerRows+L.indices.count+L.indices.events+L.formats.count+L.formats.events+S.rows+S.pool+S.leaves

theorem header_ticks (h : Header) : h.time≤12+6*h.count+2048*h.events := by
  have measured : (stage (DescentTerminalScatterChip.put h.tapes h.output h.sink)
    (DescentTerminalScatterChip.datum h.tapes h.shift) h.tapes.lane).work = 191 := rfl
  unfold Header.time DescentTerminalScatterChip.boundedCost DescentTerminalHeaderScatter.cost
  rw [measured]
  change (4+h.count*6)+((4+386*(2*h.events))+(4+6*h.events)) ≤ _
  omega

theorem leaf_ticks (L : DescentTerminalLeafFold.Layout) (n k : ℕ) :
    DescentTerminalLeafFold.work L n k≤32+128*n+512*k := by
  have row : (DescentTerminalLeafFold.row L).work = 46 := rfl
  have lookup : (DescentTerminalLeafFold.lookup L).work = 22 := rfl
  unfold DescentTerminalLeafFold.work
  rw [row, lookup]
  change (((4+6*(n+1))+(4+96*(2*k)))+(3+12*k))+(4+48*n) ≤ _
  omega

theorem clocks (S : Shape) (L : Layout) : time S L≤4096*volume S L := by
  have a:=DescentTerminalDataPlane.clock S.plane L.plane
  have b:=DescentTerminalDenseHeaderRAM.linear_cost S.plane.headerRows L.exteriorWidths
  have c:=header_ticks L.indices;have d:=header_ticks L.formats
  have e:=DescentTerminalRouteIssue.clocks_bound L.route S.rows
  have f:=leaf_ticks L.leaf S.pool S.leaves
  have costBook : L.book.load.work = 58 := rfl
  unfold time volume
  rw [costBook]
  omega

end
end Hierarchy.DescentTerminalEmitter

end OAI
