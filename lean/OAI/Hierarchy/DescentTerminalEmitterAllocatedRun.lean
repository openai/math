import OAI.Hierarchy.DescentTerminalEmitterParity
import OAI.Hierarchy.DescentTerminalEmitterPrice

namespace OAI
/-! # The actual fixed allocated emitter and its one worst-case tariff -/
namespace Hierarchy.DescentTerminalEmitter.Allocation
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section
variable {w:ℕ} (s:Shape) (i f base:ℕ) (src:Sources) (plane:DescentTerminalDataPlane.Layout)
    (ext:DescentTerminalDenseHeaderRAM.Layout) (blankFmt:ℕ)
local notation "E" => layout s i f base src plane ext blankFmt

def rowsPaid := 1+s.plane.exteriors*2^(s.plane.headBits+s.plane.restBits)+s.plane.publicRows+
  plane.raw.size+s.plane.headerRows+3*s.rows+s.pool+s.leaves+i+f

theorem tariff : time s E≤4096*rowsPaid s i f plane := by
  apply (clocks s E).trans
  apply Nat.mul_le_mul_left
  change 1+_+_+plane.raw.size+s.plane.headerRows+s.rows+i+s.rows+f+s.rows+s.pool+s.leaves≤_
  unfold rowsPaid
  omega

/-- All four mutable subpasses execute after the arrived physical plane using the ten
fixed numerical regions. Only the paid read-only header lane constants are needed:
both values already present in the shared earlier parity bank. -/
theorem run (m:Memory w) (pos:0<w) (below:∀j,(src j).base+(src j).size≤base)
    (room:endAt s i f base<2^w) (flight:DescentTerminalDataPlane.Room s.plane plane w)
    (widths:DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) (start:ℕ)
    (index:src 1=parity start) (format:src 13=parity start) (leafLanes:src 38=parity start)
    (initial:∀j:Fin 2,m (start+j.val)=(j.val:Word w))
    (survive:∀j:Fin 2,BeforeKey s E (start+j.val) ∧ AfterFlights s E (start+j.val)) :
    (DescentTerminalEmitter.program (w:=w) s E).Exec m (result s E m) (time s E) ∧
    CheapCode (DescentTerminalEmitter.program (w:=w) s E) ∧
    time s E≤4096*rowsPaid s i f plane ∧ endAt s i f base≤base+60*(s.rows+s.pool+s.leaves+i+f+1) := by
  have cap:=inner_room s i f base src below room plane ext blankFmt flight widths
  have word:=installed_parity s i f base src plane ext blankFmt m cap pos start index format leafLanes initial survive
  have exec:=DescentTerminalEmitter.run s E m pos cap word
  refine ⟨?_, ?_, tariff s i f base src plane ext blankFmt, price s i f base⟩
  · exact @exec.1
  · exact @exec.2

end
end Hierarchy.DescentTerminalEmitter.Allocation

end OAI
