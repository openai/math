import OAI.Hierarchy.DescentTerminalEmitterAllocatedRun

namespace OAI
/-! # A genuine numeric lower boundary of all writers in the terminal emitter -/
namespace Hierarchy.DescentTerminalEmitter.Allocation
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentExteriorShelf DescentExterior DescentGL
open scoped Fin.CommRing
noncomputable section
variable (s:Shape) (i f base:ℕ) (src:Sources) (plane:DescentTerminalDataPlane.Layout)
    (ext:DescentTerminalDenseHeaderRAM.Layout) (blankFmt:ℕ)
local notation "E" => layout s i f base src plane ext blankFmt

/-- Actual incoming/consumed arrays may occupy any address below this minimum. -/
def front := min plane.exterior (min plane.output.base (min plane.raw.base
  (min plane.header.rem.base (min ext.rem.base base))))

theorem original_frame {x:ℕ} (low:x<front base plane ext) :
    BeforeKey s E x ∧ AfterFlights s E x := by
  rw [front] at low
  simp only [lt_min_iff] at low
  obtain ⟨outside,pub,raw,privateWidths,publicWidths,rest⟩:=low
  constructor
  · constructor
    · change x<plane.exterior+_
      omega
    · change x<plane.exterior+_
      omega
    · change x<plane.exterior+_
      omega
  · exact ⟨pub,raw,privateWidths,«protected» s i f base src plane ext blankFmt rest publicWidths⟩

theorem original_read {w:ℕ} (m:Memory w) (ready:Room s E w) {x:ℕ} (low:x<front base plane ext) :
    result s E m x=m x := by
  have saved:=original_frame s i f base src plane ext blankFmt low
  exact printed_before s E m ready saved.1 saved.2

/-- These are the real original eight-branch inputs of the two-word clock-alternation
ROM and of any immutable payload/header shelf, calculated from one original bank end. -/
theorem retained_bank (a:Bank) (early:a.base+a.size≤front base plane ext) (j:ℕ) (hj:j<a.size) :
    BeforeKey s E (a.base+j) ∧ AfterFlights s E (a.base+j) :=
  original_frame s i f base src plane ext blankFmt (by omega)

theorem literal_run {w:ℕ} (m:Memory w) (pos:0<w) (below:∀j,(src j).base+(src j).size≤base)
    (room:endAt s i f base<2^w) (flight:DescentTerminalDataPlane.Room s.plane plane w)
    (widths:DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) (offset:ℕ)
    (index:src 1=parity offset) (format:src 13=parity offset) (leafLanes:src 38=parity offset)
    (initial:∀j:Fin 2,m (offset+j.val)=(j.val:Word w)) (early:offset+2≤front base plane ext) :
    (DescentTerminalEmitter.program (w:=w) s E).Exec m (result s E m) (time s E) ∧
    CheapCode (DescentTerminalEmitter.program (w:=w) s E) ∧
    time s E≤4096*rowsPaid s i f plane ∧ endAt s i f base≤base+60*(s.rows+s.pool+s.leaves+i+f+1) :=
  run s i f base src plane ext blankFmt m pos below room flight widths offset index format leafLanes initial
    (fun j=>original_frame s i f base src plane ext blankFmt (by omega))

end
end Hierarchy.DescentTerminalEmitter.Allocation

end OAI
