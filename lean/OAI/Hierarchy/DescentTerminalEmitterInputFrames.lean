import OAI.Hierarchy.DescentTerminalEmitterFrames

namespace OAI
/-! # Earlier memory retained by the terminal emitter -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentExteriorShelf DescentExterior DescentGL
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (S : Shape) (L : Layout)

structure AfterFlights (S : Shape) (L : Layout) (p : ℕ) : Prop where
  pub : p<L.plane.output.base
  raw : p<L.plane.raw.base
  widths : p<L.plane.header.rem.base
  later : Later L p

theorem after_flights (m : Memory w) (room : Room S L w) {p : ℕ} (hi : AfterFlights S L p) :
    result S L m p=DescentTerminalDataPlane.exterior S.plane L.plane m p := by
  rw [after_plane S L m room hi.later,DescentTerminalDataPlane.finalMem,
    DescentTerminalDenseHeaderRAM.before_inputs _ _ room.plane.widths hi.widths,
    DescentTerminalDataPlane.file,DescentTerminalRawJoin.output,DescentTerminalChipRuntime.image_low _ _ _ _ hi.raw,
    DescentTerminalDataPlane.exteriorRows,DescentTerminalChipRuntime.image_low _ _ _ _ hi.pub]

structure BeforeKey (S : Shape) (L : Layout) (p : ℕ) : Prop where
  keys : p<keyAt S.plane.headBits S.plane.restBits S.plane.bitLanes S.plane.exteriors L.plane.exterior
  first : p<start S.plane.headBits S.plane.restBits S.plane.bitLanes S.plane.exteriors L.plane.exterior
  sticky : p<flagOut (j:=S.plane.headBits) (r:=S.plane.restBits) (t:=S.plane.bitLanes)
    (e:=S.plane.exteriors) L.plane.exterior

theorem printed_before (m : Memory w) (room : Room S L w) {p : ℕ} (lo : BeforeKey S L p) (hi : AfterFlights S L p) :
    result S L m p=m p := by
  rw [after_flights S L m room hi,DescentTerminalDataPlane.exterior,flaggedMem,DescentExteriorRejectWord.before _ _ _ lo.sticky]
  unfold serviceMemory DescentExteriorFetch.finalMem
  let rows := S.plane.exteriors * 2^(S.plane.headBits+S.plane.restBits)
  have later (delta : ℕ) :
      p<start S.plane.headBits S.plane.restBits S.plane.bitLanes S.plane.exteriors L.plane.exterior+delta :=
    lo.first.trans_le (Nat.le_add_right _ delta)
  rw [DescentTerminalChipRuntime.image_low _ _ _ _ (later (2*rows)),
    DescentTerminalChipRuntime.image_low _ _ _ _ (later rows),
    DescentTerminalChipRuntime.image_low _ _ _ _ lo.first,
    DescentTerminalChipRuntime.image_low _ _ _ _ lo.keys]

end
end Hierarchy.DescentTerminalEmitter

end OAI
