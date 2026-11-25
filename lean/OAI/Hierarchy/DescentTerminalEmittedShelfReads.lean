import OAI.Hierarchy.DescentTerminalEmitterInputFrames
import OAI.Hierarchy.DescentTerminalBookedGates
import OAI.Hierarchy.DescentTerminalChipTapes
import OAI.Hierarchy.DescentTerminalPackedLeafRAM

namespace OAI
/-! # Projection of real issued banks out of the complete terminal emitter -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalHeaderScatter DescentTerminalChipRuntime Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w : ℕ} (S : Shape) (L : Layout) (m : Memory w) (room : Room S L w)

structure AfterNames (a : ℕ) : Prop where
  names : a<L.book.names.base
  progress : a<L.route.progress.base
  gates : a<L.route.gate.base
  leaves : a<L.leaf.cells.base
  scalar : a<L.scalar

include room in
theorem after_format {i : ℕ} (f : AfterNames L i) : result S L m i=formatted S L m i := by
  rw [result,leaf_early S L _ room f.leaves f.scalar,routed,route_early _ _ _ f.progress f.gates,
    named,DescentTerminalLocalPortBook.Gather.output,DescentTerminalChipRuntime.image_low _ _ _ _ f.names]
include room in
theorem after_index {i : ℕ} (f : AfterNames L i) (early:i<L.formats.output.base) : result S L m i=indexed S L m i := by
  rw [after_format S L m room f,formatted,Header.early _ _ room.fmt early]

namespace Header
variable {A : Type} (h : Header) {w : ℕ} (mem : Memory w)
  (atRow : A ↪ Fin h.count) (ans : A→Word w)
/-- Authentic sparse fields for the dynamic little address/value records.
References to widths use the just-reached interior/exterior prefix bank. -/
structure Emits : Type where
  issued : Fin h.events→Option A
  key : A→ℕ
  site : A→ℕ
  prior : A→ℕ
  start : A→ℕ
  localRow : A→ℕ
  onPublic : A→Bool
  occurrence : ∀a,∃i,issued i=some a
  ranks : DescentTerminalScatterChip.Ranks issued key site prior start localRow onPublic h.tapes mem
  bank : DescentTerminalScatterChip.Columns atRow site prior start localRow onPublic ans h.tapes mem h.shift
  safe : h.count ≤ h.sink-h.output.base
  inBank : h.sink-h.output.base<h.output.size
  origin : h.output.base≤h.sink
  early : (stage (DescentTerminalScatterChip.dest h.tapes h.output.base h.sink)
      (DescentTerminalScatterChip.datum h.tapes h.shift) h.tapes.lane).Fits w h.output.base

theorem read (shape : Room h w) (pos : 0<w) (printed : Emits h mem atRow ans)
    (i : Fin h.count) : h.final mem (h.output.base+i.val)=Function.extend atRow ans (fun _=>(h.blank:Word w)) i := by
  exact DescentTerminalScatterChip.truth printed.issued atRow printed.key printed.site printed.prior printed.start printed.localRow
    printed.onPublic ans h.tapes h.output mem h.src h.sink h.shift h.blank pos printed.ranks printed.bank printed.occurrence
    shape.dst printed.safe printed.inBank printed.origin printed.early shape.address i
end Header

include room in
/-- Both input wire banks are actual earlier source arrays, before the
raw join and the two width preprocessors. -/
theorem rawWords {P : Type} [Fintype P] {B : ℕ} {width : P→ℕ} (ext : P ↪ ℕ) (outer : Ports width)
    (pay : Fin S.plane.rawRows×Fin B→Bool) (volume : (∑z,width z)≤S.plane.publicRows*B)
    (cap : S.plane.rawRows+2+S.plane.publicRows≤L.plane.raw.size)
    (candidate : S.plane.rawRows≤L.plane.candidate.size) (pub : S.plane.publicRows≤L.plane.output.size)
    (source : ∀i : Fin S.plane.rawRows,DescentTerminalDataPlane.exteriorRows S.plane L.plane m (L.plane.candidate.base+i.val)=
      ((DescentTerminalDenseWindow.dense B (DescentTerminalDenseGraphRead.stream pay) i.val).val:Word w))
    (actual : ∀i : Fin S.plane.publicRows,DescentTerminalDataPlane.exteriorRows S.plane L.plane m (L.plane.output.base+i.val)=
      ((DescentTerminalDenseWindow.dense B (DescentTerminalDenseGraphRead.publicStream ext outer) i.val).val:Word w))
    (before : ∀j<L.plane.raw.size,Later L (L.plane.raw.base+j) ∧ L.plane.raw.base+j<L.plane.header.rem.base)
    (j : ℕ) (fit : j<L.plane.raw.size) :
    result S L m (L.plane.raw.base+j)=((DescentTerminalRawJoin.expected ext outer pay j).val:Word w) := by
  obtain ⟨later,first⟩:=before j fit
  rw [after_plane S L m room later,DescentTerminalDataPlane.finalMem,
    DescentTerminalDenseHeaderRAM.before_inputs _ _ room.plane.widths first]
  exact DescentTerminalRawJoin.read ext outer pay L.plane.candidate L.plane.output L.plane.raw _
    room.plane.candidate room.plane.published room.plane.rawRoom cap candidate pub volume source actual j fit

end
end Hierarchy.DescentTerminalEmitter

end OAI
