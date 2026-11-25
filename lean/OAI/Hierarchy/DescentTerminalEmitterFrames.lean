import OAI.Hierarchy.DescentTerminalEmitter

namespace OAI
/-! # Every stage of the terminal issuer preserves prior physical records and read-only advice -/
namespace Hierarchy.DescentTerminalEmitter
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalHeaderScatter
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

theorem Header.early (h : Header) (m : Memory w) (fit : h.Room w) {j : ℕ} (lo : j<h.output.base) :
    h.final m j=m j := by
  exact DescentTerminalScatterChip.before h.tapes h.output h.src h.events h.count h.sink h.shift h.blank m
    fit.dst (by have:=fit.address;omega) lo


theorem leaf_early (S : Shape) (L : Layout) (m : Memory w) (room : Room S L w) {j : ℕ}
    (first:j<L.leaf.cells.base) (last:j<L.scalar) :
    DescentTerminalLeafFold.final L.leaf m S.pool S.leaves L.scratch L.scalar j=m j := by
  let leaf:=L.leaf
  have fit:=room.leaf
  have endCells:=fit.2.2
  have safe : j<L.scratch:=by omega
  have endAt : L.scratch<2^w:=by have:=room.endLeaf;omega
  have away (i : Fin S.leaves) : (DescentTerminalLeafFold.selected leaf m S.pool S.leaves i).1.val≠j := by
    change ((bounded leaf.cells (DescentTerminalLeafFold.address leaf)).eval
      (DescentTerminalLeafFold.cleared leaf S.pool m) ((field i 0).val:Word w)).val≠j
    rw [bounded_val leaf.cells _ _ _ fit endAt]
    change L.leaf.cells.base + _ ≠ j
    omega
  calc
    DescentTerminalLeafFold.final leaf m S.pool S.leaves L.scratch L.scalar j =
        DescentTerminalLeafFold.reduced leaf m S.pool S.leaves L.scratch j :=
      DescentTerminalChipRuntime.image_low _ L.scalar S.pool (DescentTerminalLeafFold.lookup leaf) last
    _ = DescentTerminalLeafFold.staged leaf S.pool S.leaves L.scratch m j :=
      ProtocolRAMWeightedScatter.frame (fun i=>(DescentTerminalLeafFold.selected leaf m S.pool S.leaves i).1.val)
        (fun i=>(DescentTerminalLeafFold.selected leaf m S.pool S.leaves i).2.val)
        (DescentTerminalLeafFold.staged leaf S.pool S.leaves L.scratch m) S.leaves j away
    _ = DescentTerminalLeafFold.cleared leaf S.pool m j :=
      DescentTerminalChipRuntime.image_low _ L.scratch (2*S.leaves) (DescentTerminalLeafFold.row leaf) safe
    _ = m j := DescentTerminalChipRuntime.image_low m leaf.cells.base (S.pool+1) (.lit 0) first


theorem route_early (L : DescentTerminalRouteIssue.Layout) (n : ℕ) (m : Memory w) {j : ℕ}
    (one:j<L.progress.base) (two:j<L.gate.base) : DescentTerminalRouteIssue.finalMem L n m j=m j := by
  simp [DescentTerminalRouteIssue.finalMem,DescentTerminalRouteIssue.progress,DescentTerminalHeaderPrefixRAM.result,
    image,fillSegment,not_le.mpr one,not_le.mpr two]

/-- The memory computed by the planes is kept verbatim below each of the six
later output banks. In particular its real cutoff and both flag words
can be observed directly after the local-book and leaf stages. -/
structure Later (L : Layout) (addr : ℕ) : Prop where
  external : addr<L.exteriorWidths.rem.base
  indices : addr<L.indices.output.base
  formats : addr<L.formats.output.base
  names : addr<L.book.names.base
  progress : addr<L.route.progress.base
  gates : addr<L.route.gate.base
  leaves : addr<L.leaf.cells.base
  scalar : addr<L.scalar

theorem after_plane (S : Shape) (L : Layout) (m : Memory w) (room : Room S L w) {j : ℕ} (lo : Later L j) :
    result S L m j=DescentTerminalDataPlane.finalMem S.plane L.plane m j := by
  rw [result,leaf_early S L _ room lo.leaves lo.scalar,routed,route_early _ _ _ lo.progress lo.gates,
    named,DescentTerminalLocalPortBook.Gather.output,DescentTerminalChipRuntime.image_low _ _ _ _ lo.names,
    formatted,Header.early _ _ room.fmt lo.formats,indexed,Header.early _ _ room.idx lo.indices,
    external,DescentTerminalDenseHeaderRAM.before_inputs _ _ room.ext lo.external]

theorem after_gate (S : Shape) (L : Layout) (m : Memory w) (room : Room S L w) {j : ℕ}
    (one:j<L.leaf.cells.base) (two:j<L.scalar) : result S L m j=routed S L m j := leaf_early S L _ room one two

end
end Hierarchy.DescentTerminalEmitter

end OAI
