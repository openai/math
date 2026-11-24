import OAI.Computability.VPVNP.PairTerminalVertexFramePacked
import OAI.Computability.VPVNP.PairVertexRootFields
import OAI.Computability.VPVNP.PairTerminalPrefixBudget

/-!
# Root-gather operands at every physical site

The terminal worker reloads the current vertex ordinal and six header words,
including the live width, inverse, and prefix pointers. Its root layout
agrees with the layout read from the physical shared-bit post-memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM PrivateRAM PairSimulation Compression CompressorRecords DescriptorSpace
open TraversalRows TraversalRoles LocalHistory
open scoped Fin.CommRing

variable {G : Group} {D : DescriptorSpace.Layout} {cap width ord : ℕ} {roles : List TaggedLayer}
variable {reference m : Memory G.w}
local notation "pub" => terminalOperands G
local notation "H" => vertexHeader G
local notation "size" => tagWords cap roles
local notation "first" => endAddress D
local notation "lay" => TerminalRootGather.Layout.ofHeader

theorem VertexPacked.gatherLayout (P : VertexPacked G D cap roles width)
    (frame : LinkedVertexMemory G reference ord m) (degree : ℕ) (state : Word G.w) :
    lay degree pub H state m = lay degree pub H state reference := by
  simp only [TerminalRootGather.Layout.ofHeader, NativeFrame.fromHeader, NativeFrame.regions]
  have h (j : ℕ) (hj : 0 < j) (hj' : j < 31) := P.header frame j hj hj'
  have h7 : m (H+7).val = reference (H+7).val := h 7 (by decide) (by decide)
  have h8 : m (H+8).val = reference (H+8).val := h 8 (by decide) (by decide)
  have h9 : m (H+9).val = reference (H+9).val := h 9 (by decide) (by decide)
  have h10 : m (H+10).val = reference (H+10).val := h 10 (by decide) (by decide)
  have h11 : m (H+11).val = reference (H+11).val := h 11 (by decide) (by decide)
  have h13 : m (H+13).val = reference (H+13).val := h 13 (by decide) (by decide)
  have h6 : m (H+6).val = reference (H+6).val := h 6 (by decide) (by decide)
  have h15 : m (H+15).val = reference (H+15).val := h 15 (by decide) (by decide)
  rw [h7,h8,h9,h10,h11,h13,h6,h15]

theorem VertexPacked.headerNumbering (P : VertexPacked G D cap roles width)
    (frame : LinkedVertexMemory G reference ord m) {a k : ℕ} (X : State a k) (v : X.network.Site)
    (degree : ℕ) (state : Word G.w) (index : state.val = ((siteOrder X).entries.symm v).val)
    (sites : (reference (H+7).val).val = (siteOrder X).length)
    (slots : (reference (H+8).val).val = TerminalPrefix.arcCount X) :
    TerminalGatherGeometry.Numbering X (lay degree pub H state m) v := by
  rw [P.gatherLayout frame degree state]
  exact ⟨index,sites,slots⟩

/-- Inputs consumed by the concrete gather's DFS handoff. Its private end
fit is supplied by the site's argument arena. All external fits and the
typed shared-bit and row equalities are recovered from the packed layout. -/
theorem VertexPacked.gather (P : VertexPacked G D cap roles width) (frame : LinkedVertexMemory G reference ord m)
    {a k : ℕ} (X : State a k) (v : X.network.Site) (degree : ℕ) (state : Word G.w)
    (last : Fin D.levels) (tab : Fin D.shape.tables) (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (width_eq : width = X.totalWidth)
    (capacity : TerminalPrefix.arcCount X ≤ slotCapacity D) (cells : TerminalPrefix.arcCount X ≤ tableWords D)
    (index : state.val = ((siteOrder X).entries.symm v).val)
    (sites : (reference (H+7).val).val = (siteOrder X).length)
    (slots : (reference (H+8).val).val = TerminalPrefix.arcCount X)
    (incoming : (reference (H+10).val).val = incidenceBase D last (TerminalPrefix.arcCount X) 4)
    (widths : (reference (H+9).val).val = incidenceBase D last (TerminalPrefix.arcCount X) 5)
    (starts : (reference (H+11).val).val = DescriptorSpace.tableBase D last tab)
    (wires : (reference (H+13).val).val = first+size)
    (rows : TerminalGatherGeometry.Rows X (lay degree pub H state reference) reference)
    (bits : ∀ i, reference (first+size+i.val) = PrivateFields.bitValue G.w (f i))
    (privateFit : (lay degree pub H state reference).dest + (∑ dir : Bool, ∑ j, X.halfWidth v dir j) < 2^G.w) :
    let L := lay degree pub H state m
    TerminalGatherGeometry.Numbering X L v ∧ TerminalGatherGeometry.Rows X L m ∧
      (∀ i, m (L.wires+i.val) = PrivateFields.bitValue G.w (f i)) ∧ L.Fits m ∧
      L.packet m = (NodeArguments.packed X v (TerminalGatherGeometry.half X f v)).map (PrivateFields.bitValue G.w) := by
  intro L
  dsimp only [L]
  rw [P.gatherLayout frame degree state]
  let L₀ := lay degree pub H state reference
  have num : TerminalGatherGeometry.Numbering X L₀ v := ⟨index,sites,slots⟩
  have dir := P.gatherRows X frame L₀ last tab capacity cells incoming widths starts rows
  have hi := P.arena
  have lo := P.counter_rows
  have room := P.room
  have hw : L₀.wires = first+size := wires
  have wb : ∀ i, m (L₀.wires+i.val) = PrivateFields.bitValue G.w (f i) := by
    intro i
    have ix := i.isLt.trans_eq (TerminalPrefix.width_sum X)
    rw [hw]
    exact (frame.below room (by omega) (by omega)).trans (bits i)
  have heads (head : ℕ) (hh : head ∈ [L₀.incomingHead,L₀.widthHead,L₀.prefixHead]) :
      head+TerminalPrefix.arcCount X ≤ 2^G.w := by
    change head ∈ [(reference (H+10).val).val,(reference (H+9).val).val,(reference (H+11).val).val] at hh
    rw [incoming,widths,starts] at hh
    have upper := (P.heads last tab _ capacity cells head hh).2
    omega
  have count := (P.heads last tab _ capacity cells (DescriptorSpace.tableBase D last tab) (by simp)).2
  exact ⟨num,dir,wb,TerminalGatherGeometry.fits num dir f wb (by omega) heads
    (by rw [hw]; omega) privateFit,TerminalGatherGeometry.packet_eq num dir f wb⟩

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
