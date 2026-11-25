import OAI.Computability.BorderVNP.DiagonalTallyGadgetReadback
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource
import OAI.Computability.BorderVNP.DiagonalTallySelectedOperands

/-! # The actual signed lookup deck produces the complete native tally operand list -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks DiagonalTallyPacketEmit
open VPVNP.BurstRAM FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports DiagonalTallyRAM

variable {w : ℕ} (a : Layout) (pub : Arg → Word w) (owner : Fin a.cube.header.d → ℕ) (team demand : ℕ)
variable (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)

local notation "lookup" => gadgetLookup a pub owner team demand A

/-- Compose the actual post-private-call raw gadget deck with the verified cell
operand scan. Only the additional cell count, descriptor base and parameter width
are read from the suffix controls. All packet triples, bits and IDs are already
certified by the owned-group receipt. -/
theorem gadgetOperands {banks : CellBanks.Layout} {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    (alloc : ReportAllocation a.before a.after banks l cs q)
    (bankStart : banks.bankStart=a.cube.cellBank) (bankCount : banks.cells=a.cube.cells)
    (bankStride : banks.stride=a.cube.cellStride) (zeroAddr : l.zeroAddr=a.cube.stop)
    (frame : (pub 0).val=l.frame) (mac : TeamOpcode.Macros w 8) (s : Bank w) (mem : Memory w)
    (prepared : CubePacket.WordPrepared lookup a.id pub mem)
    (report : DiagonalTallyMaterialize.supplied mem (cellEnd cs q) q.descriptors (cellOperands cs q))
    (count : (mem (l.frame+35)).val=(cellOperands cs q).length)
    (table : (mem (l.frame+44)).val=a.after.descriptors) (params : (mem (l.frame+95)).val=l.parameters)
    (vertices : (lookup).frame.count ≤ a.p.report.vertices)
    (digits : argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s ≤ a.p.report.cubeWidth)
    (frameRoom : l.frame+101<a.after.start) (room : a.after.fresh<2^w)
    (idCap : ∀ i, a.id (((lookup).visits i).entry demand)<l.gadgets)
    (dim : l.parameters+l.gadgets ≤ 2^w) :
    let X := lookup
    let cells := cellOperands cs q
    let suffix := a.after.suffixFrame cells.length X.frame.count l.zeroAddr l.parameters
    let os := cells++suffix.packetOperands l.frame (a.cube.stop+1) (fun i => a.id ((X.visits i).entry demand))
    ∃ es t mt, Runs pub mac (.seq producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands) s mem es t mt ∧
      traceCost es ≤ selectedOperandsTicks X.frame.count X.frame.width ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      DiagonalTallyMaterialize.supplied mt a.after.fresh a.after.descriptors os ∧
      (mt (l.frame+35)).val=os.length ∧ os.length ≤ a.after.bound.operands ∧
      (∀ k,operandReads a.after.descriptors os k → outsidePointers l.frame k ∧ k≠l.frame+34) ∧
      ∀ k,k<a.after.start → k≠l.frame+35 → mt k=mem k := by
  intro X cells suffix os
  have lits := a.literal_bounds
  have lower : banks.bankStart+banks.cells*banks.stride ≤ l.zeroAddr := by
    rw [bankStart,bankCount,bankStride,zeroAddr,lits.1]
  have oneLo : banks.bankStart ≤ a.cube.stop+1 := by rw [bankStart]; have := lits.1; omega
  have frameFields := prepared.frame
  change X.frame.resident (readings pub) (readings mem) at frameFields
  obtain ⟨ct,_,_,_,_,z,_,_,_⟩ := frameFields
  simp only [readings,frame] at ct z
  have addr : (mem (l.frame+47)).val=X.table := frame ▸ prepared.tableWord
  have dest : (mem (l.frame+71)).val=a.after.ids := frame ▸ prepared.dstWord
  have before (i : Fin X.frame.count) (r : Reference) (hr : r∈recipe (X.visits i).selector (X.visits i).vertex a.cube.b a.cube.s) :
      r.address (X.visits i).base l.zeroAddr (a.cube.stop+1)<a.after.start := by
    rw [zeroAddr]
    exact prepared.below i r hr
  have capacity (i : Fin X.frame.count) : l.parameters+a.id ((X.visits i).entry demand)<2^w :=
    (Nat.add_lt_add_left (idCap i) _).trans_le dim
  let frame' := {(a.after.packetFrame X.frame.count X.frame.triples X.frame.recipes l.zeroAddr (a.cube.stop+1)
    (Fintype.card (Vertex (a.cube.n+1)))) with width:=argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s}
  have correct : frame'=X.frame := by unfold frame'; rw [zeroAddr]; rfl
  have args := alloc.selectedOperands pub mac s mem X.visits a.id demand X.frame.triples X.frame.recipes (a.cube.stop+1)
    X.table frame vertices digits lower (by rw [zeroAddr]; omega) oneLo lits.2 report frameRoom room addr
    prepared.tableFit prepared.deck (zeroAddr ▸ prepared.zero) prepared.one prepared.banks before capacity
  exact args (by change frame'.resident _ _; rw [correct]; exact prepared.frame)
    (by change frame'.Fits _ _ _; rw [correct,←frame]; exact prepared.fits)
    (by change frame'.recipeAt _ _ _ _ _ _; rw [correct]; exact prepared.recipe)
    prepared.triples ⟨count,ct,table,dest,zeroAddr ▸ z,params⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
