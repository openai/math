import OAI.Computability.BorderVNP.DiagonalSignedNativePacketSeeds
import OAI.Computability.BorderVNP.FiniteEvaluatorDescriptorOrder

/-! # Cross-cell descriptor order on the actual fragment return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM FragmentRows SignedTaskArena DiagonalTallyAllocation DiagonalTallyCellReports CellPacketGeometry

variable {w description frame ctl offsets db : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

/-- The report traversal and the stable fragment passes preserve both endpoints
of the descriptor interval of every real cell. Their disjoint order, including
empty neighboring cells, follows from the actual frozen inverse permutation. -/
theorem signed_fragment_descriptor_order (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description) (reported : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings reported.val.2.2)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f reported.val.2.2 fit cells) (place : a.SparsePlacement frame ctl)
    (geo : SparseGeometry a f offsets ctl) (base : ℕ → ℕ)
    (kept : ∀ z, ctl+37≤z → z<a.cube.header.header → readings m z=base z)
    (physical : banks.bankStart=a.cube.cellBank) (fp : rl.frame=frame) (l : CellControlRows.Layout)
    (count : l.cells=a.cube.cells) (padded : l.padded=2^db) (lo : ctl+37≤l.sorted)
    (hi : l.sorted+2*l.padded≤a.cube.header.header) (markers : l.stops+(a.cube.cells+1)≤2^db)
    (ordered : DescriptorRanks (a.cube.cells+1) l.stops db l.sorted base) :
    ∀ c c' : Fin l.cells, c<c' →
      readings e.output (l.sorted+l.padded+(l.stops+c.val)) < readings e.output (l.sorted+l.padded+c'.val) := by
  have agree (i : Fin (2^db)) : readings e.output (l.sorted+(2^db+i.val))=base (l.sorted+(2^db+i.val)) := by
    apply signed_geometry_on_fragment alloc seed reported e place geo base kept physical fp
    · omega
    · have := i.isLt
      omega
  have recovered := ordered.readback markers agree
  intro c c' less
  let b : Fin (a.cube.cells+1) := ⟨c.val,by have := c.isLt; omega⟩
  let b' : Fin (a.cube.cells+1) := ⟨c'.val,by have := c'.isLt; omega⟩
  have separate := recovered.separate b b' (show b<b' from less)
  simpa only [padded,Nat.add_assoc,b,b'] using separate

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
