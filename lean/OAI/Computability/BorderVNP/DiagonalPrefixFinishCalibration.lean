import OAI.Computability.BorderVNP.DiagonalSignedBundleBankRoom
import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.DiagonalTallyGadgetReadback
import OAI.Computability.BorderVNP.FragmentRowsSparsePatch

/-! # The physical directories and word sizes used after the signed calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open GeometryAdvice Packing.RoutingOutputs CellPacketGeometry TerminalCells
open TeamContraction.ProcessorSlots RoutingISA RoutingISA.SignedTaskArena

/-- In the public geometry output the primary descriptor sort follows the
37 scalar controls. Both fit before the routed packet bank, including the
entire padded primary payload. -/
theorem signed_finish_directories (t : Layout) (A : StartupArena)
    (candidates reserve gates originals live p d depth field w chunks : ℕ) :
    let fresh := A.next+7*candidates
    let ordinary := signedGridOutputCount t.cube.cables t.cube.cells originals live 37 (Total p d)
    let outputs := ordinary+(2^depth+2^depth)
    let dest := Allocation.dest fresh reserve gates outputs field
    let ctl := controlsBase dest t.cube.cables t.cube.cells originals live
    let start := packetBase dest t.cube.cables t.cube.cells originals live 37
    let dirs := GeometryDirectories.published start p d (t.cube.cells+1) chunks ctl (Total p d) depth
    t.cube.header.header = Allocation.stop fresh reserve gates outputs field w →
      t.p.sorted = dirs.sorted → t.p.padded = dirs.padded → t.cube.cells ≤ t.p.report.cells →
      t.SparsePlacement A.frame ctl ∧ t.p.sorted+t.p.padded ≤ t.cube.header.packetBase ∧
        ctl+37 ≤ t.cube.header.packetBase := by
  intro fresh ordinary outputs dest ctl start dirs base sorted padded cells
  have frame : A.frame+112 ≤ fresh := by
    dsimp only [fresh,StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]
    omega
  have left : fresh ≤ dest := by dsimp only [dest,Allocation.dest,Allocation.temp]; omega
  have lower : dest ≤ ctl := by dsimp only [ctl,controlsBase,bases]; omega
  have low : A.frame+112 ≤ ctl := frame.trans (left.trans lower)
  have row : start=ctl+37 := rfl
  have spread : t.p.sorted=start+(2^p+2^p) ∧ t.p.padded=2^d := ⟨sorted,padded⟩
  have region : start+((2^p+2^p)+(2^d+2^d))=dest+ordinary := by
    dsimp only [ordinary,start,signedGridOutputCount,packetBase,controlsBase,bases,count,Total]
    omega
  have high : dest+ordinary ≤ t.cube.header.header := by
    calc
      dest+ordinary ≤ dest+outputs := Nat.add_le_add_left (Nat.le_add_right ..) _
      _ ≤ t.cube.header.header := by
        rw [base]
        change dest+outputs ≤ dest+outputs+_+_
        omega
  have head : t.cube.header.header ≤ t.cube.header.packetBase := by
    unfold CubeHeaderInstall.Inputs.packetBase; omega
  have bank := t.open_table_order.1
  have split : ctl+37 ≤ t.p.sorted := by rw [spread.1,row]; exact Nat.le_add_right ..
  have full : t.p.sorted+t.p.padded ≤ t.cube.header.header := by
    apply le_trans _ (region.le.trans high)
    rw [spread.1,spread.2]; omega
  have below : ctl+37 ≤ t.cube.header.header := split.trans ((Nat.le_add_right ..).trans full)
  exact ⟨⟨low,(low.trans (Nat.le_add_right ..)).trans split,Or.inl split,below.trans bank,full.trans bank,cells⟩,
    full.trans head,below.trans head⟩

end PackedHistoryCircuit.Retained

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube BorderVNP.Cube.Padding.Banks DiagonalTallyAllocation
open FiniteEvaluator VPVNP.BurstRAM

/-- The physical parameters allocate a full machine word for every count and
exactly the scalar argument width for every cube table. The vertex count seen
by the lookup is bounded by the complete enumeration reserved in this arena. -/
theorem physical_finish_widths (arena : CubeArena.Layout) (dirs : GeometryDirectories)
    (n bundles marked params exponentWidth gadgets w fieldWidth bodyCap frame ctl : ℕ)
    (id : TableEntry arena.n arena.b arena.h arena.K arena.s → ℕ)
    (pub : Arg → Word w) (owner : Fin arena.header.d → ℕ) (team demand : ℕ)
    (data : Data arena.n arena.header.d arena.header.blocks arena.b arena.h arena.K arena.s) :
    let task : Layout := ⟨arena,id,physicalParameters arena dirs n bundles marked params exponentWidth gadgets w fieldWidth bodyCap⟩
    (reportLayout task.before task.after frame ctl params fieldWidth bodyCap arena.stop).countWidth = w ∧
      Tally.argumentWidth arena.n arena.b arena.h arena.K arena.s = task.p.report.cubeWidth ∧
      (gadgetLookup task pub owner team demand data).frame.count ≤ task.p.report.vertices :=
  ⟨rfl,rfl,CubeAllocation.team_count arena data.axis owner team⟩

/-- The high-water word bounds the team number and the report dimension,
including a team with an empty actual vertex enumeration. -/
theorem Layout.finish_word_room (t : Layout) {w u v k : ℕ} (fit : t.endAddress w u v k < 2^w) :
    0 < w ∧ t.dim < 2^w ∧ t.cube.teams < 2^w ∧ t.before.limit < 2^w := by
  have teams : t.cube.teams ≤ t.cube.hostDirectory+2*t.cube.cells := by
    unfold CubeArena.Layout.hostDirectory CubeArena.Layout.pairDirectory CubeArena.Layout.ownerBase; omega
  have before := (teams.trans t.open_table_order.2.1).trans t.open_table_order.2.2
  have extent : t.before.start ≤ t.before.limit := by rw [t.before.footprint]; omega
  have between : t.before.limit ≤ t.after.start := by
    change t.before.limit ≤ t.before.limit+3*t.cube.cells+7*t.cube.cells+
      t.p.scratchStride*t.cube.cells+t.p.burstStride*t.cube.cells
    omega
  have post : t.after.start ≤ t.after.fresh := by rw [t.after.footprint]; omega
  have localBase : t.after.fresh ≤ t.after.localBase := Nat.le_add_right ..
  have one : 1 < 2^w := by
    unfold endAddress entry DiagonalResidueRAM.gateBase at fit
    omega
  have pos : 0 < w := by cases w with | zero => simp at one | succ n => omega
  unfold endAddress entry valuation tallyBits DiagonalResidueRAM.gateBase at fit
  exact ⟨pos,by omega,by omega,by omega⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
