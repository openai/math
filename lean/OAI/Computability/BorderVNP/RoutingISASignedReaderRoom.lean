import OAI.Computability.BorderVNP.RoutingISASignedReaderImage

/-! # Uniform startup and continuation addresses for the actual lead reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open TeamContraction.ProcessorSlots

/-- All four startup sources lie below the true serialized totals bank
whenever the true geometric workspace follows startup. -/
theorem Layout.reader_room (l : Layout) (A : StartupArena) {w u v gates pins : ℕ}
    (geometry : A.next ≤ l.cube.header.header) (indices : pins ≤ A.count)
    (packet : (6+3*gates+u)*w ≤ A.copied) (endFit : l.endAddress w u v gates < 2^w) :
    A.frame+30<2^w ∧ A.ibase+pins ≤ l.tallyBits ∧ A.hbase+pins ≤ l.tallyBits ∧
      A.dense+(6+3*gates+u)*w ≤ l.tallyBits := by
  have H : A.next ≤ l.cube.packetEnd := by
    unfold CubeArena.Layout.packetEnd CubeHeaderInstall.bankStop CubeHeaderInstall.Inputs.packetBase
    omega
  have start : A.next ≤ l.before.start := by
    have sep := l.cube.separated
    have upto : A.next ≤ l.cube.stop := by
      have pb : l.cube.pairBase ≤ l.cube.cellBank := by unfold CubeArena.Layout.cellBank; omega
      omega
    apply (upto.trans _).trans l.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  have free : l.before.start ≤ l.after.fresh := by
    have before : l.before.start ≤ l.before.limit := by rw [l.before.footprint]; omega
    have between : l.before.limit ≤ l.after.start := by
      change l.before.limit ≤ l.before.limit+3*l.cube.cells+7*l.cube.cells+
        l.p.scratchStride*l.cube.cells+l.p.burstStride*l.cube.cells
      omega
    have after : l.after.start ≤ l.after.fresh := by rw [l.after.footprint]; omega
    exact before.trans (between.trans after)
  have next : A.next ≤ l.tallyBits := (start.trans free).trans (by
    unfold tallyBits DiagonalTallyAllocation.AfterTasks.localBase
    omega)
  have last : l.tallyBits < 2^w := by
    unfold endAddress entry valuation DiagonalResidueRAM.gateBase at endFit
    omega
  have dense : A.dense+A.copied ≤ A.next := by
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase StartupArena.broadcastBase
    omega
  have hI : A.ibase+pins ≤ A.next := by unfold StartupArena.next StartupArena.hbase; omega
  have hH : A.hbase+pins ≤ A.next := by unfold StartupArena.next; omega
  have f : A.frame+30 ≤ A.dense := by unfold StartupArena.dense; omega
  exact ⟨f.trans_lt ((Nat.le_add_right A.dense A.copied).trans dense |>.trans next |>.trans_lt last),
    hI.trans next,hH.trans next,((Nat.add_le_add_left packet A.dense).trans dense).trans next⟩

end RoutingISA.SignedTaskArena

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM CompactMachine CellMacro.Generator BorderVNP.Cube

variable {dim b h K s n w : ℕ} {id : TableEntry dim b h K s → ℕ} {gen : Fragment IO}

/-- A positive team's actual selected completion reaches the same bank as
the chronological natural-column computation on its prepared input. -/
theorem finish_matches (S : PositiveTeam id gen n w) (p : S.Prefix) (ok : S.tallyReturns p)
    {es t mt} (run : Runs S.pub (install gen n S.routines) (finishExpansion signedOccurrences)
      (cellBank S.pub (install gen n S.routines) p.2.val.2.1 p.2.val.2.2) p.2.val.2.2 es t mt) :
    (S.finish p ok).val.1=es ∧ (S.finish p ok).val.2.1=t ∧ (S.finish p ok).val.2.2=mt :=
  (S.finish p ok).property.unique_of_deterministic (by decide) run

end RoutingISA.Evaluator.PositiveTeam

end BorderVNP
end Computability
end OAI
