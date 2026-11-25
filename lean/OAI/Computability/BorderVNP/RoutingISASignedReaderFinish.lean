import OAI.Computability.BorderVNP.RoutingISASignedReaderRoom
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepActual

/-! # Addressed reader sources on the chosen positive team's native finish -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM CompactMachine CellMacro.Generator BorderVNP.Cube SignedTaskArena
open TeamContraction.ProcessorSlots DiagonalTallyRAM DiagonalTallyMaterialize DiagonalResidueRAM
open scoped BigOperators

variable {dim b h K s n w : ℕ} {id : TableEntry dim b h K s → ℕ} {gen : Fragment IO}

/-- From the supplied records and their local subtotal, the actual positive
team's chosen returning bank keeps the original reader operands and contains
the global sums of the same physical rows. The suffix has no guess tape. -/
theorem reader_finish (S : PositiveTeam id gen n w) (p : S.Prefix) (ok : S.tallyReturns p)
    (l : SignedTaskArena.Layout) (A : StartupArena) (entryCount pins raw d teams team width : ℕ)
    (os : List Operand) (rows : Fin teams → Fin d → ℕ)
    (bank : Bank w) (selected : Memory w) (events : List (TeamRAM.Event w))
    (pd : l.dim=d) (pt : l.cube.teams=teams) :
    let mac := install gen n S.routines
    let r := cellBank S.pub mac p.2.val.2.1 p.2.val.2.2
    let ar := l.after.arenaFor os.length raw d teams team width
    Runs S.pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      r p.2.val.2.2 events bank selected →
    (∀ k < l.after.start, k ≠ (S.pub 0).val+35 → selected k=p.2.val.2.2 k) →
    ∀ input : AlignedAllocationInput ar S.pub selected os (broadcast width rows) l.after.descriptors,
    (∀ c : Fin d, ar.localRow os c.val=rows ⟨team,input.fit.team⟩ c) →
    (∀ i c, rows i c<2^width) → (∀ c, ∑ i,rows i c<2^w) →
    (S.pub 0).val=A.frame → entryCount*w ≤ A.copied → pins ≤ A.count →
    A.next ≤ l.cube.header.header → os.length ≤ l.after.bound.operands →
    ReaderKept A entryCount pins S.memory (S.pins p.1).val.2.2 p.2.val.2.2 →
      ReaderKept A entryCount pins S.memory (S.pins p.1).val.2.2 (S.finish p ok).val.2.2 ∧
      ∀ c : Fin d,∀ j<w, (S.finish p ok).val.2.2 (l.tallyBits+(c.val*w+j)) =
        word w (((∑ i,rows i c).testBit j).toNat) := by
  intro mac r ar prep keep input localCounts rowFit sumFit frame packet ix geom cap before
  obtain ⟨es,t,mt,run,_,_,sum⟩ := signedFinish_runs ar S.pub mac r bank p.2.val.2.2 selected events
    os l.after.descriptors (traceCost events) rows prep le_rfl input localCounts rowFit sumFit
  have saved := ReaderKept.after_finish A entryCount pins l raw d teams team width S.pub mac
    r bank S.memory (S.pins p.1).val.2.2 p.2.val.2.2 selected events os (broadcast width rows)
    prep keep input run frame packet ix geom cap before
  rw [(S.finish_matches p ok run).2.2]
  refine ⟨saved,?_⟩
  have dst : (ar.bitFrame w).dst=l.tallyBits := by
    simpa only [pd,pt] using l.tallyBits_actual cap raw team width w
  intro c j hj
  rw [←dst]
  exact sum c j hj

end RoutingISA.Evaluator.PositiveTeam

end BorderVNP
end Computability
end OAI
