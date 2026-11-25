import OAI.Computability.BorderVNP.DiagonalReturnedClaimClock
import OAI.Computability.BorderVNP.RoutingISAScheduleClockFinish
import OAI.Computability.BorderVNP.DiagonalTallySelectedOperands

/-! # The selected public finish window on each returning private-call suffix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader.PositiveFields

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open DiagonalTallyRAM DiagonalTallyMaterialize DiagonalTallyCellReports DiagonalTallyAllocation
open BorderVNP.Cube

/-- The measured cube-ID writer, actual report descriptor list, and physically
owned vertices bound every returning finish at the already allocated phase
window, including a finish which will feed a zero residue entry. -/
theorem FinishInput.returned_phase {teams dim width w : ℕ} {t : Fin teams} {rows : Fin teams → Fin dim → ℕ}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {state : Bank w} {mem : Memory w}
    {xs : List (List Bool)} (receipt : FinishInput t rows width pub mac state mem xs)
    {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    {n b h K s packetWidth vertices units pubWords powers : ℕ}
    (cubeRecords : Fin vertices → Operand)
    (actual : receipt.operands=cellOperands cs q++List.ofFn cubeRecords)
    (widthOne : ∀ v, (cubeRecords v).digits.length=1)
    (writer : traceCost receipt.earlier ≤ selectedOperandsTicks vertices packetWidth)
    (countFields : cs.length*(l.gadgets+l.gadgets*l.countWidth) ≤ pubWords)
    (use : teamWeighted cs ≤ powers) (wordFit : width ≤ w)
    (nonempty : 1 ≤ units) (visited : vertices ≤ TeamRowClock.physicalCoefficient n b h K s * units)
    (z : Returns (finishExpansion signedOccurrences) pub mac state mem) :
    traceCost z.val.1 ≤ cubeCoefficient n b h K s packetWidth*units +
      64*(pubWords+powers+TeamRowClock.physicalCoefficient n b h K s*units)+
      512*(teams+1)*(dim+1)*(w+1) := by
  let a := receipt.post.arenaFor receipt.operands.length receipt.raw dim teams t.val width
  have clock := (receipt.returned z).1
  have cost := alignedWork_le a cs q vertices cubeRecords widthOne pubWords powers w countFields use
    (by change receipt.operands.length=_; rw [actual]) wordFit
  change alignTallies.slots+allocateTallies.slots+a.work w (cellOperands cs q++List.ofFn cubeRecords) ≤
    64*(pubWords+powers+vertices)+512*(teams+1)*(dim+1)*(w+1) at cost
  rw [←actual] at cost
  change traceCost receipt.earlier ≤ packetIDTicks vertices packetWidth at writer
  exact clock.trans ((Nat.add_le_add writer cost).trans (finish_window nonempty visited))

end TeamContraction.JointHeader.PositiveFields

end BorderVNP
end Computability
end OAI
