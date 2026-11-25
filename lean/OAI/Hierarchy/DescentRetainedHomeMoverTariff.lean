import OAI.Hierarchy.DescentRetainedHomeMover
import OAI.Hierarchy.DescentRetainedControlTariff
import OAI.Hierarchy.DescentRetainedTargetPlacementTariff

namespace OAI
/-! # Full retained primitive invoice with the measured home control included -/
namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentResetRetainedSetup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn (names names_seq)
noncomputable section
variable (z : DescentRetainedHomeMover.Layout)
local notation "v" => z.transfer
def queryBudget:=14+(v).channels*(25+11)

theorem query_work (base : ℕ) (which : Fin z.shapes→Option ℕ) (i : Fin ((v).nodes*z.shapes)) :
    (z.query base which i).work≤z.queryBudget:=by
  apply DescentOperandFamilyBook.expr_work
  exact fun j=>z.control.channel_work which (z.controlBase base) _ ((v).hostBank base j)

def invoice (base w : ℕ) :=
  (v).movementFee base w+z.control.invoice 7+DescentResetRetainedSetup.Layout.mountFee z.toLayout.bookWords+
    DescentRetainedTargetPlacement.Chart.invoice z.placement z.batch z.queryBudget

theorem price (base w : ℕ) (prev : Fin (v).blocks→Bank) (saved count inv : Bank)
    (which : Fin z.shapes→Option ℕ) (packet : Expr) (work : packet.work≤7)
    (prior : 0<(v).previousLanes) (mixed : 0<(v).gatherLanes) (matrix : 0<(v).matrixLanes) (dec : 0<(v).decodedLanes)
    (root : 0<z.rootLanes) (blocks : 0<z.blocks) (lanes : 0<z.lanes) :
    z.ticks base prev saved count inv which packet w+7*names (z.program base prev saved count inv which packet w)≤z.invoice base w:=by
  have moved:=(v).moved_price base w (z.prior prev) saved prior mixed matrix dec
  have route:=z.control.tariff (z.controlBase base) w which packet 7 work root dec
  have placed:=DescentRetainedTargetPlacement.Chart.tariff z.placement z.batch (z.placementBase base) w (z.kept which) (z.query base which)
    count inv z.queryBudget (z.query_work base which) dec blocks lanes
  simp only [ticks,program,names_seq,DescentOperandFamilyBook.program,Book.names,
    DescentOperandFamilyBook.ticks,DescentOperandFamilyBook.words,DescentOperandFamilyBook.unit,
    invoice,DescentRetainedPrimitive.Layout.bookWords,DescentResetRetainedSetup.Layout.mountFee]
  omega

end
end Hierarchy.DescentRetainedHomeMover.Layout

end OAI
