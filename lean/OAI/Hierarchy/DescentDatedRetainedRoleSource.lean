import OAI.Hierarchy.DescentPhysicalResetRoleFrames
import OAI.Hierarchy.DescentRetainedHomeMoverRead

namespace OAI
/-! # The physical retained operand at the final primitive instruction -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentPackedZip DescentGL DescentColonies
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : FinalInputs u)
local notation "o" => a.successor
local notation "b" => a.rebased floor
local notation "ds" => (o).actor.directory ((o).middle.stop b)
local notation "P₀" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "key" => (⟨(P₀).saved,0⟩ : Bank)
local notation "start" => (o).fullEnd b
local notation "stop" => (o).roleEnd b
local notation "move" => (o).roleTransfer
local notation "v" => (move).transfer
local notation "P" => (move).placement
local notation "batch" => (move).batch
local notation "chart" => (o).primitive.chart

theorem retained_source {U : ℕ} (mid : Memory w) (fit : z.Room)
    (size : 2^((v).high+(v).low)=(v).groups*(v).blocks) (blockPitch : 2^(v).low=(v).gatherLanes*(v).blocks)
    (gather : 0<(v).gatherLanes) (blocks : 0<(v).blocks) (oldPitch : 0<(v).previousLanes)
    (cut : (v).cut≤(v).high+(v).low) (pitch : (v).matrixLanes*(v).donors=2^(v).low)
    (live : 0<(v).matrixLanes) (dec : 0<(v).decodedLanes) (ready : 0<(move).rootLanes)
    (L : DescentGL.Layout ((v).high+(v).low)) (elected : z.venueImage mid (key).base=((DescentExterior.matrixCode L).val:Word w))
    (X : Fin (v).blocks→Fin (v).hosts→Fin (v).groups→Cell (v).wholeWord)
    (Y : Fin (v).hosts→Fin (v).grouped→Cell (move).control.rootWidth)
    (capacity : ∀j,(v).hosts*chunks (v).groups (v).previousLanes≤(z.previousRoles j).size)
    (read : ∀j,Reads (z.previousRoles j) (X j) (v).previousLanes (z.venueImage mid))
    (packet : Source (oldMatrix u) Y (move).rootLanes (z.venueImage mid))
    (groups : (move).groups*(move).blocks=(v).grouped)
    (name : Fin U→Fin (P).sparse) (amount : z.venueImage mid (ds).count.base=(U:Word w))
    (inverse : ∀i:Fin U,z.venueImage mid ((ds).inverse.base+i.val)=((name i).val:Word w))
    (narrow : U<2^w) (hosts : (move).newHosts≤2^w) (saved : U≤(ds).inverse.size)
    (x : Fin (chart).blocks) (n : Fin (chart).nodes) :
    Source (z.roles.retained x n)
      (DescentRetainedTargetPlacement.Chart.compact (P) batch ((move).kept z.which) name
        (fun i h g=>(move).targetInputs z.which Y ((move).oldStrips size cut L X) i h (g.cast groups))
        (n.cast z.roleNodes) (x.cast z.roleBlocks)) (move).lanes (z.roleInput mid):=by
  have actual:=(move).issued start z.previousRoles key (ds).count (ds).inverse z.which (oldMatrix u) (z.venueImage mid) fit.roleMove
    size blockPitch gather blocks oldPitch cut pitch live dec ready L elected X Y capacity read packet groups name amount inverse narrow hosts saved
    (n.cast z.roleNodes) (x.cast z.roleBlocks)
  have bank:=DescentRetainedTargetPlacement.Chart.validBank (P) (batch) ((move).placementBase start) fit.roleMove.roof
    (n.cast z.roleNodes) (x.cast z.roleBlocks)
  have frame:=(z.role_input_frames fit mid).2.1
  intro t
  exact (eval_below _ _ (z.retainedImage mid) (z.roleInput mid) (show (z.roles.retained x n).Fits w stop from ⟨bank.1,trivial⟩)
    (fun j hj=>frame j (.inl hj))).trans (actual t)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
