import OAI.Hierarchy.DescentRetainedSeven
import OAI.Hierarchy.DescentRetainedMoveTariff
import OAI.Hierarchy.DescentRetainedTargetPlacementTariff
import OAI.Hierarchy.DescentRetainedControlTariff

namespace OAI
/-! # Time and code of the physically sorted seven-field table issuer -/
namespace Hierarchy.DescentRetainedSeven.Chart
open DescentSIMDLookup DescentPackedZip DescentResetRetainedSetup DescentOrdinaryAtomFieldRAM
open DescentPacking.PackedMatch.Local ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentStaticWordColumn (names names_seq names_mount)
noncomputable section
variable (c : DescentRetainedSeven.Chart)
local notation "L" => c.retained
def queryBudget:=64+(L).channels*(25+11)

theorem query_work (floor : ℕ) (which : c.control.Targets) (o : Fin (L).outputs) (t : Fin c.placement.shapes) :
    (c.query floor which o t).work≤c.queryBudget:=by
  let ts:=DescentResetNodeBooks.tabs (c.tabs floor) (L).stripWord (L).channels (L).decodedLanes
  let xs:=fun j=>c.control.targetStream which (c.seen floor) t (.lookup ((L).hostBank floor j) .row)
  have collectBound (is : List (Fin (L).channels)) : (Gather.collect ts xs is).work≤1+is.length*(25+11):=by
    induction is with
    | nil=>rfl
    | cons i is ih=>
      have h:=(c.control.channel_work which (c.seen floor) t ((L).hostBank floor i))
      change (xs i).work≤25 at h
      simp only [Gather.collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul];omega
  have acc:=(collectBound (List.finRange (L).channels))
  change (c.joined floor which t).work≤1+(List.finRange (L).channels).length*(25+11) at acc
  rw [List.length_finRange] at acc
  unfold query
  split
  · change (c.joined floor which t).work+_≤64+(L).channels*(25+11)
    omega
  · simp only [DescentRetainedControl.Layout.originalID,DescentPackedZip.work,queryBudget]
    change ((c.joined floor which t).work+_)+7+11≤64+(L).channels*(25+11)
    omega

def invoice (floor w packetWork : ℕ):=
  (L).movementFee floor w+c.control.invoice packetWork+
    Layout.mountFee (((L).channels+1)*2^(((L).siteWord+(L).stripWord)*(L).decodedLanes))+
    Layout.mountFee ((L).outputs*2^((L).siteWord*(L).decodedLanes))+
    DescentRetainedTargetPlacement.Chart.invoice c.placement c.batch c.queryBudget

theorem price (floor w : ℕ) (which : c.control.Targets) (keep : Fin c.placement.shapes→Bool)
    (old : Fin (L).sources→Bank) (saved : Bank) (packet : Expr) (cnt inv : Bank) (T : ℕ) (cpu : packet.work≤T)
    (prior : 0<(L).previousLanes) (gather : 0<(L).gatherLanes) (matrix : 0<(L).matrixLanes) (dec : 0<(L).decodedLanes)
    (pkt : 0<c.packetLanes) (blk : 0<c.placement.blocks) (lanes : 0<c.placement.lanes) :
    c.ticks floor w which old saved packet cnt inv+7*names (c.program floor w which keep old saved packet cnt inv)≤
      c.invoice floor w T:=by
  have m:=(L).moved_price floor w old saved prior gather matrix dec
  have k:=c.control.tariff (c.seen floor) w which packet T cpu pkt dec
  have p:=DescentRetainedTargetPlacement.Chart.tariff c.placement c.batch (c.place floor) w keep
    (c.terms floor which) cnt inv c.queryBudget
    (fun j=>c.query_work floor which (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) dec blk lanes
  simp only [ticks,program,names_seq,joinCode,dictCode,ROM.mount,names_mount,invoice,Layout.mountFee,Nat.mul_assoc]
  omega

end
end Hierarchy.DescentRetainedSeven.Chart

end OAI
