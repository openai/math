import OAI.Hierarchy.DescentResetSignedHaloPacked
import OAI.Hierarchy.DescentResetOppositeRectangle
import OAI.Hierarchy.DescentResetSignedHaloRight

namespace OAI
/-! # The real previous signed field selects self or its source neighbor -/
namespace Hierarchy.DescentResetSignedHaloMatrix.Right
open DescentSharedCableNames DescentSharedCableNames.Stage DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open DescentResetOppositePayload DescentIssuedFallbackPanel DescentGroupPeerOrder DescentSixParty DescentStageEdgeReceipt
open DescentPacking.PackedMatch.Local.Stage DescentResetOriginHaloRAM DescentHostDirectory DescentColonies ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

section Physical
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i b H G a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {pow : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W pow price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (groups : J↪Fin G) (hosts : V↪Fin H)
set_option quotPrecheck false
local notation "rank" => groupRank (groups.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "names" => cableNames k rank
local notation "addr" => DescentIssuedFallbackPanel.address A native S ready
local notation "peer" =>physicalPeer A names
local notation "adj"=>hostRotor hosts (hostRoster A (hosts.trans Fin.valEmbedding))
local notation "E" => DescentSharedCableNames.Stage.Grain A
local notation "signedRect" => rectangular (b:=b) A native S ready groups hosts

theorem signed_halo (enough : DescentSignedCableCodec.width A.degree A.cap≤b) (width : A.degree+1<2^a) (s : Bool) (e : E) :
    let pr:=port A s e
    let data:=signedRect pr.1.2 (addr pr).2 (hosts pr.1.1.2) (groups pr.1.1.1)
    let z:=askedField A.degree A.cap b a data 0
    ∃j : Fin (A.degree+1),z.val=j.val+1 ∧ (closed adj (hosts pr.1.1.2) j).getD (hosts pr.1.1.2)=
      hosts (port A true e).1.1.2:=by
  intro pr field z
  let r:=live A native S ready names pr.1 pr.2
  have real : chip A.degree A.cap field=some r:=by
    rw [show field=widened A.degree A.cap b (Prepare.signed A native S ready groups hosts pr.1.2 (addr pr).2 (hosts pr.1.1.2) (groups pr.1.1.1)) from rfl,
      decoded enough,DescentResetOppositePayload.signed_at A native S ready groups hosts pr.1 (addr pr).2]
    exact signed_read A native S ready names pr.1 pr.2
  have flag : r.target=s:=by cases s <;>rfl
  refine ⟨slot r,?_,?_⟩
  · change ((askedField _ _ _ _ field 0).val)=_
    change (( (chip A.degree A.cap field).elim 0 (fun t=>(slot t).val+1) : ℕ) : Cell a).val=_
    rw [real]
    exact Fin.val_cast_of_lt ((show (slot r).val+1≤A.degree+1 from (slot r).isLt).trans_lt width)
  · cases s with
    | true=>simp [slot,flag,closed,pr]
    | false=>
      have peerRead:=signedPeer_actual A native S ready names false e
      change signedPeer A native S ready names false pr.1 (addr pr).2=_ at peerRead
      have next:peer pr.1 r.neighbor=some ((port A true e).1):=by
        have seen : signedPanel A native S ready names pr.1 (addr pr).2 = some r :=
          signed_read A native S ready names pr.1 pr.2
        rw [signedPeer, seen] at peerRead
        change (if r.target=false then peer pr.1 r.neighbor else none) = _ at peerRead
        rw [ite_eq_left flag] at peerRead
        exact peerRead.trans (congrArg some (port_fst A true e).symm)
      have neighbors:=(DescentResetOppositePayload.peering A groups hosts pr.1 r.neighbor).symm.trans next
      have atHost : ((hostRoster A (hosts.trans Fin.valEmbedding)) pr.1.1.2 r.neighbor).map hosts=some (hosts (port A true e).1.1.2):=by
        have found:=congrArg (Option.map (fun p=>hosts p.1.2)) neighbors
        simpa [Option.map_map] using found
      simp only [slot,flag,Bool.false_eq_true,ite_false,closed,Fin.lastCases_castSucc,DescentResetOppositePayload.host_at A hosts,atHost,Option.getD_some]
end Physical
end
end Hierarchy.DescentResetSignedHaloMatrix.Right

end OAI
