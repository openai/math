import OAI.Hierarchy.DescentDatedOperandNarrowSockets
import OAI.Hierarchy.DescentDatedOperandMatchedFields
import OAI.Hierarchy.DescentDatedOperandRawFields
import OAI.Hierarchy.DescentDatedSignedHeaderFits
import OAI.Hierarchy.DescentDatedSignedAny
import OAI.Hierarchy.DescentDatedBookedChip

namespace OAI
/-! # All physical addresses used by an ordinary operand candidate, for arbitrary input memory -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentPackedColony DescentSharedCableNames DescentDatedSourcePathDirectory DescentSharedLeafLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ)
local notation "e₀" => v.material
local notation "s₀" => v.signed
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "G" => (e₀).groups
local notation "B" => (e₀).blocks
local notation "M" => (e₀).lanes
local notation "b" => (e₀).fieldBits
local notation "first₀" => v.donorEnd floor
local notation "prior₀" => PriorHeader.endAddress H G M D first₀
local notation "start₀" => v.materialStart floor
local notation "limit₀" => (e₀).endAddress start₀
local notation "path₀" => v.operandPathStart floor
local notation "rank₀" => v.operandRankStart floor
local notation "old₀" => v.operandOldHeaderStart floor
local notation "end₀" => v.operandHeaderEnd floor
local notation "map₀" => (e₀).projectionStart start₀
local notation "mapEnd" => DepotRAM.Material.Route.Projection.roof b B M K G P₀ map₀
local notation "marks₀" => v.markEnd floor

theorem parent_candidate_room {w : ℕ} (c : v.SignedChart) (cash : v.SignedRoom floor w) (upper : v.signedEnd floor≤end₀)
    (x : Fin B) (i : Fin (P₀*DepotRAM.Material.roles fmt₀)) :
    (v.parentSerial floor c x i).Fits w end₀ ∧ (v.parentPeer floor c x i).Fits w end₀ :=by
  let core:=DescentOrdinarySignedParents.ROM.endAddress ((s₀).tailStart marks₀) (s₀).degree (s₀).lowSites
    (s₀).tickets (s₀).cap (s₀).fieldBits (s₀).lanes
  let tail:=DescentOrdinarySignedAll.Tail core (s₀).blocks (s₀).candidates (s₀).fieldBits (s₀).lanes (s₀).hosts (s₀).groups
  have ord:=DescentOrdinarySignedAll.ordered (X:=(s₀).blocks) («K» := (s₀).candidates) («b» := (s₀).fieldBits)
    («M» := (s₀).lanes) («H» := (s₀).hosts) (gg:=(s₀).groups) (cap:=(s₀).cap) core
  have tailLe : tail≤v.signedEnd floor:=ord.2.trans (le_of_eq ((s₀).calibrated marks₀))
  have space : v.signedEnd floor<2^w:=(Nat.le_add_right ..).trans_lt cash.room
  let z : (s₀).Socket:=(x.cast c.blocks.symm,v.parentSlot c i)
  have rank : (v.parentSerial floor c x i).Fits w tail:=
    ⟨DescentResetSignedScan.Ranks.output_fits core z.1 (1:Fin 3) z.2 (tailLe.trans_lt space),trivial⟩
  have gather:=(s₀).gathered_fits marks₀ cash.room z
  have peer : (v.parentPeer floor c x i).Fits w ((s₀).tailStart marks₀):=
    DescentPackedChildNeighbor.SIMD.fitted _ _ ((s₀).peer_chart_room_of_gathered marks₀ space z gather) _
  have before : (s₀).tailStart marks₀≤core:=by dsimp [core,DescentOrdinarySignedParents.ROM.endAddress];omega
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (tailLe.trans upper) rank,
    ProtocolRAMGeneratedWrite.fits_mono _ (before.trans (ord.1.trans (tailLe.trans upper))) peer⟩

theorem native_ticket_head_room {w : ℕ} (c : v.SignedChart) (cash : v.SignedRoom floor w)
    (reach : (e₀).reach=P₀) (bands : (e₀).oldGroups=G*B) (pitch : 0<M) (positive : 0<B) (grow : H≤K)
    (prior : prior₀≤end₀) (early : limit₀≤old₀) (signed : v.signedEnd floor≤end₀) (space : end₀<2^w) :
    (∀key,(v.wideHead floor c key).Fits w end₀) ∧ ∀key,(v.narrowHead floor key).Fits w end₀ :=by
  have toRank : path₀≤rank₀:=(Nat.le_add_right ..).trans (end_le path₀ H G M D)
  have toOld : rank₀≤old₀:=Nat.le_add_right ..
  have last : old₀≤end₀:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have pathHigh:=toRank.trans (toOld.trans last)
  have fitMap : mapEnd≤old₀:=by rw [←reach,v.stampedRoof];exact early
  have mapBound : (v.receiverMap floor).base+(v.receiverMap floor).size ≤ mapEnd:=Nat.le_add_right ..
  have mapRoom {out : ℕ} (h : mapEnd≤out) :
      (v.receiverMap floor).Fits w out:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((mapBound.trans fitMap).trans_lt (last.trans_lt space)),mapBound.trans h⟩
  have matBound:=early.trans last
  have matField (x f i) : (v.rawFieldHead floor x f i).Fits w end₀:=by
    let coord:=finProdFinEquiv.symm i
    let z:=(DepotRAM.Material.seatIndex fmt₀).symm coord.2
    let col:=DepotRAM.Material.Sheets.rawId fmt₀ f z
    let bk:=v.receivedBank start₀ col
    have paid:=v.received_fit start₀ end₀ w matBound space pitch positive bands grow col
    have off:=(PriorHeader.accessible_at («H» := H) («D» := D) («M» := M) («G» := G) first₀ (prior.trans_lt space)
      bk end₀ prior paid.1 paid.2).2
    have ok:=DepotRAM.Material.Route.Projection.socket_fit («K» := K) map₀ end₀ (fitMap.trans last) space
      (v.operandRanks floor) (v.operandRoster floor) bk 0 coord.1 x off
    exact ⟨ok.apply,ok.right,ok.shift,ok.left⟩
  have matched (x : Fin B) (p : Fin P₀) (j : Fin (DescentDatedOperandPages.count fmt₀)) :
      (v.operandDatum floor x p j).Fits w end₀:=by
    let bk:=DescentDatedOperandPages.resultBank fmt₀ v.operandDepotLayout (v.originMouthEnd floor) j
    have paid:=DescentDatedOperandPages.returned_room fmt₀ v.operandDepotLayout (v.originMouthEnd floor)
      (pathHigh.trans_lt space) j
    have chunksEq : chunks (e₀).oldGroups (M*B)=chunks G M:=by rw [bands,chunks_group _ _ _ pitch positive]
    have count : H*chunks G M≤bk.size := by
      calc H*chunks G M = H*chunks (e₀).oldGroups (M*B) := congrArg (H * ·) chunksEq.symm
           _ ≤ bk.size := paid.2
    have off:=(PriorHeader.accessible_at («H» := H) («D» := D) («M» := M) («G» := G) first₀ (prior.trans_lt space)
      bk end₀ prior ⟨paid.1.1,paid.1.2.1,paid.1.2.2.trans pathHigh⟩ count).2
    have ok:=DepotRAM.Material.Route.Projection.socket_fit («K» := K) map₀ end₀ (fitMap.trans last) space
      (v.operandRanks floor) (v.operandRoster floor) bk 0 p x off
    exact ⟨ok.apply,ok.right,ok.shift,ok.left⟩
  constructor
  · rintro (⟨x,f,i⟩|rest)
    · exact matched x (v.matchOldIndex i f).1 (v.matchOldIndex i f).2
    rcases rest with ⟨x,f,i⟩|⟨x,f,i⟩
    · exact matched x (v.matchAnchorIndex i f).1 (v.matchAnchorIndex i f).2
    · change (v.signedRawHead floor c x f i).Fits w end₀
      unfold signedRawHead
      split
      · apply matField
      split
      · exact (v.parent_candidate_room floor c cash signed x i).1
      · exact (v.parent_candidate_room floor c cash signed x i).2
  · rintro (i|p)
    · obtain ⟨⟨p,d⟩,rfl⟩:=finProdFinEquiv.surjective i
      let hdr:=chart path₀ H G M p d
      have geo:=geometry path₀ p d ((toOld.trans last).trans_lt space)
      have fit : Readable hdr 1 H G M (Packed.bits P₀) w end₀:=
        ⟨fun bank mem=>⟨(geo.fit bank mem).1,(geo.fit bank mem).2.1,(geo.fit bank mem).2.2.trans (toOld.trans last)⟩,
          geo.ranks,geo.starts,geo.cuts,geo.repeats⟩
      simpa only [narrowHead,previousPathHead,Equiv.symm_apply_apply] using
        narrow_mapped_fits fit (mapRoom (fitMap.trans last))
    · have geo:=Local.shared_geometry path₀ p (0:Fin (D+1)) (last.trans_lt space)
      exact ProtocolRAMGeneratedWrite.fits_mono _ last (narrow_mapped_fits geo (mapRoom fitMap))

/-- The actual registered signed interval already buys all candidate reads.
This bound uses only the public chart, allocation and final address. -/
theorem signed_ticket_head_room {w : ℕ} (c : v.SignedChart) (cash : v.SignedRoom floor w)
    (space : end₀<2^w) :
    (∀key,(v.wideHead floor c key).Fits w end₀) ∧ ∀key,(v.narrowHead floor key).Fits w end₀ :=by
  obtain ⟨s0,s1,s2,s3,s4,s5⟩:=v.into_booked_headers floor
  have path : v.signedEnd floor≤path₀:=s0.trans (s1.trans (s2.trans s3))
  have old : path₀≤old₀:=((Nat.le_add_right ..).trans (end_le path₀ H G M D)).trans (Nat.le_add_right ..)
  have prior : prior₀≤v.signedEnd floor:=by rw [←c.degree];exact s5
  have material : limit₀≤v.signedEnd floor:=cash.material.trans ((s₀).room marks₀)
  exact v.native_ticket_head_room floor c cash (congrArg breadth c.degree) cash.groups cash.lanes cash.blocks cash.growth
    (prior.trans (path.trans s4)) (material.trans (path.trans old)) (path.trans s4) space

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
